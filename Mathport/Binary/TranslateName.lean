/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam

Lean3 uses snake_case for everything.

As of now, Lean4 uses:
- camelCase for defs
- PascalCase for types
- snake_case for proofs
-/
import Lean
import Mathport.Util.Misc
import Mathport.Util.String
import Mathport.Binary.Basic


namespace Mathport.Binary

open Lean Lean.Meta

inductive ExprKind
  | eSort
  | eDef
  | eProof

partial def translatePrefix (pfix3 : Name) : BinportM Name := do
  match ← lookupNameExt pfix3 with
  | some pfix4 => pure pfix4
  | none =>
    match pfix3 with
    | Name.anonymous  ..  => pure Name.anonymous
    | Name.num pfix3 k .. => pure $ Name.mkNum (← translatePrefix pfix3) k
    | Name.str pfix3 s .. =>
      let s := if (← read).config.stringsToKeep.contains s then s else s.snake2pascal
      pure $ Name.mkStr (← translatePrefix pfix3) s

def translateSuffix (s : String) (eKind : ExprKind) : BinportM String :=
  return if (← read).config.stringsToKeep.contains s then s else
    match eKind with
    | ExprKind.eSort  =>
      -- TODO: consider re-enabling this, but be warned you will need to propagate elsewhere
      -- let s := if s.startsWith "has_" then s.drop 4 else s
      s.snake2pascal
    | ExprKind.eDef   => s.snake2camel
    | ExprKind.eProof => s

partial def mkCandidateLean4NameForKind (n3 : Name) (eKind : ExprKind) : BinportM Name := do
  if let some n4 ← lookupNameExt n3 then return n4
  if n3.isStr && n3.getString! == `_main then mkCandidateLean4NameForKind n3.getPrefix eKind else
    let pfix4 ← translatePrefix n3.getPrefix
    match n3 with
    | Name.num _ k ..  => pure $ Name.mkNum pfix4 k
    | Name.str _ s ..  => pure $ Name.mkStr pfix4 (← translateSuffix s eKind)
    | _                => pure Name.anonymous

def getExprKind (type : Expr) : MetaM ExprKind := do
  if ← try isProp type catch _ => pure false then return ExprKind.eProof
  if ← try returnsSort type catch _ => pure false then return ExprKind.eSort
  return ExprKind.eDef
where
  returnsSort (type : Expr) : MetaM Bool :=
    forallTelescope type fun _ b => pure $ b matches Expr.sort ..

def mkCandidateLean4Name (n3 : Name) (type : Expr) : BinportM Name := do
  mkCandidateLean4NameForKind n3 (← liftMetaM <| getExprKind type)

inductive ClashKind
  | found (msg : String) : ClashKind
  | freshDecl  : ClashKind
  deriving Inhabited, Repr, BEq

def mkMismatchMessage (defEq : Bool) (ty3 ty4 : Expr) : BinportM String := do
  if defEq then return ""
  let msg := m!"lean 3 declaration is{indentExpr ty3}\nbut is expected to have type{indentExpr ty4}"
  msg.toString

-- Given a declaration whose expressions have already been translated to Lean4
-- (i.e. the names *occurring* in the expressions have been translated
-- TODO: this is awkward, the `List Name` is just the list of constructor names for defEq inductive clashes
partial def refineLean4Names (decl : Declaration) : BinportM (Declaration × ClashKind × List Name) := do
  match decl with
  | Declaration.axiomDecl ax =>
    refineAx { ax with name := ← mkCandidateLean4Name ax.name ax.type }
  | Declaration.thmDecl thm =>
    refineThm { thm with name := ← mkCandidateLean4Name thm.name thm.type }
  | Declaration.defnDecl defn =>
    let name ← mkCandidateLean4Name defn.name defn.type
    -- Optimization: don't bother def-eq checking constructions that we know will be def-eq
    if name.isStr && (← read).config.defEqConstructions.contains name.getString! then
      let clashKind := if (← getEnv).contains name then .found "" else .freshDecl
      return (Declaration.defnDecl { defn with name := name }, clashKind, [])
    refineDef { defn with name := name }
  | Declaration.inductDecl lps nps [indType] iu =>
    let mut candidateName ← mkCandidateLean4Name indType.name indType.type
    let indType := indType.replacePlaceholder (newName := candidateName)
    let indType := indType.updateNames InductiveType.selfPlaceholder candidateName
    refineInd lps nps indType iu
  | _ => throwError "unexpected declaration type"

where
  refineAx (ax3 : AxiomVal) := do
    println! "[refineAx] {ax3.name} {ax3.type}"
    match (← getEnv).find? ax3.name with
    | some ax4 =>
      let defEqType ← isDefEqUpto ax3.levelParams ax3.type ax4.levelParams ax4.type
      if (← read).config.skipDefEq || defEqType && (ax4 matches .axiomInfo _) then
        pure (.axiomDecl ax3, .found (← mkMismatchMessage defEqType ax3.type ax4.type), [])
      else
        println! "[clash] {ax3.name}"
        refineAx { ax3 with name := extendName ax3.name }
    | none => pure (.axiomDecl ax3, .freshDecl, [])

  refineThm (thm3 : TheoremVal) := do
    println! "[refineThm] {thm3.name}"
    match (← getEnv).find? thm3.name with
    | some thm4 =>
      let defEqType ← isDefEqUpto thm3.levelParams thm3.type thm4.levelParams thm4.type
      if (← read).config.skipDefEq || defEqType && (thm4 matches .thmInfo _) then
        pure (.thmDecl thm3, .found (← mkMismatchMessage defEqType thm3.type thm4.type), [])
      else
        println! "[clash] {thm3.name}"
        refineThm { thm3 with name := extendName thm3.name }
    | none => pure (.thmDecl thm3, .freshDecl, [])

  refineDef (defn3 : DefinitionVal) := do
    println! "[refineDef] {defn3.name}"
    match (← getEnv).find? defn3.name with
    | some defn4 =>
      let ok ← if (← read).config.skipDefEq then
        let ok ← isDefEqUpto defn3.levelParams defn3.type defn4.levelParams defn4.type
        pure <| some ok
      else
        let ok ← match defn4 with
        | .defnInfo defn4 => isDefEqUpto defn3.levelParams defn3.value defn4.levelParams defn4.value
        | _ => pure false
        pure <| if ok then some true else none
      if let some defEqType := ok then
        pure (.defnDecl defn3, .found (← mkMismatchMessage defEqType defn3.type defn4.type), [])
      else
        println! "[clash] {defn3.name}"
        refineDef { defn3 with name := extendName defn3.name }
    | none => pure (.defnDecl defn3, .freshDecl, [])

  refineInd (lps : List Name) (numParams : Nat) (indType3 : InductiveType) (isUnsafe : Bool) := do
    println! "[refineInd] {indType3.name}"
    let recurse := do
      println! "[clash] {indType3.name}"
      refineInd lps numParams (indType3.updateNames indType3.name (extendName indType3.name)) isUnsafe
    match (← getEnv).find? indType3.name with
    | some (.inductInfo indVal) =>
      let ok ← (do
        if lps.length ≠ indVal.levelParams.length then return none
        if (← read).config.skipDefEq then
          return some (← isDefEqUpto lps indType3.type indVal.levelParams indVal.type)
        if indVal.numParams ≠ numParams then return none
        if !(← isDefEqUpto lps indType3.type indVal.levelParams indVal.type) then return none
        let ctors := indType3.ctors.zip indVal.ctors
        let ok ← ctors.allM fun (ctor3, name4) => do
          let some (ConstantInfo.ctorInfo ctor4) := (← getEnv).find? name4
            | throwError "constructor '{name4}' not found"
          isDefEqUpto lps ctor3.type ctor4.levelParams ctor4.type
        return if ok then some true else none)
      if let some defEqType := ok then
        let msg ← mkMismatchMessage defEqType indType3.type indVal.type
        pure (.inductDecl lps numParams [indType3] isUnsafe, .found msg, indVal.ctors)
      else recurse
    | none => pure (.inductDecl lps numParams [indType3] isUnsafe, .freshDecl, [])
    | _ => println! "[refineInd] not an IND"
           recurse

  isDefEqUpto (lvls₁ : List Name) (t₁ : Expr) (lvls₂ : List Name) (t₂ : Expr) : BinportM Bool := do
    if lvls₁.length ≠ lvls₂.length then return false
    let t₂ := t₂.instantiateLevelParams lvls₂ $ lvls₁.map mkLevelParam
    let result := Kernel.isDefEq (← getEnv) {} t₁ t₂
    if (← read).config.skipDefEq then
      return match result with
        | .ok defeq => defeq
        -- Remark: we translate type errors to true instead of false because
        -- otherwise we get lots of false positives where definitions
        -- depending on a dubious translation are themselves marked dubious
        | .error .. => true
    else
      ofExceptKernelException result

  -- Note: "'" does not work any more, since there are many "'" suffixes in mathlib
  -- and the extended names may clash.
  extendName (n : Name) (suffix : String := "ₓ") : Name :=
    match n with
    | .str p s => .str p (s ++ suffix)
    | n        => .str n suffix

def refineLean4NamesAndUpdateMap (decl : Declaration) : BinportM (Declaration × ClashKind) := do
  let (decl', clashKind, ctors) ← refineLean4Names decl
  let dubious := if let .found msg := clashKind then msg else ""
  let tr (n3 n4 : Name) := do
    println! "[translateName] {n3} -> {n4}"
    addNameAlignment n3 n4 (n3.isStr && n3.getString! == `_main) dubious
    addPossibleFieldName n3 n4

  tr decl.toName decl'.toName

  match decl, decl' with
  | Declaration.inductDecl _ _ [indType3] _, Declaration.inductDecl _ _ [indType4] _ =>
    tr (indType3.name ++ `rec) (indType4.name ++ `rec)
    let ctors3 := indType3.ctors.map fun ctor =>
      { ctor with name := ctor.name.replacePrefix InductiveType.selfPlaceholder indType3.name }
    for (ctor3, ctor4) in
      ctors3.zip (if ctors.isEmpty then indType4.ctors.map Constructor.name else ctors)
    do
      tr ctor3.name ctor4
  | _, _ => pure ()

  pure (decl', clashKind)

end Mathport.Binary
