/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Daniel Selsam
-/
import Lean.Expr
import Mathport.Util.Misc
import Mathport.Util.Json
import Mathport.Syntax.AST3

namespace Mathport

open Lean (Json FromJson Position Name BinderInfo HashMap)
open Lean.FromJson (fromJson?)

namespace Parse

-- The following instance temporarily overrides the Lean4 instance
-- It is a minor convenience to avoid needing to translate `RawName` -> `Name` throughout the file.
local instance (priority := high) : FromJson Name where
  fromJson?
  | Json.null => pure Name.anonymous
  | Json.str s => pure (.mkSimple s)
  | Json.arr a => a.foldlM (init := Name.anonymous) fun
    | n, (i : Nat) => pure $ n.mkNum i
    | n, (s : String) => pure $ n.mkStr s
    | _, _ => throw "JSON string expected"
  | _ => throw "JSON array expected"

abbrev AstId := Nat
abbrev LevelId := Nat
abbrev ExprId := Nat
abbrev TacticStateId := Nat
abbrev Tag := Option AstId

structure RawNode3 where
  start    : Position
  «end»    : Option Position
  kind     : String
  value    : Name
  children : Option (Array AstId)
  pexpr    : Option ExprId
  expr     : Option ExprId
  deriving FromJson, Repr, Inhabited

def RawNode3.children' (n : RawNode3) : Array AstId := n.children.getD #[]
def RawNode3.end' (n : RawNode3) : Position := n.end.getD n.start

section
open AST3
open Lean3 (Proj)

structure State where
  notations : Array Notation := #[]
  cmds : Array Command := #[]
  tactics : HashMap AstId (Spanned AST3.Tactic) := {}

abbrev NotationKind := Option MixfixKind

structure Context where
  ast : Array (Option RawNode3)
  expr : Array Lean3.Expr
  getNotationId : NotationKind → Subarray AstId → StateT State (Except String) NotationId
  getInductiveId : Array AstId → StateT State (Except String) CommandId
  getCommandId : AstId → StateT State (Except String) CommandId
  deriving Inhabited

abbrev M := ReaderT Context $ StateT State $ Except String

def getNotationId (nk : NotationKind) (args : Subarray AstId) : M NotationId :=
  fun r => r.getNotationId nk args

def getInductiveId (args : Array AstId) : M NotationId :=
  fun r => r.getInductiveId args

def getCommandId (i : AstId) : M NotationId :=
  fun r => r.getCommandId i

def RawNode3.map (i : AstId) (n : RawNode3)
  (f : String → Name → Array AstId → M α) : M (Spanned α) := do
  pure ⟨some ⟨i, n.start, n.end'⟩, ← f n.kind n.value n.children'⟩

def RawNode3.pexpr' (n : RawNode3) : M Lean3.Expr :=
  match n.pexpr with
  | none => default
  | some e => return (← read).expr[e]!

def RawNode3.expr' (n : RawNode3) : M Lean3.Expr :=
  match n.expr with
  | none => default
  | some e => return (← read).expr[e]!

def opt (f : AstId → M α) (i : AstId) : M (Option α) :=
  if i = 0 then pure none else some <$> f i

def getRaw (i : AstId) : M RawNode3 := do
  match (← read).ast[i]! with
  | some a => pure a
  | none => dbgStackTrace fun _ =>
    throw $ if i = 0 then "unexpected null node" else "missing node"

def withNodeK (f : String → Name → Array AstId → M α) (i : AstId) : M α := do
  let r ← getRaw i
  f r.kind r.value r.children'

def withNode (f : String → Name → Array AstId → M α) (i : AstId) : M (Spanned α) := do
  let r ← getRaw i
  pure { meta := some ⟨i, r.start, r.end'⟩, kind := ← f r.kind r.value r.children' }

def withNodeP (f : String → Name → Array AstId → Option ExprId → M α) (i : AstId) :
    M (Spanned α) := do
  let r ← getRaw i
  pure { meta := some ⟨i, r.start, r.end'⟩, kind := ← f r.kind r.value r.children' r.pexpr }

def withNodeR (f : RawNode3 → M α) (i : AstId) : M (Spanned α) := do
  let r ← getRaw i
  pure { meta := some ⟨i, r.start, r.end'⟩, kind := ← f r }

def getRaw? : AstId → M (Option RawNode3) := opt getRaw

inductive NodeK : Type
  | mk (kind : String) (value : Name) (children : Array (Option (Spanned NodeK))) : NodeK
  deriving Inhabited

def Node := Spanned NodeK
instance : Inhabited Node := inferInstanceAs (Inhabited (Spanned NodeK))

open Std (Format) in
mutual

  partial def optNode_repr : Option Node → Format
    | none => ("⬝" : Format)
    | some a => NodeK_repr a.kind

  partial def NodeK_repr : NodeK → Format
    | ⟨k, v, c⟩ =>
      let s := (Lean.Name.escapePart k).getD k ++
        if v.isAnonymous then "" else "[" ++ v.toString ++ "]"
      if c.isEmpty then s else
        "(" ++ s ++ Format.join (c.toList.map fun c => Format.line ++ optNode_repr c) ++ ")"
          |>.nest 2 |>.group

end

instance : Repr NodeK := ⟨fun n _ => NodeK_repr n⟩
instance : Repr Node := inferInstanceAs (Repr (Spanned NodeK))

mutual

  partial def getNode : AstId → M Node := withNode mkNodeK

  partial def mkNodeK (k : String) (v : Name) (c : Array AstId) : M NodeK :=
    NodeK.mk k v <$> c.mapM (opt getNode)

end

def decodeNat! (v : Name) : Nat :=
  (Lean.Syntax.decodeNatLitVal? v.getString!).get!

def decodeDecimal! (v : Name) : Nat × Nat :=
  let v := v.getString!
  match String.split v (· = '/') with
  | [n, d] => ((Lean.Syntax.decodeNatLitVal? n).get!, (Lean.Syntax.decodeNatLitVal? d).get!)
  | _ => ((Lean.Syntax.decodeNatLitVal? v).get!, 1)

def getNat : AstId → M (Spanned Nat) := withNode fun _ v _ => pure $ decodeNat! v

def getNameK : AstId → M Name := withNodeK fun _ v _ => pure v
def getName : AstId → M (Spanned Name) := withNode fun _ v _ => pure v

def getStrK : AstId → M String := withNodeK fun _ v _ => pure v.getString!
def getStr : AstId → M (Spanned String) := withNode fun _ v _ => pure v.getString!

def getSym : AstId → M (Spanned Symbol) :=
  withNode fun
  | "quoted", v, _ => pure $ Symbol.quoted v.getString!
  | "ident", v, _ => pure $ Symbol.ident v.getString!
  | k, _, _ => throw s!"getSym parse error, unknown kind {k}"

def getBinderName : AstId → M (Spanned BinderName) :=
  withNode fun
  | "_", _, _ => pure BinderName.«_»
  | "ident", v, _ => pure $ BinderName.ident v
  | k, _, _ => throw s!"getBinderName parse error, unknown kind {k}"

def getChoice : AstId → M Choice :=
  withNodeK fun
  | "choice", _, args => Choice.many <$> args.mapM getNameK
  | "notation", v, _ => pure $ Choice.one v
  | k, _, _ => throw s!"getChoice parse error, unknown kind {k}"

def getProj : AstId → M (Spanned Proj) :=
  withNode fun
  | "nat", v, _ => pure $ Proj.nat (decodeNat! v)
  | "ident", v, _ => pure $ Proj.ident v
  | k, _, _ => throw s!"getSym parse error, unknown kind {k}"

def getOptionVal : AstId → M (Spanned OptionVal) :=
  withNode fun
  | "nat", v, _ => pure $ OptionVal.nat (decodeNat! v)
  | "ident", v, _ => pure $ OptionVal.str v.getString!
  | "bool", v, _ => pure $ OptionVal.bool (v == `true)
  | "decimal", v, _ => let (n, d) := decodeDecimal! v; pure $ OptionVal.decimal n d
  | k, _, _ => throw s!"getOptionVal parse error, unknown kind {k}"

def getInferKind : AstId → M InferKind :=
  withNodeK fun
  | "{}", _, _ => pure InferKind.relaxedImplicit
  | "()", _, _ => pure InferKind.none
  | "[]", _, _ => pure InferKind.implicit
  | k, _, _ => throw s!"getInferKind parse error, unknown kind {k}"

def arr (f : AstId → M α) (i : AstId) : M (Array α) := do
  match ← getRaw? i with
  | some n => n.children'.mapM f
  | none => pure #[]

def ctx (s : String) (m : M α) : M α := do
  try m catch e => throw $ "at " ++ s ++ ": " ++ e


def toNotationKind : String → Option NotationKind
| "infix" => some (some MixfixKind.infix)
| "infixl" => some (some MixfixKind.infixl)
| "infixr" => some (some MixfixKind.infixr)
| "postfix" => some (some MixfixKind.postfix)
| "prefix" => some (some MixfixKind.prefix)
| "notation" => some none
| _ => none

open Level in
partial def getLevel : AstId → M (Spanned Level) :=
  withNode fun
  | "_", _, _ => pure «_»
  | "param", v, _ => pure $ «param» v
  | "max", _, args => Level.«max» <$> args.mapM getLevel
  | "imax", _, args => Level.«imax» <$> args.mapM getLevel
  | "nat", v, _ => pure $ Level.nat $ decodeNat! v
  | "+", _, #[a, b] => return Level.add (← getLevel a) (← getNat b)
  | "(", _, #[e] => Level.paren <$> getLevel e
  | k, _, _ => throw s!"getLevel parse error, unknown kind {k}"

def getLevels : AstId → M Levels := opt (arr getLevel)
def getLevelDecl : AstId → M LevelDecl := opt (arr getName)

def wrapperNotations : Lean.NameHashSet :=
  List.foldl (·.insert ·) {} [
    `by, `have, `assume, `show, `suffices, `if, `«(», `«⟨», `«{», `«{!», `«.(», `«._»,
    `«```(», `«``(», `«`(», `«`[», `«`», `«%%», `«#[», `«(:», `«()», `«(::)», `fun, `Type,
    `«Type*», `Sort, `«Sort*», `let, `calc, `«@», `«@@», `begin, `sorry, `match, `do]

mutual

  partial def getDefaultOrCollection :
    AstId → M (Sum Default (Name × Spanned Expr)) := withNodeK fun
    | ":=", _, #[e] => return Sum.inl $ Default.«:=» $ ← getExpr e
    | ".", _, #[e] => return Sum.inl $ Default.«.» $ ← getName e
    | "collection", v, #[rhs] => return Sum.inr (v, ← getExpr rhs)
    | k, _, _ => throw s!"getDefault parse error, unknown kind {k}"

  partial def getDefault (n : AstId) : M (Option Default) := do
    match ← opt getDefaultOrCollection n with
    | none => pure none
    | some (Sum.inl dflt) => pure $ some dflt
    | _ => throw s!"getDefault parse error"

  partial def getBinder : AstId → M (Spanned Binder) := withNode getBinder_aux

  partial def getBinder_aux
    | "binder_0", _, args => binder BinderInfo.default args
    | "binder_1", _, args => binder BinderInfo.instImplicit args
    | "binder_2", _, args => binder BinderInfo.strictImplicit args
    | "binder_4", _, args => binder BinderInfo.implicit args
    | "binder_8", _, args => binder BinderInfo.default args -- aux decl binders not supported
    | k, _, args => match toNotationKind k with
      | some nk => Binder.notation <$> getNotationId nk args
      | none => throw s!"getBinder parse error, unknown kind {k}"
  where
    binder (bi : BinderInfo) (args : Array AstId) : M Binder := do
      match ← opt (arr getBinderName) args[0]!, ← getBinders args[1]!, ← opt getExpr args[2]!,
        ← opt getDefaultOrCollection (args.getD 3 0) with
      | vars, bis, ty, none => pure $ Binder.binder bi vars bis ty none
      | vars, bis, ty, some (Sum.inl dflt) => pure $ Binder.binder bi vars bis ty dflt
      | some vars, #[], none, some (Sum.inr (c, rhs)) => pure $ Binder.collection bi vars c rhs
      | _, _, _, _ => throw s!"getBinder parse error"
  partial def getBinders : AstId → M Binders := arr getBinder

  partial def getLambdaBinder : AstId → M (Spanned LambdaBinder) := withNode fun
    | "⟨", _, args => LambdaBinder.«⟨⟩» <$> args.mapM getExpr
    | k, v, args => LambdaBinder.reg <$> getBinder_aux k v args

  partial def getLetDecl : AstId → M (Spanned LetDecl) := withNode fun
    | "var", _, #[x, bis, ty, e] => return (LetDecl.var (← getBinderName x)
      (← getBinders bis) (← opt getExpr ty) (← getExpr e))
    | "pat", _, #[pat, e] => return LetDecl.pat (← getExpr pat) (← getExpr e)
    | k, _, args => match toNotationKind k with
      | some nk => LetDecl.notation <$> getNotationId nk args
      | none => throw s!"getBinder parse error, unknown kind {k}"

  partial def getArg : AstId → M (Spanned Arg) :=
    withNodeP fun
    | "exprs", _, args, _ => Arg.exprs <$> args.mapM getExpr
    | "binders", _, args, _ => Arg.binders <$> args.mapM getBinder
    | k, v, args, pexpr => if k.startsWith "binder"
      then Arg.binder <$> getBinder_aux k v args
      else Arg.expr <$> getExpr_aux k v args pexpr

  partial def getExpr_aux : String → Name → Array AstId → Option ExprId → M Expr
    | "notation", v, args, _ => match v with
      | `«->» => return Expr.«→» (← getExpr args[0]!) (← getExpr args[1]!)
      | `Pi => return Expr.«Pi» (← getBinders args[0]!) (← getExpr args[1]!)
      | `«^.» => Spanned.kind <$> getExpr args[1]!
      | _ => if wrapperNotations.contains v
        then Spanned.kind <$> getExpr args[0]!
        else Expr.notation (Choice.one v) <$> args.mapM getArg
    | "sorry", _, _, _ => pure Expr.«sorry»
    | "_", _, _, _ => pure Expr.«_»
    | "()", _, _, _ => pure Expr.«()»
    | "{}", _, _, _ => pure Expr.«{}»
    | "ident", v, _, _ => pure $ Expr.ident v
    | "const", _, #[n, us], none => return Expr.const (← getName n) (← opt (arr getLevel) us) #[]
    | "const", _, #[n, us], some pexprId => do
      match (← read).expr[pexprId]! with
      | Lean3.Expr.const resolved _ =>
        return Expr.const (← getName n) (← opt (arr getLevel) us) #[resolved]
      | pexpr => throw s!"[const.pexpr] not a const: {repr pexpr}"
    | "choice_const", _, #[n, us], none => do
        dbg_trace "[getExpr_aux.warn] choice_const {(← getName n).kind} has no choices"
        pure $ Expr.const (← getName n) (← opt (arr getLevel) us) #[]
    | "choice_const", _, #[n, us], some pexprId => do
      match (← read).expr[pexprId]! with
      | Lean3.Expr.choice args =>
        let choices ← args.mapM fun
        | Lean3.Expr.const n _ => pure n
        | choice => do throw s!"[getExpr_aux.error] choice_const {
          (← getName n).kind} expecting constants, found {repr choice}"
        return Expr.const (← getName n) (← opt (arr getLevel) us) choices
      | _ => throw s!"choice_const: expecting choice"
    | "nat", v, _, _ => pure $ Expr.nat $ decodeNat! v
    | "decimal", v, _, _ => let (n, d) := decodeDecimal! v; pure $ Expr.decimal n d
    | "string", v, _, _ => pure $ Expr.string v.getString!
    | "char", v, _, _ => pure $ Expr.char v.getString!.front
    | "(", _, #[e], _ => Expr.paren <$> getExpr e
    | "Sort*", _, _, _ => pure $ Expr.sort false true none
    | "Type*", _, _, _ => pure $ Expr.sort true true none
    | "Sort", _, #[l], _ => Expr.sort false false <$> opt getLevel l
    | "Type", _, #[l], _ => Expr.sort true false <$> opt getLevel l
    | "app", _, #[f, x], _ => return Expr.app (← getExpr f) (← getExpr x)
    | "fun", _, #[bis, e], _ => return Expr.fun false (← arr getLambdaBinder bis) (← getExpr e)
    | "assume", _, #[bis, e], _ => return Expr.fun true (← arr getLambdaBinder bis) (← getExpr e)
    | "show", _, #[ty, e], _ => return Expr.show (← getExpr ty) (← getProof e)
    | "have", _, args, _ => getHave false args
    | "suffices", _, args, _ => getHave true args
    | "field", _, #[e, pr], _ => return Expr.«.» true (← getExpr e) (← getProj pr)
    | "^.", _, #[e, pr], _ => return Expr.«.» false (← getExpr e) (← getProj pr)
    | "if", _, #[h, c, t, e], _ =>
      return Expr.if (← opt getName h) (← getExpr c) (← getExpr t) (← getExpr e)
    | "calc", _, args, _ => Expr.calc <$> args.mapM getStep
    | "@", _, #[e], _ => Expr.«@» false <$> getExpr e
    | "@@", _, #[e], _ => Expr.«@» true <$> getExpr e
    | "(:", _, #[e], _ => Expr.pattern <$> getExpr e
    | "```()", _, #[e], _ => Expr.«`()» true false <$> getExpr e
    | "``()", _, #[e], _ => Expr.«`()» false false <$> getExpr e
    | "`()", _, #[e], _ => Expr.«`()» false true <$> getExpr e
    | "%%", _, #[e], _ => Expr.«%%» <$> getExpr e
    | "`[", _, args, _ => Expr.«`[]» <$> args.mapM getTactic
    | "`", v, _, _ => pure $ Expr.«`» false v
    | "``", v, _, _ => pure $ Expr.«`» true v
    | "⟨", _, args, _ => Expr.«⟨⟩» <$> args.mapM getExpr
    | "infix_fn", _, #[f, e], _ => return Expr.infix_fn (← getChoice f) (← opt getExpr e)
    | "tuple", _, args, _ => Expr.«(,)» <$> args.mapM getExpr
    | ":", _, #[e, ty], _ => return Expr.«:» (← getExpr e) (← getExpr ty)
    | "{!", _, args, _ => Expr.hole <$> args.mapM getExpr
    | "#[", _, args, _ => Expr.«#[]» <$> args.mapM getExpr
    | "by", _, #[tac], _ => Expr.by <$> getTactic tac
    | "begin", _, args, _ => Expr.begin <$> getBlock false args
    | "let", _, #[decls, e], _ => return Expr.let (← arr getLetDecl decls) (← getExpr e)
    | "match", _, #[e, ty, arms], _ =>
      return Expr.match (← arr getExpr e) (← opt getExpr ty) (← arr getArm arms)
    | "do", v, args, _ => Expr.do (!v.isAnonymous) <$> args.mapM getDoElem
    | "fin_set", _, args, _ => Expr.«{,}» <$> args.mapM getExpr
    | "subtype", _, args, _ => getSubtype false args
    | "set_of", _, args, _ => getSubtype true args
    | "sep", _, #[x, S, p], _ => return Expr.sep (← getName x) (← getExpr S) (← getExpr p)
    | "set_replacement", _, #[e, bis], _ =>
      return Expr.setReplacement (← getExpr e) (← getBinders bis)
    | "structinst", _, #[S, src, flds, srcs, catchall], _ =>
      return Expr.structInst (← opt getName S) (← opt getExpr src)
        (← arr getField flds) (← arr getExpr srcs) (catchall ≠ 0)
    | "at_pat", _, #[n, pat], _ => return Expr.atPat (← getName n) (← getExpr pat)
    | ".(", _, #[e], _ => Expr.«.()» <$> getExpr e
    | "...", _, _, _ => pure Expr.«...»
    | "choice", _, args, _ =>
      return Expr.notation (Choice.many (← arr getNameK args[0]!)) (← args[1:].toArray.mapM getArg)
    | "user_notation", v, args, _ => Expr.userNotation v <$> args.mapM getParam
    | k, _v, _args, _ => do
      throw s!"getExpr parse error, unknown kind {k}"
        -- at\n {repr (← Expr.other <$> mkNodeK k v args)}"
  where
    getHave (suff : Bool) (args) : M _ :=
      return Expr.have suff (← opt getName args[0]!)
        (← getExpr args[1]!) (← getProof args[2]!) (← getExpr args[3]!)
    getStep := withNodeK fun _ _ args => do pure (← getExpr args[0]!, ← getExpr args[1]!)
    getField := withNodeK fun _ _ args => do pure (← getName args[0]!, ← getExpr args[1]!)
    getSubtype (setOf : Bool) (args) : M _ :=
      return Expr.subtype setOf (← getName args[0]!) (← opt getExpr args[1]!) (← getExpr args[2]!)

  partial def getExpr : AstId → M (Spanned Expr) := withNodeP getExpr_aux

  partial def getArm : AstId → M Arm := withNodeK fun _ _ args => do
    pure ⟨← arr getExpr args[0]!, ← getExpr args[1]!⟩

  partial def getDoElem : AstId → M (Spanned DoElem) :=
    withNode fun
    | "let", _, #[decl] => DoElem.let <$> getLetDecl decl
    | "<-", _, #[pat, ty, rhs, els] =>
      return DoElem.«←» (← getExpr pat) (← opt getExpr ty) (← getExpr rhs) (← opt getExpr els)
    | "eval", _, #[e] => DoElem.eval <$> getExpr e
    | k, _, _ => throw s!"getDoElem parse error, unknown kind {k}"

  partial def getProof : AstId → M (Spanned Proof) :=
    withNode fun
    | ":=", _, #[e] => Proof.from true <$> getExpr e
    | "from", _, #[e] => Proof.from false <$> getExpr e
    | "begin", _, args => Proof.block <$> getBlock false args
    | "{", _, args => Proof.block <$> getBlock true args
    | "by", _, #[tac] => Proof.by <$> getTactic tac
    | k, _, _ => throw s!"getProof parse error, unknown kind {k}"

  partial def getTactic (i : AstId) : M (Spanned Tactic) := do
    let getTactic' := withNode fun
    | ";", _, args => Tactic.«;» <$> args.mapM getTactic
    | "<|>", _, args => Tactic.«<|>» <$> args.mapM getTactic
    | "[", _, args => Tactic.«[]» <$> args.mapM getTactic
    | "begin", _, args => Tactic.block <$> getBlock false args
    | "{", _, args => Tactic.block <$> getBlock true args
    | "by", _, #[tac] => Tactic.by <$> getTactic tac
    | "exact_shortcut", _, #[e] => Tactic.exact_shortcut <$> getExpr e
    | "(", _, #[e] => Tactic.expr <$> getExpr e
    | "tactic", v, args => Tactic.interactive v <$> args.mapM getParam
    | k, _, _ => throw s!"getTactic parse error, unknown kind {k}"
    let t ← getTactic' i
    modify fun s => { s with tactics := s.tactics.insert i t }
    pure t

  partial def getBlock (curly : Bool) (args : Array AstId) : M Block := do
    pure ⟨curly, ← opt getName args[0]!, ← opt getExpr args[1]!, ← args[2:].toArray.mapM getTactic⟩

  partial def getParam : AstId → M (Spanned Param) :=
    withNodeR fun r => match r.kind with
    | "parse" => return Param.parse (← r.pexpr') (← r.children'.mapM getVMCall)
    | "expr" => Param.expr <$> getExpr r.children'[0]!
    | "begin" => Param.block <$> getBlock false r.children'
    | "{" => Param.block <$> getBlock true r.children'
    | k => throw s!"getParam parse error, unknown kind {k}"

  partial def getVMCall : AstId → M (Spanned VMCall) :=
    withNode fun
    | "ident", v, _ => pure $ VMCall.ident v
    | "nat", v, _ => pure $ VMCall.nat $ decodeNat! v
    | "token", v, _ => pure $ VMCall.token v.getString!
    | "pat", _, #[e] => return VMCall.pat (← getExpr e).kind
    | "expr", _, #[e] => return VMCall.expr (← getExpr e).kind
    | "binders", _, args => VMCall.binders <$> args.mapM getBinder
    | "begin", _, args => VMCall.block <$> getBlock false args
    | "{", _, args => VMCall.block <$> getBlock true args
    | "inductive", _, args => VMCall.inductive <$> getInductiveId args
    | "command", _, args => VMCall.command <$> opt getCommandId (args.getD 0 0)
    | "with_input", v, args => return VMCall.withInput (← args.mapM getVMCall) (decodeNat! v)
    | k, _, _ => throw s!"getVMCall parse error, unknown kind {k}"

end

partial def getPrec : AstId → M (Spanned Precedence) :=
  withNode fun
  | "nat", v, _ => pure $ Precedence.nat $ decodeNat! v
  | "expr", _, #[e] => Precedence.expr <$> getExpr e
  | k, _, _ => throw s!"getPrec parse error, unknown kind {k}"

partial def getPrecSym_aux (args : Array AstId) : M PrecSymbol :=
  return (← getSym args[0]!, ← opt getPrec args[1]!)

partial def getPrecSym : AstId → M PrecSymbol := withNodeK fun _ _ => getPrecSym_aux

partial def getAction : AstId → M (Spanned Action) :=
  withNode fun
  | "nat", v, _ => pure $ Action.prec $ Precedence.nat $ decodeNat! v
  | "expr", _, #[e] => return Action.prec $ Precedence.expr $ ← getExpr e
  | "prev", _, _ => pure Action.prev
  | "scoped", _, #[p, sc] => do
    let scope i := do
      let args := (← getRaw i).children'
      pure (← getName args[0]!, ← getExpr args[1]!)
    pure $ Action.scoped (← opt getPrec p) (← opt scope sc)
  | "foldl", _, args => getFold false args
  | "foldr", _, args => getFold true args
  | k, _, _ => throw s!"getAction parse error, unknown kind {k}"
where
  getFold (r) (args : Array AstId) : M Action := do
    let sc := (← getRaw args[2]!).children'
    pure $ Action.fold r
      (← opt getPrec args[0]!) (← getPrecSym args[1]!)
      (← getName sc[0]!, ← getName sc[1]!, ← getExpr sc[2]!)
      (← opt getExpr args[3]!) (← opt getPrecSym args[4]!)

partial def getLiteral : AstId → M (Spanned Literal) :=
  withNode fun
  | "nat", v, _ => pure $ Literal.nat $ decodeNat! v
  | "var", _, #[v, act] => return Literal.var (← getName v) (← opt getAction act)
  | "sym", _,  args => Literal.sym <$> getPrecSym_aux args
  | "binder", _, #[p] => Literal.binder <$> opt getPrec p
  | "binders", _, #[p] => Literal.binders <$> opt getPrec p
  | k, _, _ => throw s!"getLiteral parse error, unknown kind {k}"

partial def getNotationDef (nk : NotationKind) (args : Subarray AstId) : M Notation :=
  match nk with
  | some nk =>
    return Notation.mixfix nk (← opt getName args[0]!)
      (← getSym args[1]!, ← opt getPrec args[2]!) (← opt getExpr args[3]!)
  | none =>
    return Notation.notation (← opt getName args[0]!)
      (← arr getLiteral args[1]!) (← opt getExpr args[2]!)

partial def getNotation' : AstId → M Notation :=
  withNodeK fun k _ a => getNotationDef (toNotationKind k).get! a

partial def getNotation : AstId → M NotationId :=
  withNodeK fun k _ a => getNotationId (toNotationKind k).get! a

partial def getField : AstId → M (Spanned Field) := withNode fun
  | "field_0", _, args => field BinderInfo.default args
  | "field_1", _, args => field BinderInfo.instImplicit args
  | "field_2", _, args => field BinderInfo.strictImplicit args
  | "field_4", _, args => field BinderInfo.implicit args
  | "field_8", _, args => field BinderInfo.default args -- aux decl binders not supported
  | k, _, args => match toNotationKind k with
    | some nk => Field.notation <$> getNotationDef nk args
    | none => throw s!"getField parse error, unknown kind {k}"
where
  field (bi : BinderInfo) (args : Array AstId) : M Field :=
    return Field.binder bi (← arr getName args[0]!) (← opt getInferKind args[1]!)
      (← getBinders args[2]!) (← opt getExpr args[3]!) (← getDefault (args.getD 4 0))

def getAttrArg : AstId → M (Spanned AttrArg) := withNodeR fun r =>
  match r.kind with
  | "!" => pure AttrArg.eager
  | "indices" => AttrArg.indices <$> r.children'.mapM getNat
  | "key_value" => return AttrArg.keyValue (← getStr r.children'[0]!) (← getStr r.children'[1]!)
  | "vm_override" =>
    return AttrArg.vmOverride (← getName r.children'[0]!) (← opt getName r.children'[1]!)
  | "parse" => return AttrArg.user (← r.pexpr') (← r.children'.mapM getVMCall)
  | k => throw s!"getAttrArg parse error, unknown kind {k}"

def getAttr : AstId → M (Spanned Attribute) := withNode fun
  | "priority", _, #[e] => Attribute.priority <$> getExpr e
  | "attr", v, #[del, arg] =>
    if del = 0 then Attribute.add v <$> opt getAttrArg arg
    else pure $ Attribute.del v
  | k, _, _ => throw s!"getAttr parse error, unknown kind {k}"

open DeclVal in
def getDeclVal : AstId → M (Spanned DeclVal) :=
  withNodeP fun
  | "eqns", _, args, _ => eqns <$> args.mapM getArm
  | k, v, args, pexpr => expr <$> getExpr_aux k v args pexpr

open Modifier in
def getModifier : AstId → M (Spanned Modifier) := withNode fun
  | "private", _, _ => pure «private»
  | "protected", _, _ => pure «protected»
  | "noncomputable", _, _ => pure «noncomputable»
  | "meta", _, _ => pure «meta»
  | "mutual", _, _ => pure «mutual»
  | "doc", v, _ => pure $ doc v.getString!
  | "@[", _, #[a] => attr false true <$> arr getAttr a
  | "attribute", _, #[loc, a] => attr (loc ≠ 0) false <$> arr getAttr a
  | k, _, _ => throw s!"getModifier parse error, unknown kind {k}"

def getModifiers : AstId → M Modifiers := arr getModifier

def getLocal (i : AstId) : M LocalReserve := do
  match (← getRaw? i).map fun n => n.kind with
  | some "local"   => pure (true, false)
  | some "reserve" => pure (false, true)
  | none           => pure (false, false)
  | _ => throw "getLocal parse error"

def getIntro : AstId → M (Spanned Intro) := withNode fun _ _ args => do
  pure ⟨← opt getStrK args[0]!, ← getName args[1]!,
    ← opt getInferKind args[2]!, ← getBinders args[3]!, ← opt getExpr args[4]!⟩

def getRename : AstId → M Rename := withNodeK fun _ _ args => do
  pure ⟨← getName args[0]!, ← getName args[1]!⟩

def getParent : AstId → M (Spanned Parent) := withNode fun _ _ args => do
  pure ⟨args[0]! ≠ 0, ← opt getName args[1]!, ← getExpr args[2]!, ← arr getRename args[3]!⟩

def getMk : AstId → M (Spanned Mk) := withNode fun _ _ args => do
  pure ⟨← getName args[0]!, ← opt getInferKind args[1]!⟩

def getMutual {α} (f : AstId → M α) : AstId → M (Mutual α) := withNodeK fun _ _ args => do
  pure ⟨← arr getAttr args[0]!, ← getName args[1]!, ← getExpr args[2]!, ← arr f args[3]!⟩

open OpenClause in
def getOpenClause : AstId → M (Spanned OpenClause) :=
  withNode fun
  | "explicit", _, args => explicit <$> args.mapM getName
  | "renaming", _, args => «renaming» <$> args.mapM getRename
  | "hiding", _, args => «hiding» <$> args.mapM getName
  | k, _, _ => throw s!"getOpenClause parse error, unknown kind {k}"

def getOpen : AstId → M Open := withNodeK fun _ _ args => do
  pure ⟨← getName args[0]!, ← opt getName args[1]!, ← args[2:].toArray.mapM getOpenClause⟩

open HelpCmd in
def getHelpCmd : AstId → M HelpCmd := withNodeK fun
  | "options", _, _ => pure options
  | "commands", _, _ => pure commands
  | k, _, _ => throw s!"getHelpCmd parse error, unknown kind {k}"

open PrintAttrCmd in
def getPrintAttrCmd : AstId → M (Spanned PrintAttrCmd) := withNode fun
  | "recursor", _, _ => pure recursor
  | "unify", _, _ => pure unify
  | "simp", _, _ => pure simp
  | "congr", _, _ => pure congr
  | "attr", v, _ => pure $ attr v
  | k, _, _ => throw s!"getPrintAttrCmd parse error, unknown kind {k}"

open PrintCmd in
def getPrintCmd (args : Array AstId) : M PrintCmd := do
  let r ← getRaw args[0]!
  match r.kind with
  | "string" => pure $ str r.value.getString!
  | "raw" => raw <$> getExpr args[1]!
  | "options" => pure options
  | "trust" => pure trust
  | "key_equivalences" => pure keyEquivalences
  | "definition" => «def» <$> getName args[1]!
  | "instances" => instances <$> getName args[1]!
  | "classes" => pure classes
  | "attributes" => pure attributes
  | "prefix" => «prefix» <$> getName args[1]!
  | "aliases" => pure aliases
  | "axioms" => axioms <$> opt getName args[1]!
  | "fields" => fields <$> getName args[1]!
  | "notation" => «notation» <$> args.mapM getName
  | "inductive" => «inductive» <$> getName args[1]!
  | "attribute" => attr <$> getPrintAttrCmd args[1]!
  | "token" => token <$> r.map args[0]! fun _ v _ => pure v
  | "ident" => ident <$> r.map args[0]! fun _ v _ => pure v
  | k => throw s!"getPrintCmd parse error, unknown kind {k}"

def getHeader (args : Subarray AstId) :
  M (LevelDecl × Option (Spanned Name) × Binders × Option (Spanned Expr)) := do
  pure (← getLevelDecl args[0]!, ← opt getName args[1]!,
    ← getBinders args[2]!, ← opt getExpr args[3]!)

def getMutualHeader (args : Subarray AstId) : M (LevelDecl × Binders) := do
  pure (← getLevelDecl args[0]!, /- ← arr getName args[1]!, -/ ← getBinders args[2]!)

def getInductive (cl : Bool) (args : Array AstId) : M InductiveCmd := do
  let mods ← getModifiers args[0]!
  if args[1]! = 0 then
    let (us, n, bis, ty) ← getHeader args[2:6]
    let nota ← opt getNotation' args[6]!
    pure $ InductiveCmd.reg cl mods n.get! us bis ty nota (← arr getIntro args[7]!)
  else
    let (us, bis) ← getMutualHeader args[2:5]
    let nota ← opt getNotation' args[5]!
    pure $ InductiveCmd.mutual cl mods us bis nota (← arr (getMutual getIntro) args[6]!)

open Command in
def getCommand : AstId → M (Spanned Command) :=
  withNode fun
  -- | "prelude", _, _ => «prelude»
  | "init_quotient", _, _ => pure initQuotient
  -- | "import", _, args => «import» <$> args.mapM getName
  | "mdoc", v, _ => pure $ mdoc v.getString!
  | "namespace", _, #[n] => «namespace» <$> getName n
  | "section", _, #[n] => «section» <$> opt getName n
  | "end", _, #[n] => «end» <$> opt getName n
  | "universe", _, args => «universe» false false <$> args.mapM getName
  | "universes", _, args => «universe» false true <$> args.mapM getName
  | "universe_variable", _, args => «universe» true false <$> args.mapM getName
  | "universe_variables", _, args => «universe» true true <$> args.mapM getName
  | "axiom", _, args => getAxiom AxiomKind.axiom args
  | "constant", _, args => getAxiom AxiomKind.constant args
  | "axioms", _, args => getVars args $ «axioms» AxiomKind.axiom
  | "constants", _, args => getVars args $ «axioms» AxiomKind.constant
  | "variable", _, args => getVars args $ «variable» VariableKind.variable false
  | "parameter", _, args => getVars args $ «variable» VariableKind.parameter false
  | "variables", _, args => getVars args $ «variable» VariableKind.variable true
  | "parameters", _, args => getVars args $ «variable» VariableKind.parameter true
  | "definition", _, args => getDecl DeclKind.def args
  | "theorem", _, args => getDecl DeclKind.theorem args
  | "abbreviation", _, args => getDecl DeclKind.abbrev args
  | "example", _, args => getDecl DeclKind.example args
  | "instance", _, args => getDecl DeclKind.instance args
  | "inductive", _, args => Command.inductive <$> getInductive false args
  | "class_inductive", _, args => Command.inductive <$> getInductive true args
  | "structure", _, args => getStructure false args
  | "class", _, args => getStructure true args
  | "attribute", _, args => getAttribute args
  | "precedence", _, #[c, p] => return precedence (← getSym c) (← getPrec p)
  | "open", _, args => «open» false <$> args.mapM getOpen
  | "export", _, args => «open» true <$> args.mapM getOpen
  | "include", _, args => «include» true <$> args.mapM getName
  | "omit", _, args => «include» false <$> args.mapM getName
  | "hide", _, args => «hide» <$> args.mapM getName
  | "theory", _, #[mods] => «theory» <$> getModifiers mods
  | "set_option", _, #[opt, val] => return setOption (← getName opt) (← getOptionVal val)
  | "declare_trace", _, #[n] => declareTrace <$> getName n
  | "add_key_equivalence", _, #[n1, n2] => return addKeyEquivalence (← getName n1) (← getName n2)
  | "run_cmd", _, #[e] => runCmd <$> getExpr e
  | "#check", _, #[e] => check <$> getExpr e
  | "#reduce", _, #[whnf, e] => reduce (whnf ≠ 0) <$> getExpr e
  | "#eval", _, #[e] => eval <$> getExpr e
  | "#unify", _, #[e1, e2] => return unify (← getExpr e1) (← getExpr e2)
  | "#compile", _, #[e] => eval <$> getExpr e
  | "#help", _, #[arg] => help <$> getHelpCmd arg
  | "#print", _, args => print <$> getPrintCmd args
  | "user_command", v, args =>
    return userCommand v (← getModifiers args[0]!) (← args[1:].toArray.mapM getParam)
  | k, _, args => match toNotationKind k with
    | some nk => getNotationCmd nk args
    | none => throw s!"getCommand parse error, unknown kind {k}"
where
  getAxiom (ak) (args : Array AstId) : M Command :=
    return Command.axiom ak
      (← getModifiers args[0]!) (← getName args[2]!) (← getLevelDecl args[1]!)
      (← getBinders args[3]!) (← getExpr args[4]!)

  getVars (args : Array AstId) (f : Modifiers → Binders → Command) : M Command := do
    f (← getModifiers args[0]!) <$> args[1:].toArray.mapM getBinder

  getUWF : AstId → M (Spanned Expr) := withNodeK fun _ _ args => getExpr args[0]!

  getDecl (dk) (args : Array AstId) : M Command := do
    let mods ← getModifiers args[0]!
    if args[1]! = 0 then
      let (us, n, bis, ty) ← getHeader args[2:6]
      let val ← getDeclVal args[6]!
      let uwf ← if let .expr _ := val.kind then pure none else opt getUWF args[7]!
      pure $ .decl dk mods n us bis ty val uwf
    else
      let (us, bis) ← getMutualHeader args[2:5]
      pure $ .mutualDecl dk mods us bis (← arr (getMutual getArm) args[5]!) (← opt getUWF args[6]!)

  getNotationCmd (mk : Option MixfixKind) (args : Array AstId) : M Command :=
    return Command.notation
      (← getLocal args[0]!) (← arr getAttr args[1]!) (← getNotationDef mk args[2:])

  getStructure (cl args) : M Command := do
    return Command.structure cl (← getModifiers args[0]!) (← getName args[2]!)
      (← getLevelDecl args[1]!) (← getBinders args[3]!) (← arr getParent args[4]!)
      (← opt getExpr args[5]!) (← opt getMk args[6]!) (← arr getField args[7]!)

  getAttribute (args) : M Command := do
    let mods ← getModifiers args[0]!
    pure $ «attribute» (args[1]! ≠ 0) mods
      (← arr getAttr args[2]!) (← args[3:].toArray.mapM getName)

def getAST (comments : Array Comment) :
    AstId → M (AST3 × HashMap AstId (Spanned AST3.Tactic)) := withNodeK fun
  | "file", _, #[prel, imp, cmds] => do
    let prel ← opt (withNode fun _ _ _ => pure ()) prel
    let imp ← arr (withNodeK fun _ _ args => args.mapM getName) imp
    let cmds ← arr getCommand cmds
    let ⟨inota, icmds, tacs⟩ ← get
    pure (⟨prel, imp, cmds, inota, icmds, comments⟩, tacs)
  | k, _, args => throw s!"getAST parse error, unknown kind {k}, {args}"

partial def M.run (ast : Array (Option RawNode3)) (expr : Array Lean3.Expr) :
  M α → Except String α :=
  fun m => (m ctx).run' {}
where
  pushCmd c := do
    let n := (← get).cmds.size
    modify fun s => { s with cmds := s.cmds.push c }
    pure n
  pushNota nota := do
    let n := (← get).notations.size
    modify fun s => { s with notations := s.notations.push nota }
    pure n
  ctx := {
    ast, expr
    getNotationId := fun nk args => do pushNota (← getNotationDef nk args ctx)
    getInductiveId := fun args => do pushCmd (Command.inductive (← getInductive false args ctx))
    getCommandId := fun i => do pushCmd (← getCommand i ctx).kind }

end

inductive RawLevel where
  | «0»
  | suc : LevelId → RawLevel
  | max : Array LevelId → RawLevel
  | imax : Array LevelId → RawLevel
  | param : Name → RawLevel
  | mvar : Name → RawLevel
  deriving FromJson

instance : FromJson RawLevel :=
  ⟨fun x => do
    try fromJson? x
    catch e => throw s!"at: {x}\n{e}"⟩

instance : FromJson BinderInfo where
  fromJson? j := do
    match ← j.getNat? with
    | 0 => pure BinderInfo.default
    | 1 => pure BinderInfo.instImplicit
    | 2 => pure BinderInfo.strictImplicit
    | 4 => pure BinderInfo.implicit
    | 8 => pure BinderInfo.default -- aux decl binders not supported
    | _ => throw "unknown binder type"

inductive Annotation
  | no_univ
  | do_failure_eq
  | infix_fn
  | begin_hole
  | end_hole
  | anonymous_constructor
  | «calc»
  | no_info
  | frozen_name
  | «have»
  | «show»
  | «suffices»
  | checkpoint
  | «@»
  | «@@»
  | as_atomic
  | as_is
  | antiquote
  | expr_quote_pre
  | comp_irrel
  | inaccessible
  | «by»
  | pattern_hint
  | th_proof
  deriving FromJson

inductive RawExpr where
  | var : Nat → RawExpr
  | sort : LevelId → RawExpr
  | const : Name → Array LevelId → RawExpr
  | app : ExprId → ExprId → RawExpr
  | lam (name : Name) (bi : BinderInfo) (dom body : ExprId)
  | Pi (name : Name) (bi : BinderInfo) (dom body : ExprId)
  | «let» (name : Name) (type value body : ExprId)
  | «local» (name pp : Name) (bi : BinderInfo) (type : ExprId)
  | mvar (name pp : Name) (type : ExprId)
  | annotation (name : Annotation) (args : Array ExprId)
  | field_notation (field : Name) (idx : Nat) (args : Array ExprId)
  | typed_expr (args : Array ExprId)
  | «structure instance» (struct : Name) (catchall : Bool)
    (fields : Array Name) (args : Array ExprId)
  | projection_macro (I constr proj : Name) (idx : Nat) (params : Array Name)
    (type val : ExprId) (args : Array ExprId)
  | «sorry» (synthetic : Bool) (args : Array ExprId)
  | prenum (value : String)
  | nat_value (value : String)
  | string_macro (value : String)
  | expr_quote_macro (value : ExprId) (reflected : Bool)
  | choice (args : Array ExprId)
  | as_pattern (args : Array ExprId)
  | rec_fn (name : Name) (args : Array ExprId)
  | delayed_abstraction (value : Array Name) (args : Array ExprId)
  | no_equation : Unit → RawExpr
  | equation (ignore_if_unused : Bool) (args : Array ExprId)
  | equations (num_fns : Nat) (fn_names fn_actual_names : Array Name)
    (prev_errors is_private is_noncomputable is_meta is_lemma gen_code aux_lemmas : Bool)
    (args : Array ExprId)
  | equations_result (args : Array ExprId)
  | ac_app (args : Array ExprId)
  | perm_ac (args : Array ExprId)
  | cc_proof (args : Array ExprId)
  deriving FromJson

instance : FromJson RawExpr :=
  ⟨fun x => do
    try fromJson? x
    catch e => throw s!"at: {x}\n{e}"⟩

structure RawTacticInvocation where
  ast : AstId
  start : TacticStateId
  «end» : TacticStateId
  success : Bool
  deriving FromJson

structure RawHyp where
  name : Name
  pp : Name
  type : ExprId
  value : Option ExprId
  deriving FromJson

structure RawGoal where
  hyps : Array RawHyp
  target : ExprId

instance : FromJson RawGoal where
  fromJson? j := do pure ⟨← fromJson? (← j.getArrVal? 0), ← fromJson? (← j.getArrVal? 1)⟩

structure RawTacticState where
  decl : Name
  goals : Array RawGoal
  pp : Option String -- Note: we do not propagate this to AST3.TacticState
  deriving FromJson

deriving instance FromJson for AST3.Comment

structure RawAST3 where
  ast      : Array (Option RawNode3)
  file     : AstId
  level    : Array RawLevel
  expr     : Array (Option RawExpr)
  tactics  : Option (Array RawTacticInvocation)
  states   : Option (Array RawTacticState)
  comments : Array AST3.Comment
  deriving FromJson

section
open Lean (Level)
open Lean3 (EquationsHeader LambdaEquation Expr Proj)

variable (lvls : Array Level)
def buildLevel : RawLevel → Level
  | RawLevel.«0» => Lean.levelZero
  | RawLevel.suc l => Lean.mkLevelSucc lvls[l]!
  | RawLevel.max ls => Lean.mkLevelMax lvls[ls[0]!]! lvls[ls[1]!]!
  | RawLevel.imax ls => Lean.mkLevelIMax lvls[ls[0]!]! lvls[ls[1]!]!
  | RawLevel.param n => Lean.mkLevelParam n
  | RawLevel.mvar n => Lean.mkLevelMVar ⟨n⟩

variable (exprs : Array Expr)

def buildLevels (ls : Array RawLevel) : Array Level := Id.run do
  let mut out := #[]
  for l in ls do
    let l' := buildLevel out l
    out := out.push l'
  out

def Annotation.build : Annotation → Lean3.Annotation
  | no_univ => Lean3.Annotation.no_univ
  | do_failure_eq => Lean3.Annotation.do_failure_eq
  | infix_fn => Lean3.Annotation.infix_fn
  | begin_hole => Lean3.Annotation.begin_hole
  | end_hole => Lean3.Annotation.end_hole
  | anonymous_constructor => Lean3.Annotation.anonymous_constructor
  | «calc» => Lean3.Annotation.«calc»
  | no_info => Lean3.Annotation.no_info
  | frozen_name => Lean3.Annotation.frozen_name
  | «have» => Lean3.Annotation.«have»
  | «show» => Lean3.Annotation.«show»
  | «suffices» => Lean3.Annotation.«suffices»
  | checkpoint => Lean3.Annotation.checkpoint
  | «@» => Lean3.Annotation.«@»
  | «@@» => Lean3.Annotation.«@@»
  | as_atomic => Lean3.Annotation.as_atomic
  | as_is => Lean3.Annotation.as_is
  | antiquote => Lean3.Annotation.antiquote
  | expr_quote_pre => Lean3.Annotation.expr_quote_pre
  | comp_irrel => Lean3.Annotation.comp_irrel
  | inaccessible => Lean3.Annotation.inaccessible
  | «by» => Lean3.Annotation.«by»
  | pattern_hint => Lean3.Annotation.pattern_hint
  | th_proof => Lean3.Annotation.th_proof

def RawExpr.build : RawExpr → Expr
  | var i => Expr.var i
  | sort l => Expr.sort lvls[l]!
  | const c ls => Expr.const c $ ls.map fun l => lvls[l]!
  | app f a => Expr.app exprs[f]! exprs[a]!
  | lam n bi d b => Expr.lam n bi exprs[d]! exprs[b]!
  | Pi n bi d b => Expr.Pi n bi exprs[d]! exprs[b]!
  | «let» n t v b => Expr.let n exprs[t]! exprs[v]! exprs[b]!
  | mvar n pp t => Expr.mvar n pp exprs[t]!
  | «local» n pp bi t => Expr.local n pp bi exprs[t]!
  | annotation n args => Expr.annotation n.build exprs[args[0]!]!
  | field_notation field idx args => Expr.field exprs[args[0]!]! $
    if field.isAnonymous then Proj.ident field else Proj.nat idx
  | typed_expr args => Expr.typed_expr exprs[args[0]!]! exprs[args[1]!]!
  | «structure instance» s ca flds args => Expr.structinst s ca
    (flds.zipWith args fun n a => (n, exprs[a]!))
    (args[flds.size:].toArray.map fun a => exprs[a]!)
  | projection_macro I c p i ps ty val args =>
    Expr.proj I c p i ps exprs[ty]! exprs[val]! exprs[args[0]!]!
  | «sorry» s args => Expr.sorry s exprs[args[0]!]!
  | prenum n => Expr.prenum (Lean.Syntax.decodeNatLitVal? n).get!
  | nat_value n => Expr.nat (Lean.Syntax.decodeNatLitVal? n).get!
  | string_macro v => Expr.string v
  | expr_quote_macro v r => Expr.quote exprs[v]! r
  | choice args => Expr.choice $ args.map fun v => exprs[v]!
  | as_pattern args => Expr.as_pattern exprs[args[0]!]! exprs[args[1]!]!
  | rec_fn n args => Expr.rec_fn n exprs[args[0]!]!
  | delayed_abstraction ns args =>
    let args := args.map fun a => exprs[a]!
    Expr.delayed_abstraction args.back (ns.zip args.pop)
  | no_equation _ => Expr.no_equation
  | equation iu args => Expr.equation exprs[args[0]!]! exprs[args[1]!]! iu
  | equations n ns as _ p nc m l gc al args =>
    let args : Array Expr := args.map fun a => exprs[a]!
    let h := EquationsHeader.mk n ns as p nc m l gc al
    let (args, wf) :=
      if args.size ≥ 2 ∧ args.back.toLambdaEqn.isNone then (args.pop, some args.back)
      else (args, none)
    Expr.equations h (args.map fun e => e.toLambdaEqn.get!) wf
  | equations_result args => Expr.equations_result $ args.map fun a => exprs[a]!
  | ac_app args =>
    let args : Array Expr := args.map fun a => exprs[a]!
    Expr.ac_app args.pop args.back
  | perm_ac args => Expr.perm_ac exprs[args[0]!]! exprs[args[1]!]! exprs[args[2]!]! exprs[args[3]!]!
  | cc_proof args => Expr.cc_proof exprs[args[0]!]! exprs[args[1]!]!

def buildExprs (es : Array (Option RawExpr)) : Array Expr := Id.run do
  let mut out := #[]
  for e in es do
    let e' : Expr := match e with
    | some e => e.build lvls out
    | none => default
    out := out.push e'
  out

def RawHyp.build : RawHyp → AST3.Hyp
  | ⟨name, pp, ty, val⟩ => ⟨name, pp, exprs[ty]!, val.map fun e => exprs[e]!⟩

def RawGoal.build : RawGoal → AST3.Goal
  | ⟨hyps, target⟩ => ⟨hyps.map (·.build exprs), exprs[target]!⟩

def RawTacticState.build : RawTacticState → Name × Array AST3.Goal
  | ⟨declName, goals, _⟩ => (declName, goals.map (·.build exprs))

def RawTacticInvocation.build
  (states : Array (Name × Array AST3.Goal))
  (tacs : HashMap AstId (Spanned AST3.Tactic)) :
  RawTacticInvocation → AST3.TacticInvocation
  | ⟨ast, start, end_, success⟩ =>
    ⟨states[start]!.1, tacs.find? ast, states[start]!.2, states[end_]!.2, success⟩

end

def RawAST3.build :
    RawAST3 → (invocs :_:= true) → Except String (AST3 × Array AST3.TacticInvocation)
| ⟨ast, file, level, expr, tactics, states, comments⟩, invocs => do
  let level := buildLevels level
  let expr := buildExprs level expr
  M.run ast expr $ do
    let (ast, tacs) ← getAST comments file
    let invocs :=
      if invocs then
        let states := (states.getD #[]).map (fun (s : RawTacticState) => s.build expr)
        (tactics.getD #[]).map (·.build states tacs)
      else #[]
    pure (ast, invocs)

end Parse

def parseAST3 (filename : System.FilePath) (invocs :_:= true) :
  IO (AST3 × Array AST3.TacticInvocation) := do
  -- println! "Reading {filename}..."
  let s ← IO.FS.readFile filename
  -- println! "Parsing Json..."
  let json ← Json.parse s
  -- println! "Decoding RawAST3..."
  let rawAST3 ← fromJson? json (α := Parse.RawAST3)
  -- println! "Converting RawAST3 to AST3..."
  rawAST3.build invocs
