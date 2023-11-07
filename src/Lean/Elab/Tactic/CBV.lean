/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Leonardo de Moura
-/
import Lean

namespace Std.Tactic.CBV
open Lean Elab Tactic Meta
open Lean.Compiler.LCNF.ToLCNF (etaReduceImplicit mustEtaExpand)

inductive LitValue where
  | natVal (val : Nat)
  | strVal (val : String)
  -- TODO: add constructors for `Int`, `Float`, `UInt` ...
  deriving Inhabited, BEq, Hashable

inductive LetValueKind
  | erased -- the let value is erased
  | lit -- the value is `.lit _`
  | call -- the value is `(.const ..) ...`
  | callFVar -- the value is `(.fvar ..) ...`
  | proj -- the value is `.proj ..`
  | quotLift -- the value is `Quot.lift ...`
  deriving Inhabited, BEq

structure LetDecl where
  fvarId : FVarId
  binderName : Name
  type : Expr
  value : Expr
  kind : LetValueKind
  deriving Inhabited, BEq

structure Param where
  fvarId     : FVarId
  binderName : Name
  type       : Expr
  deriving Inhabited, BEq

def Param.toExpr (p : Param) : Expr :=
  .fvar p.fvarId

inductive AltCore (Code : Type) where
  | alt (ctorName : Name) (params : Array Param) (code : Code)
  | default (code : Code)
  deriving Inhabited

structure CasesCore (Code : Type) where
  typeName : Name
  resultType : Expr
  discr : FVarId
  alts : Array (AltCore Code)
  deriving Inhabited

inductive Code where
  | let (decl : LetDecl) (k : Code)
  -- | fun (decl : FunDeclCore Code) (k : Code)
  -- | cases (cases : CasesCore Code)
  -- | return (fvarId : FVarId)
  | erased (e : Expr)
  | unreach (type : Expr)
  deriving Inhabited

structure CodeLambda where
  params : Array Param
  body : Code
  deriving Inhabited

abbrev Alt := AltCore Code
abbrev Cases := CasesCore Code

inductive Arg where
  /-- The argument is erased, so it should be left unmodified -/
  | erased
  /-- The argument was not normalized, and `fvar` is defeq to the input
  iff it denotes a `letDecl` -/
  | fvar (fvarId : FVarId)
  deriving Inhabited

def Arg.toExpr (orig : Expr) : Arg → Expr
  | .erased => orig
  | .fvar fvarId => .fvar fvarId

namespace Compile

-- set_option trace.Meta.Match.match true in
-- set_option trace.Meta.Match.debug true in
-- noncomputable def foo : Nat → Option Nat → Nat
--   | 0, none => 0
--   | 0, some 4 => 0
--   | 0, n => 0
--   | 1, some 0 => 1
--   | 1, some (n+1) => 1
--   | 1, none => 1
--   | n+2, i => foo n i + foo (n+1) i
-- termination_by _ n _ => n

-- #print foo.match_1
-- set_option trace.Meta.Tactic.split true
-- example (h : n = 0) : foo 0 0 = 0 := by
--   -- split
--   -- rw [foo]
--   unfold foo
--   split


-- #eval show Command.CommandElabM _ from do
--   let some eqn ← Command.liftTermElabM <| getUnfoldEqnFor? ``foo | unreachable!
--   let some info ← getMatcherInfo? ``foo.match_1 | unreachable!
--   let matchEqns ← Command.liftTermElabM <| Match.getEquationsFor ``foo.match_1
--   -- for eqn in eqns do
--   Command.elabCommand (← `(#check $(mkIdent eqn):ident))
--   Command.elabCommand (← `(#print $(mkIdent matchEqns.splitterName):ident))
-- #eval show MetaM _ from do
--   let s := (Name.mkNum `_private.Std.Tactic.CBV 0) ++ `Std.Tactic.CBV.Compile.foo.match_1.splitter
--   let some info ← getMatcherInfo? ``foo.match_1 | unreachable!
--   let matchEqns ← Match.getEquationsFor ``foo.match_1
--   return matchEqns.splitterAltNumParams

inductive Element where
  | let (decl : LetDecl)
  | unreach (p : Param)
  | quotLift (e : Expr)
  deriving Inhabited

structure LCtx where
  params   : HashMap FVarId Param := {}
  letDecls : HashMap FVarId LetDecl := {}
  deriving Inhabited

def LCtx.addParam (lctx : LCtx) (param : Param) : LCtx :=
  { lctx with params := lctx.params.insert param.fvarId param }

def LCtx.addLetDecl (lctx : LCtx) (letDecl : LetDecl) : LCtx :=
  { lctx with letDecls := lctx.letDecls.insert letDecl.fvarId letDecl }

structure Context where
  baseName : Name

inductive Terminator where
  | unreach (e : Expr)
  | erased (e : Expr)
  | ret (e : FVarId)
  deriving Inhabited

structure State where
  lctx' : LocalContext := {}
  lctx : LCtx := {}
  nextIdx : Nat := 0
  /-- Cache from Lean regular expression to LCNF argument. -/
  cache : PHashMap Expr Arg := {}
  /-- `toLCNFType` cache -/
  typeCache : HashMap Expr Expr := {}
  /-- isTypeFormerType cache -/
  isTypeFormerTypeCache : HashMap Expr Bool := {}
  parents : Array (Array Param × Array Element) := #[]
  /-- LCNF sequence, we chain it to create a LCNF `Code` object. -/
  seq : Array Element := #[]
  terminator : Option Terminator := none

abbrev M := ReaderT Context <| StateRefT State MetaM

abbrev TermT := OptionT -- none means `terminator` was set

instance : MonadLift MetaM M where
  monadLift x := do withLCtx (← get).lctx' (← getLocalInstances) x

instance : MonadStateOf State M := inferInstance

def terminate (t : Terminator) : TermT M α :=
  show M _ from do
    modify fun s => { s with terminator := t }
    pure none

def toCode (ps : Array Param) (e : Expr) (result : Option Arg) : M Code := do
  let terminator ← match result with
    | none => pure (← get).terminator.get!
    | some .erased => return .erased e
    | some (.fvar e) => pure (.ret e)
  sorry

def toCodeLambda (ps : Array Param) (e : Expr) (result : Option Arg) : M CodeLambda :=
  return { params := ps, body := (← toCode ps e result) }

def inferLitValueType : LitValue → Expr
  | .natVal .. => mkConst ``Nat
  | .strVal .. => mkConst ``String

def litToValue (lit : Literal) : LitValue :=
  match lit with
  | .natVal val => .natVal val
  | .strVal val => .strVal val

def withNewScope (x : M α) : M α := do
  let saved ← get
  -- typeCache and isTypeFormerTypeCache are not backtrackable
  let saved := { saved with typeCache := {}, isTypeFormerTypeCache := {} }
  modify fun s => { s with seq := #[] }
  try
    x
  finally
    modify fun { typeCache, isTypeFormerTypeCache, .. } =>
      { saved with typeCache, isTypeFormerTypeCache }

@[inline] def modifyLCtx (f : LCtx → LCtx) : M Unit := do
   modify fun s => { s with lctx := f s.lctx }

/-- Create a new local declaration using a Lean regular type. -/
def mkParam (binderName : Name) (type : Expr) : M Param := do
  let fvarId ← mkFreshFVarId
  let param := { fvarId, binderName, type }
  modify fun s => { s with
    lctx := s.lctx.addParam param
    lctx' := s.lctx'.mkLocalDecl param.fvarId binderName type .default
  }
  return param

def mkLetDecl (binderName : Name) (type : Expr) (value : Expr) (kind : LetValueKind) : M LetDecl := do
  let fvarId ← mkFreshFVarId
  let letDecl := { fvarId, binderName, type, value, kind }
  modify fun s => { s with
    lctx := s.lctx.addLetDecl letDecl
    lctx' := s.lctx'.mkLetDecl letDecl.fvarId binderName type value false
    seq := s.seq.push <| .let letDecl
  }
  return letDecl

/-- Add LCNF element to the current sequence -/
def pushElement (elem : Element) : M Unit := do
  modify fun s => { s with seq := s.seq.push elem }

def mkAuxLetDecl (e : Expr) (kind : LetValueKind) : M FVarId := do
  match e with
  | .fvar fvarId => return fvarId
  | _ =>
    let letDecl ← mkLetDecl (← mkFreshId) (← inferType e) e kind
    pushElement (.let letDecl)
    return letDecl.fvarId

def letValueToArg (kind : LetValueKind) (e : Expr) : TermT M Arg := .fvar <$> mkAuxLetDecl e kind

/--
Eta-expand with `n` lambdas.
-/
def etaExpandN (e : Expr) (n : Nat) : M Expr := do
  if n == 0 then
    return e
  else
    Meta.forallBoundedTelescope (← Meta.inferType e) n fun xs _ =>
      Meta.mkLambdaFVars xs (mkAppN e xs)

def builtinTypes : List Name := [
  -- ``String,
  -- ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize,
  -- ``Float,
  -- ``Thunk, ``Task,
  -- ``Array, ``ByteArray, ``FloatArray,
  -- ``Nat, ``Int
]

def isBultinType (declName : Name) : Bool :=
  builtinTypes.contains declName

def lambdaTelescope (e : Expr) (bound : Option Nat := none) (etaExpand := false) :
    M (Array Param × Expr) :=
  go e #[] #[] bound
where
  go (e : Expr) (xs : Array Expr) (ps : Array Param) (bound : Option Nat) := do
    if bound == some 0 then
      return (ps, e.instantiateRev xs)
    else if let .lam binderName type body _ := e then
      let type := type.instantiateRev xs
      let p ← mkParam binderName type
      go body (xs.push p.toExpr) (ps.push p) (bound.map (· - 1))
    else
      let e := e.instantiateRev xs
      if etaExpand then
        eta e (← Meta.inferType e) #[] ps bound
      else
        return (ps, e)

  eta (e ty : Expr) (xs : Array Expr) (ps : Array Param) (bound : Option Nat) := do
    if bound == some 0 then
      return (ps, mkAppN e xs)
    else if let .forallE binderName type body _ := ty then -- FIXME: use whnf
      let type := type.instantiateRev xs
      let p ← mkParam binderName type
      eta e body (xs.push p.toExpr) (ps.push p) (bound.map (· - 1))
    else
      return (ps, mkAppN e xs)

partial def compile (baseName : Name) (e : Expr) : MetaM CodeLambda :=
  (visitTop e { baseName }).run' {}
where
  visitTop (e : Expr) : M CodeLambda := do
    let (ps, e) ← lambdaTelescope e (etaExpand := true)
    let lctx := (← get).lctx'
    withTheReader Meta.Context (fun ctx => { ctx with lctx }) do
      toCodeLambda ps e (← visit e)

  visitCore (e : Expr) : TermT M Arg := do
    if let some arg := (← get).cache.find? e then
      return arg
    let r : Arg ← match e with
      | .app ..
      | .const ..
      | .letE ..     => visitLambdaApp #[] e []
      | .lam ..      => visitLambda e
      | .proj s i e  => visitProj s i e
      | .mdata _ e   => visitCore e
      | .lit lit     => visitLit lit
      | .fvar fvarId => pure (.fvar fvarId)
      | .forallE .. | .mvar .. | .bvar .. | .sort ..  => unreachable!
    modify fun s => { s with cache := s.cache.insert e r }
    return r

  visit (e : Expr) : TermT M Arg := do
    let type ← Meta.inferType e
    if ← Meta.isProp type then
      return .erased
    if ← isTypeFormerType type then
      return .erased
    visitCore e

  asFVar (e : Arg) (k : FVarId → TermT M Arg) : TermT M Arg := do
    match e with
    | .erased => return .erased
    | .fvar e => k e

  visitAsExpr (e : Expr) : TermT M Expr := do
    match (← visit e) with
    | .erased => return e
    | .fvar e => return .fvar e

  visitLit (lit : Literal) : TermT M Arg :=
    letValueToArg .lit (.lit lit)

  /-- Giving `f` a constant `.const declName us`, convert `args` into `args'`, and return `.const declName us args'` -/
  visitAppDefaultConst (f : Expr) (args : Array Expr) : TermT M Arg := do
    let .const declName us := f | unreachable!
    let args ← args.mapM visitAsExpr
    letValueToArg .call <| mkAppN (.const declName us) args

  /-- Eta expand if under applied, otherwise apply k -/
  etaIfUnderApplied (e : Expr) (args : Array Expr) (arity : Nat) (k : TermT M Arg) : TermT M Arg := do
    let numArgs := e.getAppNumArgs
    if numArgs < arity then
      visit (← etaExpandN (mkAppN e args) (arity - numArgs))
    else
      k

  /--
  If `args.size == arity`, then just return `app`.
  Otherwise return
  ```
  let k := app
  k args[arity:]
  ```
  -/
  mkOverApplication (app : Arg) (args : Array Expr) (arity : Nat) : TermT M Arg := do
    if args.size == arity then
      return app
    else
      asFVar app fun f => do
        let mut e : Expr := .fvar f
        for i in [arity : args.size] do
          e := .app e (← visitAsExpr args[i]!)
        letValueToArg .callFVar e

  -- /--
  -- Visit a `matcher`/`casesOn` alternative.
  -- -/
  -- visitAlt (ctorName : Name) (numParams : Nat) (e : Expr) : M (Expr × Alt) := do
  --   withNewScope do
  --     let mut (ps, e) ← lambdaTelescope e (bound := numParams) (etaExpand := true)
  --     if ps.size != numParams then throwError "bad type {e}"
  --     /-
  --     Insert the free variable ids of fields that are type formers into `toAny`.
  --     Recall that we do not want to have "data" occurring in types.
  --     -/
  --     ps ← ps.mapM fun p => do
  --       let type ← inferType p.toExpr
  --       if (← isTypeFormerType type) then
  --         modify fun s => { s with toAny := s.toAny.insert p.fvarId }
  --       /-
  --       Recall that we may have dependent fields. Example:
  --       ```
  --       | ctor (α : Type u) (as : List α) => ...
  --       ```
  --       and we must use `applyToAny` to make sure the field `α` (which is data) does
  --       not occur in the type of `as : List α`.
  --       -/
  --       p.update (← applyToAny p.type)
  --     let c ← toCode (← visit e)
  --     let altType ← c.inferType
  --     return (altType, .alt ctorName ps c)

  -- visitCases (casesInfo : CasesInfo) (e : Expr) : TermT M Arg :=
  --   etaIfUnderApplied f args casesInfo.arity do
  --     let args := e.getAppArgs
  --     let mut resultType ← toLCNFType (← liftMetaM do Meta.inferType (mkAppN e.getAppFn args[:casesInfo.arity]))
  --     if casesInfo.numAlts == 0 then
  --       /- `casesOn` of an empty type. -/
  --       mkUnreachable resultType
  --     else
  --       let mut alts := #[]
  --       let typeName := casesInfo.declName.getPrefix
  --       let discr ← visit args[casesInfo.discrPos]!
  --       let .inductInfo indVal ← getConstInfo typeName | unreachable!
  --       match discr with
  --       | .erased =>
  --         /-
  --         This can happen for inductive predicates that can eliminate into type (e.g., `And`, `Iff`).
  --         TODO: add support for them. Right now, we have hard-coded support for the ones defined at `Init`.
  --         -/
  --         throwError "unsupported `{casesInfo.declName}` application during code generation"
  --       | .fvar discrFVarId =>
  --         for i in casesInfo.altsRange, numParams in casesInfo.altNumParams, ctorName in indVal.ctors do
  --           let (altType, alt) ← visitAlt ctorName numParams args[i]!
  --           resultType := joinTypes altType resultType
  --           alts := alts.push alt
  --         let cases : Cases := { typeName, discr := discrFVarId, resultType, alts }
  --         let auxDecl ← mkAuxParam resultType
  --         pushElement (.cases auxDecl cases)
  --         let result := .fvar auxDecl.fvarId
  --         mkOverApplication result args casesInfo.arity

  visitCtor (arity : Nat) (f : Expr) (args : Array Expr) : TermT M Arg :=
    etaIfUnderApplied f args arity do
      visitAppDefaultConst f args

  visitQuotLift (f : Expr) (args : Array Expr) : TermT M Arg := do
    let arity := 6
    etaIfUnderApplied f args arity do
      let e := mkAppRange f 0 arity args
      let letDecl ← mkLetDecl (← mkFreshId) (← inferType e) e .quotLift
      pushElement (.let letDecl)
      mkOverApplication (.fvar letDecl.fvarId) args arity
      -- let α := args[0]!
      -- let r := args[1]!
      -- let f' ← visit args[3]!
      -- let qOrig := args[5]!
      -- let q ← visit qOrig
      -- let .const _ [u, v] := f | unreachable!
      -- let code ← liftM <| withNewScope do
      --   let (ps, body) ← lambdaTelescope args[3]! (bound := some 1) (etaExpand := true)
      --   assert! ps.size == 1
      --   toCodeLambda ps body (← visit body)
      -- if let .unreach e := code.body then
      --   let f ← mkLambdaFVars (code.params.map (·.toExpr)) e
      --   terminate <| .unreach <| mkApp4 (.const ``Quot.false_of_false [u]) α r (q.toExpr qOrig) f
      -- let invq ← mkAuxLetDecl (.const ``Quot.lift [u] #[.type α, .type r, q])
      -- match f' with
      -- | .erased => return .erased
      -- | .fvar fvarId => mkOverApplication (← letValueToArg <| .fvar fvarId #[.fvar invq]) args arity

  visitEqRec (f : Expr) (args : Array Expr) : TermT M Arg :=
    let arity := 6
    etaIfUnderApplied f args arity do
      let args := e.getAppArgs
      let minor := if e.isAppOf ``Eq.rec || e.isAppOf ``Eq.ndrec then args[3]! else args[5]!
      let minor ← visit minor
      mkOverApplication minor args arity

  visitFalseRec (f : Expr) (args : Array Expr) : TermT M Arg :=
    etaIfUnderApplied f args (arity := 2) do
      terminate <| .unreach e.appArg!

  visitEmptyRec (f : Expr) (args : Array Expr) : TermT M Arg :=
    etaIfUnderApplied f args (arity := 2) do
      let motive := .lam `t (.const ``Empty []) (.const ``False []) .default
      terminate <| .unreach (mkApp2 (.const ``Empty.rec [.zero]) motive e.appArg!)

  visitAndIffRecCore (f : Expr) (args : Array Expr) (left right : Name) (minorPos majorPos : Nat) : TermT M Arg :=
    let arity := 5
    etaIfUnderApplied f args arity do
      let a := args[0]!
      let b := args[1]!
      let major := args[majorPos]!
      let ha := mkApp3 (.const left []) a b major
      let hb := mkApp3 (.const right []) a b major
      let minor := args[minorPos]!.beta #[ha, hb]
      visit (mkAppN minor args[arity:])

  -- visitNoConfusion (f : Expr) (args : Array Expr) : TermT M Arg := do
  --   let .const declName _ := e.getAppFn | unreachable!
  --   let typeName := declName.getPrefix
  --   let .inductInfo inductVal ← getConstInfo typeName | unreachable!
  --   let arity := inductVal.numParams + inductVal.numIndices + 1 /- motive -/ + 2 /- lhs/rhs-/ + 1 /- equality -/
  --   etaIfUnderApplied f args arity do
  --     let args := e.getAppArgs
  --     let lhs ← liftMetaM do Meta.whnf args[inductVal.numParams + inductVal.numIndices + 1]!
  --     let rhs ← liftMetaM do Meta.whnf args[inductVal.numParams + inductVal.numIndices + 2]!
  --     let lhs := lhs.toCtorIfLit
  --     let rhs := rhs.toCtorIfLit
  --     match lhs.isConstructorApp? (← getEnv), rhs.isConstructorApp? (← getEnv) with
  --     | some lhsCtorVal, some rhsCtorVal =>
  --       if lhsCtorVal.name == rhsCtorVal.name then
  --         etaIfUnderApplied f args (arity+1) do
  --           let major := args[arity]!
  --           let major ← expandNoConfusionMajor major lhsCtorVal.numFields
  --           let major := mkAppN major args[arity+1:]
  --           visit major
  --       else
  --         let type ← toLCNFType (← Meta.inferType e)
  --         mkUnreachable type
  --     | _, _ =>
  --       throwError "code generator failed, unsupported occurrence of `{declName}`"

  -- expandNoConfusionMajor (major : Expr) (numFields : Nat) : M Expr := do
  --   match numFields with
  --   | 0 => return major
  --   | n+1 =>
  --     if let .lam _ d b _ := major then
  --       let proof := mkLcProof d
  --       expandNoConfusionMajor (b.instantiate1 proof) n
  --     else
  --       expandNoConfusionMajor (← etaExpandN major (n+1)) (n+1)

  visitProjFn (projInfo : ProjectionFunctionInfo) (f : Expr) (args : Array Expr) : TermT M Arg := do
    let typeName := projInfo.ctorName.getPrefix
    if isBultinType typeName then
      etaIfUnderApplied f args (arity := projInfo.numParams + 1) do
        visitAppDefaultConst e.getAppFn e.getAppArgs
    else
      let .const declName us := e.getAppFn | unreachable!
      let info ← getConstInfo declName
      let f ← Core.instantiateValueLevelParams info us
      visit (f.beta e.getAppArgs)

  visitConstApp (f : Expr) (args : Array Expr) : TermT M Arg := do
    let declName := f.constName!
    if declName == ``Quot.lift then
      visitQuotLift f args
    else if declName == ``Quot.mk then
      visitCtor 3 f args
    -- else if declName == ``Eq.casesOn || declName == ``Eq.rec || declName == ``Eq.ndrec then
    --   visitEqRec f args
    else if declName == ``And.rec || declName == ``Iff.rec then
      visitAndIffRecCore f args ``And.left ``And.right (minorPos := 3) (majorPos := 4)
    else if declName == ``And.casesOn || declName == ``Iff.casesOn then
      visitAndIffRecCore f args ``And.left ``And.right (minorPos := 4) (majorPos := 3)
    else if declName == ``Iff.rec then
      visitAndIffRecCore f args ``Iff.mp ``Iff.mpr (minorPos := 3) (majorPos := 4)
    else if declName == ``Iff.casesOn then
      visitAndIffRecCore f args ``Iff.mp ``Iff.mpr (minorPos := 4) (majorPos := 3)
    else if declName == ``False.rec || declName == ``False.casesOn then
      visitFalseRec f args
    else if declName == ``Empty.rec || declName == ``Empty.casesOn then
      visitEmptyRec f args
    -- else if let some casesInfo ← Compiler.LCNF.getCasesInfo? declName then
    --   visitCases casesInfo f args
    else if let some arity ← Compiler.LCNF.getCtorArity? declName then
      visitCtor arity f args
    -- else if isNoConfusion (← getEnv) declName then
    --   visitNoConfusion f args
    else if let some projInfo ← getProjectionFnInfo? declName then
      visitProjFn projInfo f args
    else
      visitAppDefaultConst f args

  visitLambdaApp (xs : Array Expr) : Expr → List Expr → TermT M Arg
    | .app f a, args => visitLambdaApp xs f (a :: args)
    | .lam _ _ body .., value :: args
    | .letE _ _ value body _, args => do
      let value := value.instantiateRev xs
      visitLambdaApp (xs.push (← visitAsExpr value)) body args
    | .mdata _ e, args => visitLambdaApp xs e args
    | e, [] => visit (e.instantiateRev xs)
    | e, args => do
      let e := e.instantiateRev xs
      if let .const declName _ := e then
        visitConstApp e (args.toArray.map (·.instantiateRev xs))
      else if let [] := args then
        visit e
      else
        asFVar (← visit e) fun fvarId => do
          let args ← args.toArray.mapM fun a => visitAsExpr <| a.instantiateRev xs
          letValueToArg .callFVar <| mkAppN (.fvar fvarId) args

  visitLambda (e : Expr) : TermT M Arg := do
    let b := etaReduceImplicit e
    if !b.isLambda && !mustEtaExpand (← getEnv) b then
      visit b
    else
      let defName ← mkAuxName ((← read).baseName ++ `_cbv) (← get).nextIdx
      modify fun s => { s with nextIdx := s.nextIdx + 1 }
      let e' ← mkAuxDefinition defName (← inferType e).headBeta e (compile := false)
      visit e'

  visitProj (s : Name) (i : Nat) (e : Expr) : TermT M Arg := do
    asFVar (← visit e) fun fvarId =>
      letValueToArg .proj <| .proj s i (.fvar fvarId)

end Compile

def cbvCore (e : Expr) : MetaM Simp.Result := do
  sorry

elab "cbv" : conv => withMainContext do
  Conv.applySimpResult (← cbvCore (← instantiateMVars (← Conv.getLhs)))
