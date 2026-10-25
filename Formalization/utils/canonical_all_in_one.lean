import Mathlib
import Lean

open Lean Elab Term Meta Command Tactic

namespace Canonical

/-
  ============================================================
  1) Switches
  ============================================================
-/

inductive NumberMode where
  | basic
  | arith
  | all
deriving Repr, BEq

inductive SetMode where
  | extensional
  | all
deriving Repr, BEq

inductive QuantMode where
  | disallow
  | allow
deriving Repr, BEq

structure Switches where
  numbers : NumberMode := .all
  set     : SetMode    := .all
  existsQ : QuantMode  := .allow
  forallQ : QuantMode  := .allow
deriving Repr

structure StructuralOptions where
  allowQuantifier : Bool := true
deriving Repr

/-
  ============================================================
  2) Full allowed constants (when all switches are default).
  ============================================================
-/

def allowedOpConsts : Std.HashSet Name :=
  Std.HashSet.ofList
    [
      ``Eq, ``And, ``Or, ``Iff, ``Not, ``Exists, ``True, ``False, ``ite,
      ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge,

      ``Bool.true, ``Bool.false,

      ``OfNat, ``OfNat.ofNat,
      ``OfScientific, ``OfScientific.ofScientific, ``NNRatCast.toOfScientific,
      ``Nat.cast, ``Int.cast, ``Rat.cast, ``Rat.instNatCast,
      ``Nat.zero, ``Nat.succ, ``Nat.pred,

      ``EmptyCollection.emptyCollection, ``Singleton.singleton, ``Set.singleton,
      ``Insert.insert, ``Set.insert, ``setOf, ``Set.Mem, ``Set.univ,
      ``Union.union, ``Inter.inter,
      ``Set.Ici, ``Set.Ioi, ``Set.Iic, ``Set.Iio, ``Set.Icc, ``Set.Ioo, ``Set.Ioc, ``Set.Ico,

      ``Finset.card, ``Finset.sum, ``Finset.product, ``Finset.range, ``Finset.prod, ``Finset.Subtype.fintype, ``Finset.add,
      ``Finset.Ici, ``Finset.Ioi, ``Finset.Iic, ``Finset.Iio, ``Finset.Icc, ``Finset.Ioo, ``Finset.Ioc, ``Finset.Ico,

      ``Prod.mk, ``Prod.fst, ``Prod.snd, ``Subtype.mk, ``Subtype.val,

      ``HAdd.hAdd, ``HMul.hMul, ``HSub.hSub, ``HDiv.hDiv, ``HPow.hPow, ``Neg.neg, ``HMod.hMod,
      ``abs, ``Real.sqrt, ``Nat.sqrt, ``Int.sqrt, ``Rat.sqrt,

      ``Nat.add, ``Nat.mul, ``Nat.sub, ``Nat.pow, ``Nat.factorial, ``Nat.choose, ``Nat.fib,
      ``Nat.gcd, ``Nat.lcm, ``Dvd.dvd, ``Nat.ModEq, ``Int.ModEq,
      ``Nat.floor, ``Int.floor, ``Nat.ceil, ``Int.ceil, ``Nat.mod, ``Even, ``Odd, ``Int.ediv, ``Int.emod,
      ``Prime, ``Nat.Prime,

      ``Polynomial.X, ``Polynomial.C, ``Polynomial.eval, ``Polynomial.map,
      ``Polynomial.degree, ``Polynomial.natDegree, ``Polynomial.mul', ``Polynomial.add',

      ``Real.pi, ``Real.sin, ``Real.cos, ``Real.tan,
      ``Real.sinh, ``Real.cosh, ``Real.tanh,
      ``Real.exp, ``Real.log,

      ``Complex.mk, ``Complex.ofReal, ``Complex.I
    ]

/-
  ============================================================
  3) Numbers restriction (unchanged)
  ============================================================
-/

def numberRelatedConsts : Std.HashSet Name :=
  Std.HashSet.ofList
    [
      ``OfNat, ``OfNat.ofNat,
      ``OfScientific, ``OfScientific.ofScientific, ``NNRatCast.toOfScientific,
      ``Nat.cast, ``Int.cast, ``Rat.cast, ``Rat.instNatCast,
      ``Nat.zero, ``Nat.succ, ``Nat.pred,

      ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HPow.hPow, ``Neg.neg, ``HMod.hMod,
      ``abs, ``Real.sqrt, ``Nat.sqrt, ``Int.sqrt, ``Rat.sqrt,

      ``Nat.add, ``Nat.mul, ``Nat.sub, ``Nat.pow, ``Nat.factorial, ``Nat.choose, ``Nat.fib,
      ``Nat.gcd, ``Nat.lcm, ``Nat.mod,
      ``Nat.floor, ``Int.floor, ``Nat.ceil, ``Int.ceil, ``Int.ediv, ``Int.emod,
      ``Even, ``Odd, ``Dvd.dvd, ``Nat.ModEq, ``Int.ModEq,
      ``Prime, ``Nat.Prime,

      ``Real.pi, ``Real.exp, ``Real.log,
      ``Real.sin, ``Real.cos, ``Real.tan,
      ``Real.sinh, ``Real.cosh, ``Real.tanh,
      ``Real.arctan, ``Real.arccos, ``Real.arcsin,

      ``Complex.mk, ``Complex.ofReal, ``Complex.I
    ]

def basicNumberWhitelist : Std.HashSet Name :=
  Std.HashSet.ofList
    [
      ``OfNat, ``OfNat.ofNat,
      ``OfScientific, ``OfScientific.ofScientific, ``NNRatCast.toOfScientific,
      ``Nat.cast, ``Int.cast, ``Rat.cast, ``Rat.instNatCast,
      ``Nat.zero, ``Nat.succ, ``Nat.pred,
      ``Bool.true, ``Bool.false
    ]

def arithNumberWhitelist : Std.HashSet Name :=
  Std.HashSet.ofList
    [
      ``OfNat, ``OfNat.ofNat,
      ``OfScientific, ``OfScientific.ofScientific, ``NNRatCast.toOfScientific,
      ``Nat.cast, ``Int.cast, ``Rat.cast, ``Rat.instNatCast,
      ``Nat.zero, ``Nat.succ, ``Nat.pred,
      ``Bool.true, ``Bool.false,

      ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HPow.hPow, ``Neg.neg,

      ``Real.pi, ``Real.exp, ``Real.log
    ]

private def eraseMany (s : Std.HashSet Name) (xs : List Name) : Std.HashSet Name :=
  xs.foldl (fun acc n => acc.erase n) s

def restrictNumbers (allowed : Std.HashSet Name) (whitelist : Std.HashSet Name) : Std.HashSet Name :=
  let forbidden := (numberRelatedConsts.toList).filter (fun n => ¬ whitelist.contains n)
  eraseMany allowed forbidden

/-
  ============================================================
  4) Other switches
  ============================================================
-/

def setBuilderConsts : List Name := [``setOf]
def existsConst : Name := ``Exists

def allowedFromSwitches (sw : Switches) : Std.HashSet Name :=
  let s0 := allowedOpConsts

  let s1 :=
    match sw.numbers with
    | .all   => s0
    | .basic => restrictNumbers s0 basicNumberWhitelist
    | .arith => restrictNumbers s0 arithNumberWhitelist

  let s2 :=
    match sw.set with
    | .all         => s1
    | .extensional => eraseMany s1 setBuilderConsts

  let s3 :=
    match sw.existsQ with
    | .allow    => s2
    | .disallow => s2.erase existsConst

  s3

/-
  ============================================================
  5) Canonical checker core
  ============================================================
-/

private def isNonPropSort : Level → Bool
  | .zero => false
  | _     => true

partial def isTypeFormerTy : Expr → Bool
  | .sort u          => isNonPropSort u
  | .forallE _ _ b _ => isTypeFormerTy b
  | _                => false

def isTypeFormerConst (n : Name) (us : List Level) : MetaM Bool := do
  let ty ← inferType (Expr.const n us) >>= whnf
  return isTypeFormerTy ty

def isTypeArg (aTy : Expr) : Bool :=
  match aTy with
  | .sort u => isNonPropSort u
  | _       => false

def isMatchLikeConst (n : Name) : Bool :=
  let s := n.toString
  s.containsSubstr "match_" || s.containsSubstr ".match_" ||
  s.endsWith ".casesOn" || s.endsWith ".rec" || s.endsWith ".recOn"

def isInstanceConstName (n : Name) : Bool :=
  n.toString.startsWith "inst" || n.toString.containsSubstr ".inst"

/-- Strong “private” filter: ignore anything whose printed name begins with `_private` (or contains `._private`). -/
private def isPrivateName (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "_private" || s.containsSubstr "._private"

/-- Extra temp-ish heuristics (optional). -/
private def isTempLikeName (n : Name) : Bool :=
  let s := n.toString
  s.containsSubstr ".tmp" || s.containsSubstr "tmp_" || s.containsSubstr "._match"

/-- Common proof/search artifacts that are usually noise for constant reporting. -/
private def proofNoiseConsts : Std.HashSet Name :=
  Std.HashSet.ofList
    [
      ``Eq.refl, ``rfl,
      ``Decidable.decide, ``of_decide_eq_true,
      ``Eq.rec, ``Eq.recOn, ``Eq.ndrec, ``Eq.ndrecOn, ``Eq.mp, ``Eq.mpr,
      ``DFunLike.coe
    ]

/-- Ignore proof-ish constants from reports to focus on semantic operators. -/
private def isProofNoiseConst (n : Name) : Bool :=
  proofNoiseConsts.contains n ||
  n.toString.endsWith ".decEq" || n.toString.containsSubstr ".dec"

/-- NEVER print constants whose names are implementation/proof noise. -/
private def ignoreConstNameForReport (n : Name) : Bool :=
  isPrivateName n || isTempLikeName n || isInstanceConstName n || isMatchLikeConst n || isProofNoiseConst n

private def returnsClass (ty : Expr) : MetaM Bool := do
  forallTelescopeReducing ty fun _ body => do
    let body ← whnf body
    return (← isClass? body) |>.isSome

/--
Named Mathlib instances such as `WithBot.preorder` and `Real.semiring` do not
always contain `inst` in their names. They are support constants introduced by
elaboration/typeclass search, so omit constants whose result type is a class.
-/
private def ignoreConstForReport (n : Name) (us : List Level) : MetaM Bool := do
  if ignoreConstNameForReport n then
    return true
  let cTy ← inferType (Expr.const n us) >>= whnf
  if isTypeArg cTy then return true
  if isTypeFormerTy cTy then return true
  returnsClass cTy

private def projConstName? (typeName : Name) (idx : Nat) : MetaM (Option Name) := do
  let env ← getEnv
  match Lean.getStructureInfo? env typeName with
  | some info => pure (info.fieldNames[idx]?)
  | none      => pure none

partial def getAppSpine (e : Expr) : Expr × Array Expr :=
  match e with
  | .app f a =>
      let (h, args) := getAppSpine f
      (h, args.push a)
  | _ => (e, #[])

def isNumeralViaOfNat (e : Expr) : Bool :=
  let (h, args) := getAppSpine e
  match h, args.size with
  | Expr.const ``OfNat.ofNat _, 3 =>
      match args[1]? with
      | some (Expr.lit (Literal.natVal _)) => true
      | _ => false
  | _, _ => false

def explicitArgsOfApp (head : Expr) (args : Array Expr) : MetaM (Array Expr) := do
  let finfo ← getFunInfoNArgs head args.size
  let mut kept := #[]
  for i in [:args.size] do
    let a := args[i]!
    let bi := finfo.paramInfo[i]!.binderInfo
    if bi == .implicit || bi == .instImplicit || bi == .strictImplicit then
      continue
    let aTy ← inferType a >>= whnf
    if (← isClass? aTy) |>.isSome then
      continue
    kept := kept.push a
  return kept

private def isPropLike (e : Expr) : MetaM Bool := do
  let t ← inferType e >>= whnf
  match t with
  | .sort .zero => pure true
  | _           => pure false

private def isFunctionTypeExpr (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e >>= whnf
  match e with
  | .forallE .. => return true
  | _           => return false

private def isRecursionLikeConstName (n : Name) : Bool :=
  let s := n.toString
  s.endsWith ".rec" || s.endsWith ".recOn"

partial def isStructurallyCanonicalM (opts : StructuralOptions) (e : Expr) : MetaM Bool := do
  let rec go (inQuantifier : Bool) (e : Expr) : MetaM Bool := do
    let e ← instantiateMVars e
    match e with
    | .const n _ =>
        if isRecursionLikeConstName n then
          return false
        return true
    | .app _ _ =>
        let (head, args0) := getAppSpine e
        let underExists :=
          match head with
          | .const n _ => n == ``Exists
          | _          => false
        if underExists && !opts.allowQuantifier then
          return false
        if !(← go inQuantifier head) then
          return false
        let realArgs ← explicitArgsOfApp head args0
        for a in realArgs do
          if !(← go (inQuantifier || underExists) a) then
            return false
        return true
    | .lam name ty body binderInfo =>
        let ty ← instantiateMVars ty
        if inQuantifier && (← isFunctionTypeExpr ty) then
          return false
        if !(← go inQuantifier ty) then
          return false
        withLocalDecl name binderInfo ty fun x =>
          go inQuantifier (body.instantiate1 x)
    | .forallE name ty body binderInfo =>
        let propLike ← isPropLike e
        let implicationLike ←
          if propLike then
            isPropLike ty
          else
            pure false
        let quantifierLike := propLike && !implicationLike
        let nextInQuantifier := inQuantifier || quantifierLike
        if quantifierLike then
          if !opts.allowQuantifier then
            return false
          if (← isFunctionTypeExpr ty) then
            return false
        if !(← go nextInQuantifier ty) then
          return false
        withLocalDecl name binderInfo ty fun x =>
          go nextInQuantifier (body.instantiate1 x)
    | .letE name ty v body _ =>
        if !(← go inQuantifier ty) then
          return false
        if !(← go inQuantifier v) then
          return false
        withLetDecl name ty v fun x =>
          go inQuantifier (body.instantiate1 x)
    | .mdata _ b =>
        go inQuantifier b
    | .proj _ _ b =>
        go inQuantifier b
    | _ =>
        return true
  go false e

/-- Collect only relevant constants (and **hard-drop** `_private*` from reporting). -/
partial def collectRelevantConsts (e : Expr) : MetaM NameSet := do
  let rec go (e : Expr) (acc : NameSet) : MetaM NameSet := do
    let e ← instantiateMVars e
    match e with
    | .const n us =>
        if (← ignoreConstForReport n us) then
          return acc
        else
          return acc.insert n
    | .app _ _ =>
        let (head, args) := getAppSpine e
        let acc ← go head acc
        let realArgs ← explicitArgsOfApp head args
        realArgs.foldlM (fun acc arg => go arg acc) acc
    | .lam name t body binderInfo =>
        let acc ← go t acc
        withLocalDecl name binderInfo t fun x =>
          go (body.instantiate1 x) acc
    | .forallE name t body binderInfo =>
        let acc ← go t acc
        withLocalDecl name binderInfo t fun x =>
          go (body.instantiate1 x) acc
    | .letE name t v body _ =>
        let acc ← go t acc
        let acc ← go v acc
        withLetDecl name t v fun x =>
          go (body.instantiate1 x) acc
    | .mdata _ b =>
        go b acc
    | .proj typeName idx b =>
        let acc ← go b acc
        match (← projConstName? typeName idx) with
        | some n =>
            if ignoreConstNameForReport n then
              return acc
            else
              return acc.insert n
        | none => return acc
    | _ =>
        return acc
  go e NameSet.empty

partial def isCanonicalExprMWithSwitches (allowed : Std.HashSet Name) (sw : Switches) (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  match e with
  | .bvar _ => return true
  | .fvar _ => return true
  | .lit _  => return true
  | .mvar _ => return false
  | .sort _ => return true
  | .mdata _ e => isCanonicalExprMWithSwitches allowed sw e
  | .proj typeName idx s => do
    let baseOk ← isCanonicalExprMWithSwitches allowed sw s
    if !baseOk then
      return false
    match (← projConstName? typeName idx) with
    | some n =>
        if isInstanceConstName n || isMatchLikeConst n then
          return true
        return allowed.contains n
    | none => return true

  | .lam name ty body binderInfo => do
    let ty ← instantiateMVars ty
    let tyOk ←
      match ty with
      | .mvar _ => pure true
      | _       => isCanonicalExprMWithSwitches allowed sw ty
    if !tyOk then
      return false
    withLocalDecl name binderInfo ty fun x =>
      isCanonicalExprMWithSwitches allowed sw (body.instantiate1 x)

  | .forallE name ty body binderInfo => do
    if sw.forallQ == .disallow then
      if (← isPropLike e) then
        return false
    let ty ← instantiateMVars ty
    let tyOk ←
      match ty with
      | .mvar _ => pure true
      | _       => isCanonicalExprMWithSwitches allowed sw ty
    if !tyOk then
      return false
    withLocalDecl name binderInfo ty fun x =>
      isCanonicalExprMWithSwitches allowed sw (body.instantiate1 x)

  | .letE name ty v body _ => do
    let tyOk ← isCanonicalExprMWithSwitches allowed sw ty
    let vOk  ← isCanonicalExprMWithSwitches allowed sw v
    if !(tyOk && vOk) then
      return false
    withLetDecl name ty v fun x =>
      isCanonicalExprMWithSwitches allowed sw (body.instantiate1 x)

  | .const n us => do
      let cTy ← inferType (Expr.const n us) >>= whnf
      if isTypeArg cTy then return true
      if isTypeFormerTy cTy then return true
      if isInstanceConstName n then return true
      if ignoreConstNameForReport n then return true
      if (← returnsClass cTy) then return true
      return allowed.contains n

  | .app _ _ =>
      if isNumeralViaOfNat e then
        return true
      let (head, args0) := getAppSpine e
      let headOk ←
        match head with
        | .const n us => do
            let typeFormer ← isTypeFormerConst n us
            let supportConst ← ignoreConstForReport n us
            pure (allowed.contains n || isMatchLikeConst n || typeFormer || supportConst)
        | .fvar _ => pure true
        | .bvar _ => pure true
        | _       => isCanonicalExprMWithSwitches allowed sw head
      if !headOk then
        return false
      let realArgs ← explicitArgsOfApp head args0
      for a in realArgs do
        if !(← isCanonicalExprMWithSwitches allowed sw a) then
          return false
      return true

def isCanonicalExprM (allowed : Std.HashSet Name) (e : Expr) : MetaM Bool := do
  let cs ← collectRelevantConsts e
  return cs.toList.all (fun n => allowed.contains n)

def isCanonicalExprMWithStructural (allowed : Std.HashSet Name) (opts : StructuralOptions) (e : Expr) :
    MetaM Bool := do
  if !(← isCanonicalExprM allowed e) then
    return false
  isStructurallyCanonicalM opts e

/-
  ============================================================
  6) Command: #isCanonical ...
  ============================================================
-/

private def getWrappedIdentName (stx : Syntax) : CommandElabM Name := do
  if stx.isIdent then
    return stx.getId
  else if stx.getNumArgs > 0 && stx[0].isIdent then
    return stx[0].getId
  else
    throwErrorAt stx "expected an identifier"

syntax canon_opts :=
  "with"
  "admissible_vocabulary" ":=" term
  ("allow_quantifier" ":=" term)?

private partial def collectQuotedNames (stx : Syntax) : CommandElabM (List Name) := do
  if stx.getKind == `Lean.Parser.Term.doubleQuotedName then
    if stx.getNumArgs == 3 && stx[2].isIdent then
      return [stx[2].getId]
    else
      throwErrorAt stx "expected a quoted constant name"
  let mut names := []
  for child in stx.getArgs do
    names := names ++ (← collectQuotedNames child)
  return names

private def parseBoolLiteral (stx : Syntax) : CommandElabM Bool := do
  match stx with
  | `(term| true) => return true
  | `(term| false) => return false
  | _ => throwErrorAt stx "expected boolean literal `true` or `false`"

private def parseAdmissibleOptionsRequired (stx : Syntax) :
    CommandElabM (List Name × StructuralOptions) := do
  match stx with
  | `(canon_opts|
      with admissible_vocabulary := $vocab
      $[allow_quantifier := $allowQuantifier]?) =>
      let names ← collectQuotedNames vocab.raw
      let allowQuantifierValue ←
        match allowQuantifier with
        | some stx => parseBoolLiteral stx
        | none => pure true
      let opts : StructuralOptions := {
        allowQuantifier := allowQuantifierValue
      }
      return (names, opts)
  | _ =>
      throwErrorAt stx
        "malformed options block. Expected: `with admissible_vocabulary := [...]`"

syntax (name := isCanonicalCmd)
  "#isCanonical" term (canon_opts)? : command

private def ppQuotedName (n : Name) : String :=
  "``" ++ n.toString

@[command_elab isCanonicalCmd]
def elabIsCanonicalCmd : CommandElab := fun stx => do
  let tStx : Syntax := stx[1]

  if stx[2].isNone then
    throwErrorAt stx
      "missing options. Use: `#isCanonical t with admissible_vocabulary := [...]`"

  let optStx : Syntax := stx[2][0]
  let (allowedNames, structuralOpts) ← parseAdmissibleOptionsRequired optStx
  let allowed := Std.HashSet.ofList allowedNames

  liftTermElabM do
    let e ← Term.elabTerm tStx none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e

    let ok ← isCanonicalExprMWithStructural allowed structuralOpts e
    let cs ← collectRelevantConsts e

    -- extra safety: never print anything `_private*` even if it slipped in
    let shown :=
      (cs.toList.filter (fun n => ¬ ignoreConstNameForReport n)).map ppQuotedName

    if ok then
      logInfo "```canonical```"
    else
      logInfo "```not canonical```"

    logInfo m!"```[{String.intercalate ", " shown}]```"

end Canonical
