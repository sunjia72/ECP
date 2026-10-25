import Lean
import utils.canonical_all_in_one

open Lean Elab Command Meta

namespace ECP.ExtractExistsWitness

private def existsIntroWitness? (e : Expr) : Option Expr :=
  match e.getAppFn with
  | Expr.const name _ =>
      if name == ``Exists.intro then
        let args := e.getAppArgs
        if h : 3 < args.size then
          some args[2]
        else
          none
      else
        none
  | _ => none

partial def firstWitnessAtProofRoot? (e : Expr) : MetaM (Option Expr) := do
  let e ← withTransparency .all <| whnf (← instantiateMVars e)
  if let some witness := existsIntroWitness? e then
    return some witness
  match e with
  | Expr.mdata _ body =>
      firstWitnessAtProofRoot? body
  | Expr.letE name type value body _ =>
      withLetDecl name type value fun x =>
        firstWitnessAtProofRoot? (body.instantiate1 x)
  | Expr.lam name type body binderInfo =>
      withLocalDecl name binderInfo type fun x =>
        firstWitnessAtProofRoot? (body.instantiate1 x)
  | _ =>
      return none

/--
Extract the witness used by the proof term for the theorem's outermost existential.

The output is logged as a Markdown fenced code block to make downstream parsing
straightforward.
-/
elab "#extract_first_exists_witness " id:ident : command => do
  let name ← Command.liftTermElabM <| realizeGlobalConstNoOverloadWithInfo id
  let ci ← getConstInfo name
  let some value := ci.value?
    | throwError "{name} has no body to inspect"
  let some witness ← Command.liftTermElabM <| firstWitnessAtProofRoot? value
    | throwError "could not find an outer proof-root Exists.intro in {name}"
  let fmt ← Command.liftTermElabM <| Meta.ppExpr witness
  logInfo m!"```\n{fmt}\n```"

end ECP.ExtractExistsWitness

namespace ECP.CheckExistsWitnessCanonical

syntax witness_canon_opts :=
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
    CommandElabM (List Name × Canonical.StructuralOptions) := do
  match stx with
  | `(witness_canon_opts|
      with admissible_vocabulary := $vocab
      $[allow_quantifier := $allowQuantifier]?) =>
      let names ← collectQuotedNames vocab.raw
      let allowQuantifierValue ←
        match allowQuantifier with
        | some stx => parseBoolLiteral stx
        | none => pure true
      let opts : Canonical.StructuralOptions := {
        allowQuantifier := allowQuantifierValue
      }
      return (names, opts)
  | _ =>
      throwErrorAt stx
        "malformed options. Expected: `with admissible_vocabulary := [...]`"

private def logCanonicalStatus (ok : Bool) : CommandElabM Unit := do
  if ok then
    logInfo "```canonical```"
  else
    logInfo "```not canonical```"

syntax (name := checkFirstExistsWitnessCanonicalCmd)
  "#check_first_exists_witness_canonical" ident witness_canon_opts : command

/--
Extract the proof-root existential witness from a theorem and check whether that
witness uses only constants covered by the supplied admissible vocabulary.

This command logs exactly one fenced status block when the theorem can be
inspected:

```
canonical
```

or

```
not canonical
```

If the declaration is not available, the command stays silent so it does not add
secondary diagnostics after an already-failed theorem declaration in batched
verification.
-/
@[command_elab checkFirstExistsWitnessCanonicalCmd]
def elabCheckFirstExistsWitnessCanonicalCmd : CommandElab := fun stx => do
  let idStx := stx[1]
  let optStx := stx[2]
  let (allowedNames, structuralOpts) ← parseAdmissibleOptionsRequired optStx
  let allowed := Std.HashSet.ofList allowedNames
  let env ← getEnv
  let declName := idStx.getId
  let some ci := env.find? declName
    | return ()
  let some value := ci.value?
    | logCanonicalStatus false
  let some witness ← Command.liftTermElabM <| ECP.ExtractExistsWitness.firstWitnessAtProofRoot? value
    | logCanonicalStatus false
  let ok ← Command.liftTermElabM <| Canonical.isCanonicalExprMWithStructural allowed structuralOpts witness
  logCanonicalStatus ok

end ECP.CheckExistsWitnessCanonical
