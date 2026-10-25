import Lean
import Mathlib
import Aesop
-- import Smt
-- import Smt.Real
open Lean Elab Tactic Meta Command Expr
set_option pp.piBinderNames.hygienic false

set_option pp.notation true
set_option pp.unicode true
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.foralls true
set_option pp.numericTypes true
set_option pp.coercions true
set_option pp.coercions.types true

syntax "get_state" : tactic
syntax "run_coder" : tactic
syntax "run_conjecturer" : tactic

syntax "try_solvers" : tactic


def getPpTacticState : TacticM String := do
  let goals ← getUnsolvedGoals
  match goals with
  | [] => return "no goals"
  | [g] => return (← Meta.ppGoal g).pretty
  | gs =>
    return (← gs.foldlM (init := "") (fun acc g => do
      return acc ++ "" ++ (← Meta.ppGoal g).pretty)).trim

def getExistsTypesLoop (e : Expr) : MetaM (List (Name × Expr)) := do
  let mut result : List (Name × Expr) := []
  let mut current := e

  while true do
    let currentWhnf ← whnf current
    match currentWhnf with
    | Expr.app (Expr.app (Expr.const `Exists _) ty) lamExpr =>
      let lamExprWhnf ← whnf lamExpr
      match lamExprWhnf with
      | Expr.lam binderName binderType body _ =>
        result := result.append [(binderName, ty)]
        -- Use dummy variable to instantiate and move deeper
        let dummy := mkFVar ⟨Name.anonymous⟩
        current := body.instantiate1 dummy
      | _ => break
    | _ => break

  return result
def getExistsType : TacticM String := do
  let target ← getMainTarget
  let vars ← getExistsTypesLoop target
  let formatted ← vars.mapM fun (n, ty) => do
    let tyStr ← ppExpr ty
    return s!"{n.toString} : {tyStr.pretty}"
  return (formatted.toString.replace "[" "").replace "]" ""


def runECPWithState (function : String) (state : String): TacticM String := do
  let child ← IO.Process.spawn {
    cmd := "python",
    args := #["src/scripts/lean/run_ecp.py" , "--state", state, "--function", function],
    stdin := .piped,
    stdout := .piped,
    stderr := .piped,
    cwd := "/fs01/projects/imosolver/ECP/"
  }
  child.stdin.flush

  let output ← child.stdout.readToEnd
  -- let err ← child.stderr.readToEnd
  -- if err.trim ≠ "" then
  --   logInfo m!"[stderr from {function}]{err.trim}"
  return output.trim


private def collectHypsAndGoal (type : Expr) : MetaM (Array (Name × Expr) × List Expr × Expr) := do
  let typeWhnf ← whnf type
  logInfo type
  logInfo typeWhnf
  forallTelescope typeWhnf fun xs body => do
    logInfo xs
    let mut vars := #[]
    let mut hyps := []

    for x in xs do
      let xType ← inferType x
      if (← isProp xType) then
        hyps := hyps ++ [xType]
      else
        let localDecl ← getFVarLocalDecl x
        vars := vars.push (localDecl.userName, xType)

    return (vars, hyps, body)



elab_rules : tactic
  | `(tactic| get_state) => do
    let state ← getPpTacticState
    let filename ← getFileName
    let content ← IO.FS.readFile filename

    logInfo m!"State: {state}, Filename: {filename}, File content: {content}"


  | `(tactic| run_coder) => do
    let state ← getPpTacticState
    let result ←  runECPWithState "coder" state
    logInfo m!"[enumerate_solution]{result}"

  | `(tactic| run_conjecturer) => do
    let state ← getPpTacticState
    let result ←  runECPWithState "conjecturer" state
    logInfo m!"[find_solution]{result}"

elab_rules : tactic
  | `(tactic| try_solvers) => do
    -- build an array of the tactics we want to try
    let tactics ← pure #[
      ← `(tactic| native_decide)
      ← `(tactic| simp),
      ← `(tactic| aesop),
      ← `(tactic| nlinarith),
      ← `(tactic| ring),
      ← `(tactic| norm_num),
      -- ← `(tactic| smt [*])
    ]

    -- get the initial list of goals
    let gsBefore ← getGoals
    let mut solved := false

    for tac in tactics do
      if ¬solved then
        let snapshot ← saveState
        try
          -- apply the candidate tactic
          evalTactic tac
          -- check how many goals remain
          let gsAfter ← getGoals
          if gsAfter.length < gsBefore.length then
            solved := true
          else
            -- it did nothing, roll back
            snapshot.restore
        catch _ =>
          -- it outright failed, roll back
          snapshot.restore

    if solved then
      logInfo m!"True"
    else
      logInfo m!"False"

syntax "print_fol" : tactic

private def joinWith (sep : String) (xs : List String) : String :=
  match xs with
  | []      => ""
  | x :: xs => xs.foldl (init := x) (fun acc s => acc ++ sep ++ s)

private def prettyBinderNamesFresh (ns : List Name) : List String :=
  Id.run do
    let mut k := 0
    ns.map (fun n =>
      if n == Name.anonymous then
        let k := k + 1
        s!"_x{k}"
      else
        n.toString)

elab_rules : tactic
  | `(tactic| print_fol) => do
    let g ← getMainGoal
    g.withContext do
      -- 1) Partition locals into (term variables) vs (Prop hypotheses),
      --    and *sanitize* instance-implicit binders by forcing name to `_`.
      let lctx ← getLCtx
      let mut vars  : Array (Name × Expr) := #[]
      let mut props : Array Expr := #[]

      for decl in lctx do
        if !decl.isAuxDecl then
          if ← isProp decl.type then
            props := props.push decl.type
          else
            let n : Name :=
              if decl.binderInfo == BinderInfo.instImplicit then
                Name.anonymous
              else
                decl.userName.eraseMacroScopes
            vars := vars.push (n, decl.type)

      -- 2) Group variables by *definitional equality* of types (not `==`)
      --    so you don’t get random splits.
      let mut groups : Array (Expr × List Name) := #[]

      for (n, ty) in vars do
        let mut placed := false
        for i in [:groups.size] do
          let (ty', ns) := groups[i]!
          if (← isDefEq ty ty') then
            groups := groups.set! i (ty', ns ++ [n])
            placed := true
            break
        if !placed then
          groups := groups.push (ty, [n])

      -- 3) Build the ∀-prefix
      let mut quantStr := ""
      for (ty, ns) in groups.toList do
        let tyStr := (← ppExpr ty).pretty
        let namesStr := joinWith " " (prettyBinderNamesFresh ns)

        quantStr := quantStr ++ s!"∀ ({namesStr} : {tyStr}), "

      -- 4) Conjoin Prop hyps into a single implication prefix
      let propsStr ← do
        if props.isEmpty then
          pure ""
        else
          let pieces ← props.toList.mapM (fun p => do
            let s := (← ppExpr p).pretty
            pure s!"({s})")
          pure s!"({joinWith " ∧ " pieces}) → "

      -- 5) Goal
      let tgtStr := (← ppExpr (← g.getType)).pretty

      -- 6) EXACTLY ONE output
      logInfoAt (← getRef) m!"```{quantStr}{propsStr}({tgtStr})```"

/-- Internal helper: given an expression `e : Prop`, find the first `∃`-binder
    and return its name and type. -/
private partial def firstExistsBinder (e : Expr) : MetaM (Option (Name × Expr)) := do
  -- Normalize a bit to expose `Exists` applications
  let e ← whnf e
  -- Case 1: the expression is literally an `Exists` application
  if e.isAppOfArity ``Exists 2 then
    let args := e.getAppArgs
    match args with
    | #[α, p] =>
        -- `p` should be a lambda `fun (x : α) => ...`
        match p with
        | Expr.lam n ty _ _ =>
            -- we just use the binder name `n` and its type `ty`
            return some (n, ty)
        | _ =>
            return none
    | _ =>
        -- `isAppOfArity` says this shouldn't happen, but be defensive
        return none
  else
    -- Case 2: skip leading ∀ / → binders and recurse on the body
    match e with
    | Expr.forallE n ty body bi =>
        withLocalDecl n bi ty fun x => do
          firstExistsBinder (body.instantiate1 x)
    | _ =>
        return none
syntax "print_exists_var" : tactic
elab_rules : tactic
  | `(tactic| print_exists_var) => do
    let g ← getMainGoal
    g.withContext do
      let tgt ← g.getType
      let some (n, ty) ← firstExistsBinder tgt
        | throwError "Goal is not (or does not contain) an existential quantifier."
      let tyStr := (← ppExpr ty).pretty
      logInfoAt (← getRef) m!"```∃ {n.toString} : {tyStr}```"


-- example : ∃ n, n = 1 := by

--   print_exists_var


/- ----------------------------
   Demo: prints a FOL-style line and completes the proof.
   You should see something like:
   ∀ x : Nat, ∀ y : Nat, x = 1 ∧ y = 2 → x = 1
----------------------------- -/
-- theorem test (x : ℕ ) (hx : x = 1) (y : Nat) (z : ℝ)  (hy : y = 2) : x = 1 := by
--   print_fol
-- set_option pp.universes true
-- set_option pp.all true
-- set_option pp.explicit true


-- abbrev putnam_1995_b4_solution : ℤ × ℤ × ℤ × ℤ := ⟨3,1,5,2⟩

-- theorem putnam_1995_b4
--     (contfrac : ℝ)
--     (hcontfrac : contfrac = 2207 - 1 / contfrac)
--     (hcontfrac' : 1 < contfrac) :
--     let ⟨a, b, c, d⟩ := putnam_1995_b4_solution
--     contfrac ^ ((1 : ℝ) / 8) = (a + b * Real.sqrt c) / d := by
--     print_fol
-- theorem hello : ∀ (contfrac : ℝ), ((contfrac = (2207 : ℝ) - (1 : ℝ) / contfrac) ∧ ((1 : ℝ) < contfrac)) → (match putnam_1995_b4_solution with
-- | (a, b, c, d) => contfrac ^ (1 / 8 : ℝ) = ((↑a : ℝ) + (↑b : ℝ) * √(↑c : ℝ)) / (↑d : ℝ)):=by sorry
-- theorem P2000AIMEII_1 (y:ℕ ):    (∃ (m n: ℕ) , 1 ≤ m ∧ 1 ≤ n ∧ Nat.Coprime m n ∧ (m : ℚ) / (n : ℚ) = (3 : ℚ) / 4 ∧ m + n = y)    ↔ y = 7:=by
--   -- sorry
--   print_fol
  -- extract_goal
-- #checkP2000AIMEII_1

-- abbrev putnam_1976_b2_solution : ℕ × Set (List (ℤ × ℤ)) := (8, {[(0, 0)], [(2, 0)], [(0, 1)], [(0, 2)], [(0, 3)], [(0, 4)], [(0, 5)], [(0, 6)]})

-- theorem putnam_1976_b2
-- (G : Type*) [Group G]
-- (A B : G)
-- (word : List (ℤ × ℤ) → G)
-- (hword : word = fun w : List (ℤ × ℤ) => (List.map (fun t : ℤ × ℤ => A^(t.1)*B^(t.2)) w).prod)
-- (hG : ∀ g : G, ∃ w : List (ℤ × ℤ), g = word w)
-- (hA : A^4 = 1 ∧ A^2 ≠ 1)
-- (hB : B^7 = 1 ∧ B ≠ 1)
-- (h1 : A*B*A^(-(1 : ℤ))*B = 1)
-- (S : Set G)
-- (hS : S = {g : G | ∃ C : G, C^2 = g})
-- : S.ncard = putnam_1976_b2_solution.1 ∧ S = {word w | w ∈ putnam_1976_b2_solution.2} := by
--   print_fol
-- example : ∀ (G : Type u_1), ∀ (_ : Group G), ∀ (A B : G), ∀ (word : List (ℤ × ℤ) → G), ∀ (S : Set G), ((word = fun (w : List (ℤ × ℤ)) => (List.map (fun (t : ℤ × ℤ) => A ^ t.1 * B ^ t.2) w).prod) ∧ (∀ (g : G), ∃ (w : List (ℤ × ℤ)), g = word w) ∧ (A ^ (4 : ℕ) = (1 : G) ∧ A ^ (2 : ℕ) ≠ (1 : G)) ∧ (B ^ (7 : ℕ) = (1 : G) ∧ B ≠ (1 : G)) ∧ (A * B * A ^ (-1 : ℤ) * B = (1 : G)) ∧ (S = {g : G | ∃ (C : G), C ^ (2 : ℕ) = g})) → (S.ncard = putnam_1976_b2_solution.1 ∧ S = {x : G | ∃ w ∈ putnam_1976_b2_solution.2, word w = x}) := by sorry



-- abbrev putnam_1974_b1_solution : (Fin 5 → EuclideanSpace ℝ (Fin 2)) → Prop := fun p ↦ ∃ᵉ (B > 0) (o : Equiv.Perm (Fin 5)), ∀ i, dist (p (o i)) (p (o (i + 1))) = B


-- theorem putnam_1974_b1
--     (d : (Fin 5 → EuclideanSpace ℝ (Fin 2)) → ℝ)
--     (d_def : ∀ p, d p = ∑ ⟨i, j⟩ : Fin 5 × Fin 5, if i < j then dist (p i) (p j) else 0)
--     (p : Fin 5 → EuclideanSpace ℝ (Fin 2))
--     (hp : ∀ i, ‖p i‖ = 1) :
--     d p = sSup {d q | (q) (hq : ∀ i, ‖q i‖ = 1)} ↔ putnam_1974_b1_solution p := by print_fol
