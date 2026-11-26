module

public import OracqVerify.RIR.ScopedLinkError
public import OracqVerify.RIR.ScopedGateWord
public import OracqVerify.RIR.RationalPhase
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! End-to-end quantitative linking for a phase provider under control and adjoint. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.ApproximatePhase

open Lean RIR Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.OperatorErrors.OperatorError
open scoped Matrix Matrix.Norms.L2Operator

def slotName : String := "phase_slot"
def callerName : String := "phase_caller"

def slot (angle : Option JsonNumber) : ScopedModule :=
  ⟨slotName, 1, 0, [], angle.map fun value => [.gphase value], 0, true, true⟩

def callSite : CallSite := ⟨slotName, [[0]], []⟩

def call : ResolvedInstruction := .query slotName [[0]] []

def first : ResolvedInstruction := .controlled ⟨[1], 1⟩ call
def second : ResolvedInstruction := .adjoint call
def body (rounds : Nat) : List ResolvedInstruction :=
  (List.replicate rounds [first, second]).flatten

def root (rounds : Nat) : ScopedModule := gateModule callerName 2 (body rounds)

def graph (angle : Option JsonNumber) (rounds : Nat) : ScopedProgram :=
  ⟨callerName, [slot angle, root rounds], 2, 0⟩

def chooseAngle (bound : ScopedProgram) : Except String JsonNumber := do
  let impl ← lookup (bound.modules.map fun m => (m.name, m)) slotName "phase provider"
  match impl.body with
  | some [.gphase a] => pure a
  | _ => throw "Expected one serialized global phase in the provider"

def error (reference concrete : JsonNumber) : ℚ :=
  |rationalAngle reference - rationalAngle concrete|

def totalError (reference concrete : JsonNumber) (rounds : Nat) : ℚ :=
  (2 * rounds : ℕ) * error reference concrete

structure Certificate (openProgram boundProgram : Program) (reference : JsonNumber) (rounds : Nat) where
  link : ScopedSourceLink openProgram boundProgram []
  angle : JsonNumber
  caller : link.caller = graph none rounds
  closed : link.closed = graph (some angle) rounds

def certify (openProgram boundProgram : Program) (reference : JsonNumber) (rounds : Nat) :
    Except String (Certificate openProgram boundProgram reference rounds) := do
  let link ← verifyScopedSourceLink openProgram boundProgram
  let angle ← chooseAngle link.closed
  if caller : link.caller = graph none rounds then
    if closed : link.closed = graph (some angle) rounds then
      pure ⟨link, angle, caller, closed⟩
    else throw "Expected the retained caller and one single-phase provider"
  else throw "Expected the specified number of controlled/adjoint call pairs"

private theorem chord (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a-b| := by
  have eq : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      (Complex.exp (Complex.I * ((a-b : ℝ) : ℂ)) - 1) * Complex.exp ((b : ℂ) * Complex.I) := by
    have exponent : Complex.I * ((a-b : ℝ) : ℂ) + (b : ℂ) * Complex.I = (a : ℂ) * Complex.I := by
      push_cast
      ring
    rw [sub_mul, one_mul, ← Complex.exp_add, exponent]
  rw [eq, norm_mul, mul_comm (b : ℂ), Complex.norm_exp_I_mul_ofReal, mul_one]
  simpa only [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a-b))

private theorem phase_distance (reference concrete : JsonNumber) :
    ‖globalPhase 1 (angleValue reference) - globalPhase 1 (angleValue concrete)‖ ≤
      (error reference concrete : ℝ) := by
  unfold globalPhase
  rw [Matrix.diagonal_sub, Matrix.l2_opNorm_diagonal]
  have nonnegative : 0 ≤ (error reference concrete : ℝ) := by
    exact_mod_cast (abs_nonneg (rationalAngle reference - rationalAngle concrete))
  apply (pi_norm_le_iff_of_nonneg nonnegative).mpr
  intro _
  simpa [error] using chord (angleValue reference) (angleValue concrete)

noncomputable def phase (angle : JsonNumber) : WireMatrix 1 :=
  globalPhase 1 (angleValue angle)

private theorem provider (a : JsonNumber) (s : Snapshot) :
    (slot (some a)).interpret [] s = .ok (phase a) := by
  apply ScopedModule.interpret_zero_locals _ _ _ _ _ _ _ _ _ (globalPhase_unitary _ _)
  change Except.ok (1 * phase a) = _
  rw [one_mul]
  rfl

noncomputable def ideal (a : JsonNumber) : ScopedOracle :=
  fun name width _ =>
    if eq : 1 = width then
      if name = slotName then .ok (eq ▸ phase a) else .error "Unknown phase slot"
    else .error "Unexpected phase width"

noncomputable def referenceEnv (a : JsonNumber) : ScopedEnvironment :=
  [(slotName, ⟨1, [], ideal a slotName 1⟩)]

noncomputable def concreteEnv (a : JsonNumber) : ScopedEnvironment :=
  [(slotName, ⟨1, [], (slot (some a)).interpret []⟩)]

def dataView : View 2 1 := (View.ofWires 2 1 [0]).toOption.get (by decide)
def guardView : View 2 1 := (View.ofWires 2 1 [1]).toOption.get (by decide)

noncomputable def placed (a : JsonNumber) : WireMatrix 2 := dataView.placeMatrix (phase a)

private theorem call_evaluates (env : ScopedEnvironment) (s : Snapshot) (a : JsonNumber)
    (meaning : Snapshot → Except String (WireMatrix 1))
    (lookupEq : lookup env slotName "scoped callee" = .ok ⟨1, [], meaning⟩)
    (evaluates : meaning emptySnapshot = .ok (phase a)) :
    env.atCall 2 s callSite = .ok (placed a) := by
  unfold ScopedEnvironment.atCall callSite
  simp only [lookupEq, Bind.bind, Except.bind]
  rw [show View.ofWires 2 1 [[0]].flatten = .ok dataView from rfl]
  simp [show s.forward [] [] = .ok emptySnapshot from rfl, evaluates, placed, Pure.pure, Except.pure]

private theorem ref_call (s : Snapshot) (a : JsonNumber) :
    (referenceEnv a).atCall 2 s callSite = .ok (placed a) :=
  call_evaluates _ _ _ _ rfl (by simp [ideal])

private theorem impl_call (s : Snapshot) (a : JsonNumber) :
    (concreteEnv a).atCall 2 s callSite = .ok (placed a) :=
  call_evaluates _ _ _ _ rfl (provider a _)

noncomputable def controlledPhase (a : JsonNumber) : WireMatrix 2 :=
  controlledMatrix (matchesGuard guardView 1) (placed a)

private theorem first_matrix (s : Snapshot) (env : ScopedEnvironment) (a : JsonNumber)
    (called : env.atCall 2 s callSite = .ok (placed a)) :
    first.matrixWith 2 s (env.atCall 2 s) = .ok (controlledPhase a) := by
  change (do
    let view ← View.ofWires 2 1 [1]
    let u ← env.atCall 2 s callSite
    pure (controlledMatrix (matchesGuard view 1) u)) = _
  rw [show View.ofWires 2 1 [1] = .ok guardView from rfl]
  simp only [Bind.bind, Except.bind, called, Pure.pure, Except.pure, controlledPhase]

private theorem second_matrix (s : Snapshot) (env : ScopedEnvironment) (a : JsonNumber)
    (called : env.atCall 2 s callSite = .ok (placed a)) :
    second.matrixWith 2 s (env.atCall 2 s) = .ok (placed a)ᴴ := by
  change (do let u ← env.atCall 2 s callSite; pure uᴴ) = _
  simp only [Bind.bind, Except.bind, called, Pure.pure, Except.pure]

private theorem controlled_unitary (a : JsonNumber) :
    controlledPhase a ∈ unitaryGroup (Reg 2) ℂ :=
  controlledMatrix_unitary _
    (dataView.placeMatrix_unitary (globalPhase_unitary _ _))
    (dataView.placeMatrix_preserves_guard guardView (by decide) 1 _)

private theorem adjoint_unitary (a : JsonNumber) : (placed a)ᴴ ∈ unitaryGroup (Reg 2) ℂ := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Unitary.star_mem_iff.mpr (dataView.placeMatrix_unitary (globalPhase_unitary _ _))

private theorem body_members (rounds : Nat) (step : ResolvedInstruction)
    (member : step ∈ body rounds) : step = first ∨ step = second := by
  simp only [body, List.mem_flatten, List.mem_replicate] at member
  obtain ⟨l, ⟨_, same⟩, found⟩ := member
  subst l
  simpa using found

private theorem contractions (reference concrete : JsonNumber) (rounds : Nat) :
    ∀ s step, step ∈ body rounds → ∀ u v,
      step.matrixWith 2 s ((referenceEnv reference).atCall 2 s) = .ok u →
      step.matrixWith 2 s ((concreteEnv concrete).atCall 2 s) = .ok v →
      ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 := by
  intro s step member u v left right
  rcases body_members rounds step member with rfl | rfl
  · rw [first_matrix _ _ _ (ref_call s reference), Except.ok.injEq] at left
    rw [first_matrix _ _ _ (impl_call s concrete), Except.ok.injEq] at right
    exact ⟨left ▸ l2_norm_unitary_le_one (controlled_unitary reference),
      right ▸ l2_norm_unitary_le_one (controlled_unitary concrete)⟩
  · rw [second_matrix _ _ _ (ref_call s reference), Except.ok.injEq] at left
    rw [second_matrix _ _ _ (impl_call s concrete), Except.ok.injEq] at right
    exact ⟨left ▸ l2_norm_unitary_le_one (adjoint_unitary reference),
      right ▸ l2_norm_unitary_le_one (adjoint_unitary concrete)⟩

noncomputable def result (rounds : Nat) (a : JsonNumber) : WireMatrix 2 :=
  wordMatrix ((List.replicate rounds [controlledPhase a, (placed a)ᴴ]).flatten)

private theorem root_evaluates (rounds : Nat) (a : JsonNumber) (env : ScopedEnvironment) (s : Snapshot)
    (called : env.atCall 2 s callSite = .ok (placed a)) :
    (root rounds).interpret env s = .ok (result rounds a) := by
  apply ScopedModule.interpret_zero_locals _ _ _ _ _ _ _ _ _
  · apply wordMatrix_unitary
    intro matrix member
    simp only [List.mem_flatten, List.mem_replicate] at member
    obtain ⟨l, ⟨_, same⟩, found⟩ := member
    subst l
    simp only [List.mem_cons, List.not_mem_nil, or_false] at found
    rcases found with rfl | rfl
    · exact controlled_unitary a
    · exact adjoint_unitary a
  change ((body rounds).mapM (ResolvedInstruction.matrixWith 2 s (env.atCall 2 s))).map wordMatrix =
    .ok (result rounds a)
  have mapped : (body rounds).mapM (ResolvedInstruction.matrixWith 2 s (env.atCall 2 s)) =
      .ok ((List.replicate rounds [controlledPhase a, (placed a)ᴴ]).flatten) := by
    induction rounds with
    | zero => rfl
    | succ k ih =>
      simp only [body, List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append] at ih ⊢
      simp [List.mapM_cons, first_matrix _ _ _ called, second_matrix _ _ _ called, ih,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [mapped]
  rfl

private noncomputable def slotBudgets (reference concrete : JsonNumber) : ScopedBudgetTable :=
  [(slotName, fun _ => (error reference concrete : ℝ))]

private theorem slot_evidence (reference concrete : JsonNumber) :
    ScopedErrorEvidence (referenceEnv reference) (concreteEnv concrete) (slotBudgets reference concrete) := by
  refine .cons .nil _ _ _ _ _ _ ?_
  intro s u v ref actual
  have opened : ideal reference slotName 1 s = .ok (phase reference) := by simp [ideal]
  have uEq : phase reference = u := Except.ok.inj (opened.symm.trans ref)
  have vEq : phase concrete = v := Except.ok.inj ((provider concrete s).symm.trans actual)
  rw [← uEq, ← vEq]
  exact phase_distance _ _

private theorem budget_root (reference concrete : JsonNumber) (rounds : Nat) (s : Snapshot) :
    ((body rounds).map (ResolvedInstruction.callBudget
      ((referenceEnv reference).callError (slotBudgets reference concrete) s))).sum =
      (totalError reference concrete rounds : ℝ) := by
  have price : (referenceEnv reference).callError (slotBudgets reference concrete) s callSite =
      (error reference concrete : ℝ) := rfl
  have firstCost : first.callBudget
      ((referenceEnv reference).callError (slotBudgets reference concrete) s) = _ := price
  have secondCost : second.callBudget
      ((referenceEnv reference).callError (slotBudgets reference concrete) s) = _ := price
  induction rounds with
  | zero => simp [body, totalError]
  | succ k ih =>
    unfold body at ih
    simp only [body, List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append,
      List.map_cons, List.sum_cons, firstCost, secondCost]
    change (error reference concrete : ℝ) + ((error reference concrete : ℝ) + _) = _
    rw [ih]
    simp only [totalError]
    push_cast
    ring

private theorem accepted_bound
    {source bound : Program} (link : ScopedSourceLink source bound [])
    (reference concrete : JsonNumber) (rounds : Nat)
    (caller : link.caller = graph none rounds) (closed : link.closed = graph (some concrete) rounds) :
    ∃ (u v : WireMatrix 2),
      let snapshot := emptySnapshot
      (graph none rounds).matrixWith snapshot [slotName] (ideal reference) = .ok u ∧
      bound.scopedMatrix snapshot = .ok ⟨2, v⟩ ∧
      ‖u-v‖ ≤ (totalError reference concrete rounds : ℝ) := by
  let s := emptySnapshot
  let budgets : ScopedBudgetTable :=
    (callerName, fun _ => (totalError reference concrete rounds : ℝ)) :: slotBudgets reference concrete
  let abstract := result rounds reference
  let actual := result rounds concrete
  have openEval : (graph none rounds).matrixWith s [slotName] (ideal reference) = .ok abstract := by
    change (do
      let d ← lookup ((callerName, (⟨2, [], (root rounds).interpret (referenceEnv reference)⟩ :
        ScopedDefinition)) :: referenceEnv reference) callerName "scoped entry"
      if h : d.publicWires = 2 then return h ▸ (← d.apply s) else throw "Scoped entry width mismatch") = _
    simp [lookup, List.lookup, Bind.bind, Except.bind, Pure.pure, Except.pure,
      root_evaluates rounds reference _ s (ref_call s reference), abstract]
    rfl
  have closedEval : (graph (some concrete) rounds).matrixWith s = .ok actual := by
    change (do
      let d ← lookup ((callerName, (⟨2, [], (root rounds).interpret (concreteEnv concrete)⟩ :
        ScopedDefinition)) :: concreteEnv concrete) callerName "scoped entry"
      if h : d.publicWires = 2 then return h ▸ (← d.apply s) else throw "Scoped entry width mismatch") = _
    simp [lookup, List.lookup, Bind.bind, Except.bind, Pure.pure, Except.pure,
      root_evaluates rounds concrete _ s (impl_call s concrete), actual]
    rfl
  have rebuilt : link.exposed = graph none rounds := by
    rw [link.checked, caller, closed]
    rfl
  have slots : scopedSlots link.caller = [slotName] := by rw [caller]; rfl
  have evaluated : bound.scopedMatrix s = .ok ⟨2, actual⟩ := by
    have resolved := link.bound_resolved
    rw [closed] at resolved
    exact Program.scopedMatrix_of_resolved resolved closedEval
  have evidence := (slot_evidence reference concrete).extendBody
    (root rounds) (body rounds) rfl (contractions reference concrete rounds)
  have equalCost :
      (fun s => ((body rounds).map (ResolvedInstruction.callBudget
        ((referenceEnv reference).callError (slotBudgets reference concrete) s))).sum) =
        fun _ => (totalError reference concrete rounds : ℝ) :=
    funext (budget_root reference concrete rounds)
  rw [equalCost] at evidence
  refine ⟨abstract, actual, openEval, evaluated, ?_⟩
  cases link with
  | mk original final exposed src dst reconstruction checked =>
    dsimp only at rebuilt closed caller slots ⊢
    subst exposed
    subst final
    subst original
    let aligned : ScopedSourceLink source bound [] :=
      ⟨graph none rounds, graph (some concrete) rounds, graph none rounds, src, dst, reconstruction, rfl⟩
    exact aligned.distance_le s (ideal reference) budgets evidence _ rfl openEval evaluated

/-- The CLI's rational budget bounds the difference of the actual decoded
program and its resolved caller with the specified phase. -/
theorem Certificate.sound {source bound : Program} {reference : JsonNumber} {rounds : Nat}
    (cert : Certificate source bound reference rounds) :
    ∃ (u v : WireMatrix 2),
      (graph none rounds).matrixWith emptySnapshot [slotName] (ideal reference) = .ok u ∧
      bound.scopedMatrix emptySnapshot = .ok ⟨2, v⟩ ∧
      ‖u-v‖ ≤ (totalError reference cert.angle rounds : ℝ) :=
  accepted_bound cert.link reference cert.angle rounds cert.caller cert.closed

end OracqVerify.Verification.ApproximatePhase
