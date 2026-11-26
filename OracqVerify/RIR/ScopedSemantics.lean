module

public import OracqVerify.RIR.ScopedResolve
public import OracqVerify.RIR.BlockEncoding
public import OracqVerify.RIR.Link

/-! Entry and exit semantics for a module's zero-initialized private wires. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Concepts.Execution.WorkspaceCP Qatlib.Foundations.PureStateMath
open scoped Matrix

/-- Keep the public bits in order and initialize every local bit to zero. -/
def appendZero (publicWidth localWidth : Nat) : Reg publicWidth ↪ Reg (publicWidth + localWidth) where
  toFun state wire := if h : wire.val < publicWidth then state ⟨wire.val, h⟩ else false
  inj' := by
    intro first second equal
    funext wire
    simpa [wire.isLt] using congrFun equal (Fin.castAdd localWidth wire)

@[simp] theorem appendZero_public {p l : Nat} (state : Reg p) (wire : Fin p) :
    appendZero p l state (Fin.castAdd l wire) = state wire := by simp [appendZero, wire.isLt]

@[simp] theorem appendZero_local {p l : Nat} (state : Reg p) (wire : Fin l) :
    appendZero p l state (Fin.natAdd p wire) = false := by
  simp [appendZero, Nat.not_lt.mpr (Nat.le_add_right p wire.val)]

theorem mem_range_appendZero {p l : Nat} (row : Reg (p + l)) :
    row ∈ Set.range (appendZero p l) ↔ ∀ wire : Fin l, row (Fin.natAdd p wire) = false := by
  constructor
  · rintro ⟨input, rfl⟩ wire
    exact appendZero_local input wire
  · intro zero
    refine ⟨fun wire => row (Fin.castAdd l wire), ?_⟩
    funext wire
    refine Fin.addCases ?_ ?_ wire
    · intro publicBit
      exact appendZero_public _ publicBit
    · intro localBit
      rw [appendZero_local, zero]

abbrev ScopedModule.width (m : ScopedModule) := m.publicWires + m.localWires

/-- The physical image of a module entry state in its relative frame. -/
noncomputable def ScopedModule.frame (m : ScopedModule) :
    Matrix (Reg m.width) (Reg m.publicWires) ℂ :=
  basisFrame (appendZero m.publicWires m.localWires)

/-- Interpret a single definition with its callees supplied in the caller's
coordinates. Each call site includes its actual bank handles. -/
noncomputable def ScopedModule.bodyMatrix (m : ScopedModule) (snapshot : Snapshot)
    (oracle : Oracle m.width) : Except String (WireMatrix m.width) := do
  let some instructions := m.body | throw s!"Open slot: {m.name}"
  return wordMatrix (← instructions.mapM (ResolvedInstruction.matrixWith m.width snapshot oracle))

/-- The body returns the local wires to zero on the entire encoded input space. -/
def ScopedModule.Clean (m : ScopedModule) (u : WireMatrix m.width) : Prop :=
  rangeProjector m.frame * (u * m.frame) = u * m.frame

/-- The action visible at the public interface. It describes a valid scope exit
when the ambient body satisfies `Clean`. -/
noncomputable def ScopedModule.publicMatrix (m : ScopedModule) (u : WireMatrix m.width) :
    WireMatrix m.publicWires := compress m.frame u m.frame

theorem ScopedModule.frame_isIsometry (m : ScopedModule) : IsIsometry m.frame :=
  basisFrame_isIsometry _

theorem ScopedModule.clean_iff (m : ScopedModule) (u : WireMatrix m.width) :
    m.Clean u ↔ u * m.frame = m.frame * m.publicMatrix u := by
  simp only [Clean, publicMatrix, compress, rangeProjector, Matrix.mul_assoc, eq_comm]

private theorem publicMatrix_of_action {m : ScopedModule} {u : WireMatrix m.width}
    {v : WireMatrix m.publicWires} (action : u * m.frame = m.frame * v) :
    m.publicMatrix u = v := by
  have frameEq : m.frameᴴ * m.frame = 1 := m.frame_isIsometry
  rw [ScopedModule.publicMatrix, compress, Matrix.mul_assoc, action, ← Matrix.mul_assoc,
    frameEq, Matrix.one_mul]

theorem ScopedModule.publicMatrix_unitary {m : ScopedModule} {u : WireMatrix m.width}
    (unitary : u ∈ Matrix.unitaryGroup (Reg m.width) ℂ) (clean : m.Clean u) :
    m.publicMatrix u ∈ Matrix.unitaryGroup (Reg m.publicWires) ℂ := by
  let F := m.frame
  let v := m.publicMatrix u
  have hF : Fᴴ * F = 1 := m.frame_isIsometry
  have hu : uᴴ * u = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp unitary)
  have action : u * F = F * v := (m.clean_iff u).mp clean
  change v ∈ Matrix.unitaryGroup _ ℂ
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  calc
    _ = (F * v)ᴴ * (F * v) := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, hF, Matrix.one_mul]
    _ = (u * F)ᴴ * (u * F) := by rw [action]
    _ = 1 := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, hu, Matrix.one_mul, hF]

theorem ScopedModule.publicMatrix_adjoint (m : ScopedModule) (u : WireMatrix m.width) :
    m.publicMatrix uᴴ = (m.publicMatrix u)ᴴ := by
  simp only [publicMatrix, compress, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

/-- Calling the adjoint of a clean unitary also restores the local wires. -/
theorem ScopedModule.clean_adjoint {m : ScopedModule} {u : WireMatrix m.width}
    (unitary : u ∈ Matrix.unitaryGroup (Reg m.width) ℂ) (clean : m.Clean u) :
    m.Clean uᴴ := by
  let F := m.frame
  let v := m.publicMatrix u
  have hu : uᴴ * u = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp unitary)
  have hv : v * vᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp (m.publicMatrix_unitary unitary clean))
  have action : u * F = F * v := (m.clean_iff u).mp clean
  apply (m.clean_iff uᴴ).mpr
  rw [m.publicMatrix_adjoint]
  change uᴴ * F = F * vᴴ
  calc
    _ = uᴴ * ((F * v) * vᴴ) := by rw [Matrix.mul_assoc F, hv, Matrix.mul_one]
    _ = (uᴴ * u) * F * vᴴ := by
      rw [← action]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu, Matrix.one_mul]

/-- Executing two clean bodies in the same frame composes their public actions. -/
theorem ScopedModule.clean_compose {m : ScopedModule} {first second : WireMatrix m.width}
    (hFirst : m.Clean first) (hSecond : m.Clean second) :
    m.Clean (second * first) ∧
      m.publicMatrix (second * first) = m.publicMatrix second * m.publicMatrix first := by
  have action :
      (second * first) * m.frame = m.frame * (m.publicMatrix second * m.publicMatrix first) := by
    rw [Matrix.mul_assoc, (m.clean_iff first).mp hFirst, ← Matrix.mul_assoc,
      (m.clean_iff second).mp hSecond, Matrix.mul_assoc]
  have publicAction := publicMatrix_of_action action
  exact ⟨(m.clean_iff _).mpr (publicAction ▸ action), publicAction⟩

private theorem mul_basisFrame_apply {H I : Type} [Fintype H] [DecidableEq H]
    (embed : I ↪ H) (u : Matrix H H ℂ) (row : H) (col : I) :
    (u * basisFrame embed) row col = u row (embed col) := by
  simp [Matrix.mul_apply, basisFrame, mul_ite]

private theorem basisFrame_mul_apply {H I : Type} [Fintype I] [DecidableEq H] [DecidableEq I]
    (embed : I ↪ H) (v : Matrix I I ℂ) (row col : I) :
    (basisFrame embed * v) (embed row) col = v row col := by
  simp [Matrix.mul_apply, basisFrame, ite_mul, embed.injective.eq_iff]

private theorem basisFrame_mul_off_range {H I : Type} [Fintype I] [DecidableEq H]
    (embed : I ↪ H) (v : Matrix I I ℂ) {row : H} (col : I)
    (off : ∀ bit, row ≠ embed bit) : (basisFrame embed * v) row col = 0 := by
  simp [Matrix.mul_apply, basisFrame, off]

/-- A clean exit is equivalent to having zero transition amplitudes from any
zero-initialized input to every basis state with dirty workspace. -/
theorem ScopedModule.clean_iff_zero_off_frame (m : ScopedModule) (u : WireMatrix m.width) :
    let embed := appendZero m.publicWires m.localWires
    m.Clean u ↔ ∀ row col, (∀ input, row ≠ embed input) → u row (embed col) = 0 := by
  let embed := appendZero m.publicWires m.localWires
  change m.Clean u ↔ ∀ row col, (∀ input, row ≠ embed input) → u row (embed col) = 0
  rw [m.clean_iff]
  change u * basisFrame embed = basisFrame embed * compress (basisFrame embed) u (basisFrame embed) ↔ _
  constructor
  · intro action row col off
    have coefficient := congrFun (congrFun action row) col
    rw [mul_basisFrame_apply, basisFrame_mul_off_range embed _ col off] at coefficient
    exact coefficient
  · intro zeros
    ext row col
    rw [mul_basisFrame_apply]
    by_cases inside : ∃ input, row = embed input
    · obtain ⟨input, rfl⟩ := inside
      rw [basisFrame_mul_apply, basisFrame_compress]
    · have off : ∀ input, row ≠ embed input := fun input equality => inside ⟨input, equality⟩
      rw [basisFrame_mul_off_range embed _ col off]
      exact zeros row col off

/-- Coherent control preserves a clean exit and restricts the guard to the zero frame. -/
theorem ScopedModule.clean_controlled {m : ScopedModule} {u : WireMatrix m.width}
    (clean : m.Clean u) (active : Reg m.width → Prop) :
    let onEntry := fun bit => active (appendZero m.publicWires m.localWires bit)
    m.Clean (controlledMatrix active u) ∧
      m.publicMatrix (controlledMatrix active u) = controlledMatrix onEntry (m.publicMatrix u) := by
  classical
  let embed := appendZero m.publicWires m.localWires
  let v := m.publicMatrix u
  let onEntry := fun bit => active (embed bit)
  change m.Clean (controlledMatrix active u) ∧
    m.publicMatrix (controlledMatrix active u) = controlledMatrix onEntry v
  have oldAction : u * basisFrame embed = basisFrame embed * v := (m.clean_iff u).mp clean
  have action : controlledMatrix active u * basisFrame embed =
      basisFrame embed * controlledMatrix onEntry v := by
    ext row col
    rw [mul_basisFrame_apply]
    by_cases inside : ∃ bit, row = embed bit
    · obtain ⟨bit, rfl⟩ := inside
      rw [basisFrame_mul_apply]
      have same := congrFun (congrFun oldAction (embed bit)) col
      rw [mul_basisFrame_apply, basisFrame_mul_apply] at same
      simp [controlledMatrix, onEntry, same, Matrix.one_apply, embed.injective.eq_iff]
    · have off : ∀ bit, row ≠ embed bit := fun bit equality => inside ⟨bit, equality⟩
      rw [basisFrame_mul_off_range embed _ col off]
      have zero := congrFun (congrFun oldAction row) col
      rw [mul_basisFrame_apply, basisFrame_mul_off_range embed _ col off] at zero
      simp [controlledMatrix, zero, off col]
  have publicAction := publicMatrix_of_action (m := m) action
  exact ⟨(m.clean_iff _).mpr (publicAction ▸ action), publicAction⟩

/-- Kernel evidence that a resolved body admits a clean unitary module exit. -/
structure ScopedModule.Certificate (m : ScopedModule) (snapshot : Snapshot)
    (oracle : Oracle m.width) (u : WireMatrix m.width) : Prop where
  body : m.bodyMatrix snapshot oracle = .ok u
  unitary : u ∈ Matrix.unitaryGroup (Reg m.width) ℂ
  clean : m.Clean u

theorem ScopedModule.Certificate.sound {m : ScopedModule} {snapshot : Snapshot}
    {oracle : Oracle m.width} {u : WireMatrix m.width}
    (certificate : m.Certificate snapshot oracle u) :
    u * m.frame = m.frame * m.publicMatrix u ∧
      m.publicMatrix u ∈ Matrix.unitaryGroup (Reg m.publicWires) ℂ :=
  ⟨(m.clean_iff u).mp certificate.clean, m.publicMatrix_unitary certificate.unitary certificate.clean⟩

end OracqVerify.RIR
