module

public import OracqVerify.Verification.ReversibleFrame
public import OracqVerify.RIR.BlockEncoding

/-! An exact sparse success block with interchangeable reversible and QRAM flags. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.SparseBlock

open Lean RIR Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.Execution.WorkspaceCP
open scoped Matrix.Norms.L2Operator

def action (x : Reg 3) : Reg 3 := ![!x 0, x 1, xor (x 2) (x 1)]

def partner (x : Reg 2) : Reg 2 := ![!x 0, x 1]

/-- One undirected edge between addresses zero and one, with two isolated vertices. -/
noncomputable def adjacency : WireMatrix 2 := fun row col =>
  if col 1 = false then permMatrix partner row col else 0

def embed : Reg 2 ↪ Reg 3 where
  toFun x := ![x 0, x 1, false]
  inj' := by
    intro x y h
    apply funext
    intro i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 1

def plan (qram : Bool) : ScopedCapturePlan :=
  if qram then [("sparse_block", [("sparse_entry_flag", [.captured ⟨"edge_flags", ⟨2, 1⟩⟩])])]
  else []

def checkEntry (bound : Program) : Bool :=
  match lookupModule bound bound.entry with
  | .error _ => false
  | .ok entry =>
    entry.registers == [⟨"target", ⟨.bits, 2⟩⟩, ⟨"signal", ⟨.bits, 1⟩⟩] &&
      entry.attributes.lookup "be_alpha" == some (toJson (1 : Nat))

structure Replacement (caller bound : Program) (image : Json) (qram : Bool) where
  link : ScopedSourceLink caller bound (plan qram)
  frame : ReversibleFrame.Certificate bound image 3
  interface : checkEntry bound = true
  width : frame.graph.entryWires = 3
  checks : ∀ x : Reg 3, (width ▸ BasisWord.perm frame.gate.action (width.symm ▸ x) : Reg 3) = action x

def checkReplacement (caller bound : Program) (image : Json) (qram : Bool) :
    Except String (Replacement caller bound image qram) := do
  let link ← verifyScopedSourceLink caller bound (plan qram)
  let frame ← ReversibleFrame.certify bound image 3
  if interface : checkEntry bound then
    if width : frame.graph.entryWires = 3 then
      if checks : ∀ x : Reg 3,
          (width ▸ BasisWord.perm frame.gate.action (width.symm ▸ x) : Reg 3) = action x then
        return ⟨link, frame, interface, width, checks⟩
      else throw "The sparse block permutation does not match the specified edge flag"
    else throw "Expected the sparse block to have three public wires"
  else throw "Expected a two-wire target, one signal wire, and unit normalization"

private theorem matrix_eq {n : Nat} (gate : ReversibleGate n) (width : n = 3)
    (checks : ∀ x : Reg 3, (width ▸ BasisWord.perm gate.action (width.symm ▸ x) : Reg 3) = action x) :
    (width ▸ gate.matrix : WireMatrix 3) = permMatrix action := by
  subst n
  exact congrArg permMatrix (funext checks)

private theorem unitary {n : Nat} (gate : ReversibleGate n) (width : n = 3) :
    (width ▸ gate.matrix : WireMatrix 3) ∈ unitaryGroup (Reg 3) ℂ := by
  subst n
  exact BasisWord.matrix_unitary gate.action

private theorem compress_action :
    compress (basisFrame embed) (permMatrix action) (basisFrame embed) = adjacency := by
  ext row col
  rw [basisFrame_compress]
  unfold adjacency permMatrix
  have address : embed row = action (embed col) ↔ row = partner col ∧ col 1 = false := by
    constructor
    · intro h
      refine ⟨funext (Fin.forall_fin_two.mpr ⟨congrFun h 0, congrFun h 1⟩), ?_⟩
      have flag := congrFun h 2
      cases value : col 1 <;> simp [embed, action, value] at flag ⊢
    · rintro ⟨rfl, clean⟩
      funext i
      fin_cases i <;> simp [embed, action, partner, clean]
  simp only [Matrix.of_apply, address]
  by_cases flag : col 1 = false <;> simp [flag]

theorem Replacement.sound {caller bound : Program} {image : Json} {qram : Bool}
    (cert : Replacement caller bound image qram) :
    bound.scopedMatrix cert.frame.snapshot = .ok ⟨3, permMatrix action⟩ ∧
      BlockEncoding adjacency (permMatrix action) (basisFrame embed) (basisFrame embed) 1 0 := by
  have hm := matrix_eq cert.frame.gate cert.width cert.checks
  have pack {n : Nat} (u : WireMatrix n) (width : n = 3) :
      (⟨n, u⟩ : Σ wires, WireMatrix wires) = ⟨3, width ▸ u⟩ := by subst n; rfl
  refine ⟨cert.frame.sound.trans (congrArg Except.ok ((pack cert.frame.gate.matrix cert.width).trans
    (congrArg (Sigma.mk (β := WireMatrix) 3) hm))), ?_⟩
  refine ⟨hm ▸ unitary cert.frame.gate cert.width, basisFrame_isIsometry _,
    basisFrame_isIsometry _, by norm_num, le_rfl, ?_⟩
  rw [compress_action, one_smul, sub_self, norm_zero]

end OracqVerify.Verification.SparseBlock
