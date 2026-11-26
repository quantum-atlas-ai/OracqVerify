module

public import OracqVerify.Verification.Grover
import all OracqVerify.RIR.ScopedResolve
import all OracqVerify.RIR.Resolve

/-! Proof-carrying generation and independent validation of the two-address-bit Grover caller. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Generators.Grover

open Lean RIR Qatlib.Foundations.PureStateMath
open scoped Matrix

abbrev Address := Fin 4

def address (value : Address) : Reg 2 := (orderedBitsIndex 2).symm value

def generate (target : Address) : Program :=
  let registers : List Register := [⟨"target", ⟨.bits, 2⟩⟩]
  let slot : RIR.Module :=
    ⟨"grover_mark", registers, [], none, [("oracle_paradigm", .str "phase_oracle")], []⟩
  let targetView := bitsRef "target" 2
  let low : Ref := ⟨⟨.bits, 1⟩, [⟨"target", 0, 1⟩]⟩
  let high : Ref := ⟨⟨.bits, 1⟩, [⟨"target", 1, 1⟩]⟩
  let caller : RIR.Module :=
    ⟨"grover_two_bits", registers, [], some
      [.unary .h targetView, .call slot.name [targetView] [], .unary .h targetView,
        .unary .z low, .unary .z high, .control low 1 [.unary .z high], .unary .h targetView],
      [("marked_address", toJson target.val)], []⟩
  ⟨caller.name, [slot, caller]⟩

def matchesMarkedAddress (target : Address) (program : Program) : Bool :=
  match lookupModule program program.entry with
  | .error _ => false
  | .ok root =>
    match root.attributes.lookup "marked_address" with
    | none => true
    | some (.num declared) => declared == JsonNumber.fromNat target.val
    | some _ => false

/-- The caller has the Grover matrix and reads out the marked address under its phase contract. -/
def Correct (target : Address) (program : Program) : Prop :=
  program.resolveScoped = .ok Verification.Grover.openGraph ∧
    matchesMarkedAddress target program = true ∧
    (∀ memory, Verification.Grover.openGraph.matrixWith memory ["grover_mark"]
      (Verification.Grover.phaseSpec (address target) (fun _ => True)) =
        .ok (Verification.Grover.iterateAt (address target))) ∧
    Verification.Grover.iterateAt (address target) *ᵥ Ket (ZeroStr 2) = Ket (address target)

theorem correct_of_resolved (target : Address) (program : Program)
    (resolved : program.resolveScoped = .ok Verification.Grover.openGraph)
    (marked : matchesMarkedAddress target program = true) : Correct target program :=
  ⟨resolved, marked, fun memory => Verification.Grover.open_matrix memory (address target),
    Verification.Grover.exact_readout_at (address target)⟩

theorem generate_correct (target : Address) : Correct target (generate target) := by
  apply correct_of_resolved
  · fin_cases target <;> cbv
  · fin_cases target <;> cbv

def check (target : Address) (program : Program) : Except String (Subtype fun _ : Unit => Correct target program) :=
  if resolved : program.resolveScoped = .ok Verification.Grover.openGraph then
    if marked : matchesMarkedAddress target program = true then
      .ok ⟨(), correct_of_resolved target program resolved marked⟩
    else .error "Declared Grover marked address disagrees with the parameter"
  else .error "Unexpected open Grover caller or slot interface"

end OracqVerify.Generators.Grover
