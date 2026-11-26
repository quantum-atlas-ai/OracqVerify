module

public import OracqVerify.RIR.ScopedPlacement
public import OracqVerify.RIR.GateAction
public import OracqVerify.RIR.QRAMRotation

/-! Executable basis permutations with proofs relating them to the exact RIR matrices. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Matrix Qatlib.Foundations.PureStateMath
open scoped Matrix

abbrev BasisWord (n : Nat) := Vector Bool n

namespace BasisWord

def readBit {n : Nat} (x : BasisWord n) (i : Fin n) : Bool := x[i]

def basis (n : Nat) : BasisWord n ≃ Reg n where
  toFun x := x.readBit
  invFun := Vector.ofFn
  left_inv x := by ext i hi; simp [readBit]
  right_inv x := by funext i; simp [readBit]

def readView {n k : Nat} (view : View n k) (x : BasisWord n) : BasisWord k :=
  Vector.ofFn fun i => x.readBit (view i)

@[simp] theorem readView_bit {n k : Nat} (view : View n k) (x : BasisWord n) (i : Fin k) :
    (readView view x).readBit i = x.readBit (view i) := by
  simp [readView, readBit]

def writeBits {n k : Nat} (view : View n k) (word : BasisWord k)
    (state : BasisWord n) (positions : List (Fin k)) : BasisWord n :=
  positions.foldl (fun result i => result.set (view i).val (word.readBit i) (view i).isLt) state

private theorem writeBits_other {n k : Nat} (view : View n k) (word : BasisWord k)
    (positions : List (Fin k)) (state : BasisWord n) (wire : Fin n)
    (apart : ∀ i ∈ positions, view i ≠ wire) :
    (writeBits view word state positions).readBit wire = state.readBit wire := by
  induction positions generalizing state with
  | nil => rfl
  | cons i rest ih =>
    simp only [writeBits, List.foldl_cons]
    rw [← writeBits]
    rw [ih _ (fun j hj => apart j (List.mem_cons_of_mem _ hj))]
    have different : (view i).val ≠ wire.val := fun h => apart i (by simp) (Fin.ext h)
    simp [readBit, different]

private theorem writeBits_on {n k : Nat} (view : View n k) (word : BasisWord k)
    (positions : List (Fin k)) (state : BasisWord n) (wire : Fin k)
    (present : wire ∈ positions) :
    (writeBits view word state positions).readBit (view wire) = word.readBit wire := by
  induction positions generalizing state with
  | nil => contradiction
  | cons i rest ih =>
    simp only [writeBits, List.foldl_cons]
    rw [← writeBits]
    by_cases tail : wire ∈ rest
    · exact ih _ tail
    · have same : wire = i := (List.mem_cons.mp present).resolve_right tail
      subst i
      rw [writeBits_other view word rest _ (view wire)]
      · simp [readBit]
      · intro j hj equal
        exact tail (view.injective equal ▸ hj)

/-- Write an ordered view while preserving every spectator wire. -/
def writeView {n k : Nat} (view : View n k) (word : BasisWord k)
    (state : BasisWord n) : BasisWord n :=
  writeBits view word state (List.finRange k)

@[simp] theorem writeView_bit {n k : Nat} (view : View n k) (word : BasisWord k)
    (state : BasisWord n) (i : Fin k) :
    (writeView view word state).readBit (view i) = word.readBit i :=
  writeBits_on _ _ _ _ _ (List.mem_finRange i)

theorem writeView_other {n k : Nat} (view : View n k) (word : BasisWord k)
    (state : BasisWord n) (wire : Fin n) (apart : ∀ i, view i ≠ wire) :
    (writeView view word state).readBit wire = state.readBit wire :=
  writeBits_other _ _ _ _ _ (fun i _ => apart i)

@[simp] theorem read_write {n k : Nat} (v : View n k) (word : BasisWord k) (state : BasisWord n) :
    readView v (writeView v word state) = word := by
  ext i hi
  exact (readView_bit ..).trans (writeView_bit v word state ⟨i, hi⟩)

@[simp] theorem write_read {n k : Nat} (v : View n k) (state : BasisWord n) :
    writeView v (readView v state) state = state := by
  apply (basis n).injective
  funext wire
  change (writeView v (readView v state) state).readBit wire = state.readBit wire
  by_cases h : ∃ i, v i = wire
  · obtain ⟨i, rfl⟩ := h
    rw [writeView_bit, readView_bit]
  · exact writeView_other _ _ _ _ (fun i h' => h ⟨i, h'⟩)

@[simp] theorem write_write {n k : Nat} (v : View n k) (first second : BasisWord k)
    (state : BasisWord n) :
    writeView v second (writeView v first state) = writeView v second state := by
  apply (basis n).injective
  funext wire
  change (writeView v second (writeView v first state)).readBit wire =
    (writeView v second state).readBit wire
  by_cases h : ∃ i, v i = wire
  · obtain ⟨i, rfl⟩ := h
    rw [writeView_bit, writeView_bit]
  · have other : ∀ i, v i ≠ wire := fun i same => h ⟨i, same⟩
    simp only [writeView_other _ _ _ _ other]

/-- Apply a reversible update to the selected wires, retaining all spectators. -/
def place {n k : Nat} (view : View n k) (gate : BasisWord k ≃ BasisWord k) :
    BasisWord n ≃ BasisWord n where
  toFun state := writeView view (gate (readView view state)) state
  invFun state := writeView view (gate.symm (readView view state)) state
  left_inv state := by simp
  right_inv state := by simp

def load {n a d : Nat} (address : View n a) (data : View n d)
    (bank : ReadOnlyQRAM.Bank a d) (apart : DisjointViews address data) :
    BasisWord n ≃ BasisWord n := by
  let step (state : BasisWord n) :=
    writeView data (Vector.ofFn fun j =>
      xor (state.readBit (data j)) (bank (state.readBit ∘ address) j)) state
  have inverse : Function.Involutive step := by
    intro state
    have sameAddress : (step state).readBit ∘ address = state.readBit ∘ address := by
      funext i
      exact writeView_other _ _ _ _ (fun j => (apart i j).symm)
    apply (basis n).injective
    funext wire
    change (step (step state)).readBit wire = state.readBit wire
    by_cases h : ∃ i, data i = wire
    · obtain ⟨i, rfl⟩ := h
      have onData (s : BasisWord n) :
          (step s).readBit (data i) = xor (s.readBit (data i)) (bank (s.readBit ∘ address) i) := by
        rw [show (step s).readBit (data i) =
          (writeView data _ s).readBit (data i) from rfl, writeView_bit]
        simp [readBit]
      rw [onData, sameAddress, onData]
      cases state.readBit (data i) <;> cases bank (state.readBit ∘ address) i <;> rfl
    · have other : ∀ i, data i ≠ wire := fun i same => h ⟨i, same⟩
      change (writeView data _ (writeView data _ state)).readBit wire = _
      simp only [writeView_other _ _ _ _ other]
  exact ⟨step, step, inverse, inverse⟩

def add {n k : Nat} (view : View n k) (amount : BitVec k) : BasisWord n ≃ BasisWord n :=
  let packed := (basis k).trans (unsignedWord k)
  let arithmetic : BitVec k ≃ BitVec k :=
    ⟨fun x => x + amount, fun x => x - amount,
      fun x => BitVec.add_sub_cancel x amount, fun x => BitVec.sub_add_cancel x amount⟩
  place view (packed.trans (arithmetic.trans packed.symm))

/-- View of one wire used for a basis flip. -/
def oneWire {n : Nat} (wire : Fin n) : View n 1 :=
  ⟨fun _ => wire, fun _ _ _ => Subsingleton.elim _ _⟩

def flip {n : Nat} (wire : Fin n) : BasisWord n ≃ BasisWord n :=
  place (oneWire wire)
    ⟨fun state => Vector.ofFn fun i => !state.readBit i,
      fun state => Vector.ofFn fun i => !state.readBit i,
      by
        intro state
        ext i hi
        have zero : i = 0 := by omega
        subst i
        simp [readBit],
      by
        intro state
        ext i hi
        have zero : i = 0 := by omega
        subst i
        simp [readBit]⟩

def perm {n : Nat} (action : BasisWord n ≃ BasisWord n) : Reg n ≃ Reg n :=
  (basis n).symm.trans (action.trans (basis n))

noncomputable def matrix {n : Nat} (action : BasisWord n ≃ BasisWord n) : WireMatrix n :=
  permMatrix (perm action)

theorem matrix_load {n a d : Nat} (address : View n a) (data : View n d)
    (bank : ReadOnlyQRAM.Bank a d) (apart : DisjointViews address data) :
    matrix (load address data bank apart) = permMatrix (loadAtBasis address data bank) := by
  apply congrArg (fun f : Reg n → Reg n => permMatrix f)
  funext state wire
  let input := (basis n).symm state
  have bits : input.readBit = state := (basis n).apply_symm_apply state
  by_cases h : ∃ i, data i = wire
  · obtain ⟨i, rfl⟩ := h
    rw [loadAt_data]
    change (writeView data (Vector.ofFn _) input).readBit (data i) = _
    rw [writeView_bit]
    simpa [readBit, ReadOnlyQRAM.loadBasis] using
      congrArg (fun state : Reg n => xor (state (data i)) (bank (state ∘ address) i)) bits
  · have apart' : ∀ i, data i ≠ wire := fun i same => h ⟨i, same⟩
    rw [loadAt_other _ _ _ _ _ h]
    change (writeView data _ input).readBit wire = _
    rw [writeView_other _ _ _ _ apart', bits]

end BasisWord
end OracqVerify.RIR
