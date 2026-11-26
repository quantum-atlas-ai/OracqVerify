module

public import OracqVerify.Verification.WideGrover
public import OracqVerify.Verification.Grover

/-! Check the submitted wide caller and one independently bound provider. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.Verification.WideGrover

open OracqVerify.RIR Lean Matrix Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

abbrev Implementation := Grover.Implementation

def entryName : String := "grover_wide"
def slotName : String := "grover_wide_mark"

def entryBank (n : Nat) : Resource := ⟨"marks", ⟨n, 1⟩⟩
def passedBank (n : Nat) (name : String) : Resource := ⟨name, ⟨n, 1⟩⟩
def lookupBank (n : Nat) : Resource := ⟨"lookup", ⟨n, 1⟩⟩

def banks (impl : Implementation) (bank : Resource) : List Resource :=
  if impl.isQram then [bank] else []

def plan (impl : Implementation) (n : Nat) : ScopedCapturePlan :=
  if impl.isQram then [(entryName, [(slotName, [.captured (entryBank n)])])] else []

def qramWord (n : Nat) : List ResolvedInstruction :=
  let load := ResolvedInstruction.load (lookupBank n) (List.range n) [n]
  [load, .unary .z [n], load]

def provider (w : Nat) (impl : Implementation) : ScopedModule :=
  let n := w+1
  ⟨if impl.isQram then "wide_mark_qram" else "wide_mark_gate", n, Grover.peak impl,
    banks impl (lookupBank n),
    some (if impl.isQram then qramWord n else [prefixPhase (Fin.last w)]),
    Grover.peak impl, true, true⟩

def wrapper (w : Nat) (impl : Implementation) (passed : String) : ScopedModule :=
  let n := w+1
  let handles := banks impl (passedBank n passed)
  ⟨slotName, n, 0, handles,
    some [.query (provider w impl).name [List.range n] handles], Grover.peak impl, true, true⟩

def entry (n k : Nat) (impl : Implementation) : ScopedModule :=
  let handles := banks impl (entryBank n)
  ⟨entryName, n, 0, handles, some (caller n handles k), Grover.peak impl, true, true⟩

def openGraph (n k : Nat) : ScopedProgram :=
  ⟨entryName, [⟨slotName, n, 0, [], none, 0, true, true⟩, entry n k .gate], n, 0⟩

def closedGraph (w k : Nat) (impl : Implementation) (passed : String) : ScopedProgram :=
  ⟨entryName, [provider w impl, wrapper w impl passed, entry (w+1) k impl],
    w+1, Grover.peak impl⟩

def singletonImage (w : Nat) : BankImage (w+1) 1 where
  words := Vector.ofFn fun i => if i = orderedBitsIndex (w+1) (target w) then 1 else 0
  fits := by intro i; simp only [Vector.getElem_ofFn]; split <;> decide

private theorem zero_index (n : Nat) :
    (orderedBitsIndex n (ZeroStr n)).val = 0 := by
  induction n with
  | zero =>
    have h := (orderedBitsIndex 0 (ZeroStr 0)).isLt
    change (orderedBitsIndex 0 (ZeroStr 0)).val < 1 at h
    omega
  | succ n ih =>
    rw [orderedBitsIndex_succ]
    have zero : (fun i : Fin n => ZeroStr (n+1) i.castSucc) = ZeroStr n := rfl
    rw [zero, ih]
    rfl

theorem target_index (w : Nat) : (orderedBitsIndex (w+1) (target w)).val = 2^w := by
  rw [orderedBitsIndex_succ]
  have zero : (fun i : Fin w => target w i.castSucc) = ZeroStr w := by
    funext i
    have earlier : i.castSucc < Fin.last w := i.isLt
    simp [target, ne_of_lt earlier, ZeroStr]
  rw [zero, zero_index]
  simp [target]

private theorem image_reads (w : Nat) (address : Reg (w+1)) :
    (singletonImage w).bank address 0 = decide (address = target w) := by
  by_cases same : address = target w
  · subst address
    simp only [BankImage.bank, singletonImage, Vector.getElem_ofFn, ite_true, decide_true]
    exact (show (orderedBitsIndex 1).symm (1 : Fin 2) 0 = true by decide)
  · have diff := (orderedBitsIndex (w+1)).injective.ne same
    simp only [BankImage.bank, singletonImage, Vector.getElem_ofFn, ite_eq_right diff, decide_eq_false same]
    exact (show (orderedBitsIndex 1).symm (0 : Fin 2) 0 = false by decide)

private theorem ofWires_singleton {n : Nat} (i : Fin n) :
    View.ofWires n 1 [i.val] = .ok ⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩ := by
  unfold View.ofWires
  simp [i.isLt, Pure.pure, Except.pure]

private def readAt (n : Nat) : ResolvedRead (n+1) where
  bank := lookupBank n
  address := prefixView (Nat.le_succ n)
  data := (⟨fun _ => Fin.last n, fun a b _ => Subsingleton.elim a b⟩ : View (n+1) 1)
  disjoint a _ equal := (Nat.ne_of_lt a.isLt) (congrArg Fin.val equal)

private theorem readAt_decoded (n : Nat) :
    ResolvedRead.create (n+1) (lookupBank n) (List.range n) [n] = .ok (readAt n) := by
  let a : View (n+1) n := prefixView (Nat.le_succ n)
  let d : View (n+1) 1 := ⟨fun _ => Fin.last n, fun x y _ => Subsingleton.elim x y⟩
  have address : View.ofWires (n+1) n (List.range n) = .ok a :=
    view_range (Nat.le_succ n)
  have data : View.ofWires (n+1) 1 [n] = .ok d :=
    ofWires_singleton (Fin.last n)
  unfold ResolvedRead.create
  change (do
    let a ← View.ofWires (n+1) n (List.range n)
    let d ← View.ofWires (n+1) 1 [n]
    if hp : ∀ i j, a i ≠ d j then pure (⟨lookupBank n, a, d, hp⟩ : ResolvedRead (n+1))
    else throw "QRAM address and data views overlap") = _
  rw [address, data]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  have apart : ∀ i : Fin n, ∀ j : Fin 1, a i ≠ d j :=
    (readAt n).disjoint
  rw [dite_eq_left apart]
  rfl

private theorem provider_gate (w : Nat) (memory : Snapshot) :
    (provider w .gate).interpret [] memory = .ok (oraclePhase (target w)) := by
  apply ScopedModule.interpret_zero_locals _ _ _ _ _ _ _ _ _ (oraclePhase_unitary _)
  change evalWord (w+1) memory (ScopedEnvironment.atCall [] (w+1) memory)
    [prefixPhase (Fin.last w)] = _
  simp [evalWord, gate_matrix, List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure,
    Except.map, wordMatrix]

private theorem provider_qram (w : Nat) (memory : Snapshot)
    (supplied : memory (lookupBank (w+1)) = some (singletonImage w).bank) :
    (provider w .qram).interpret [] memory = .ok (oraclePhase (target w)) := by
  let n := w+1
  have executed := scopedQramPhase_interpret (provider w .qram) (readAt n) (List.range n) [n]
    (readAt_decoded n) (0 : Fin 1) (0 : Fin 1) rfl rfl [] memory (singletonImage w).bank supplied
  rw [executed, Except.ok.injEq]
  unfold oraclePhase
  congr 1
  funext address
  change Reg n at address
  have whole : ((appendZero n 1 address) ∘ prefixView (Nat.le_succ n)) = address := by
    funext i
    exact appendZero_public address i
  let : Decidable (address = target w) := Fintype.decidablePiFintype address (target w)
  change (if (singletonImage w).bank ((appendZero n 1 address) ∘ prefixView (Nat.le_succ n)) 0
      then (-1 : ℂ) else 1) = if address = target w then -1 else 1
  rw [whole, image_reads]
  simp

private def snapshotOf (handle : Resource)
    (value : ReadOnlyQRAM.Bank handle.type.addressWidth handle.type.dataWidth) : Snapshot :=
  fun r => if h : handle = r then some (h ▸ value) else none

private theorem snapshotOf_at (handle : Resource)
    (value : ReadOnlyQRAM.Bank handle.type.addressWidth handle.type.dataWidth) :
    snapshotOf handle value handle = some value := by simp [snapshotOf]

private theorem forwarded {formal actual : Resource} (shape : formal.type = actual.type)
    (memory : Snapshot) (value : ReadOnlyQRAM.Bank actual.type.addressWidth actual.type.dataWidth)
    (found : memory actual = some value) :
    memory.forward [formal] [actual] = .ok (snapshotOf formal (shape.symm ▸ value)) := by
  unfold Snapshot.forward
  simp only [List.map_cons, List.map_nil, shape, ite_true]
  congr 1
  funext r
  by_cases eq : formal = r
  · subst r
    simp [snapshotOf, shape, found, Eq.symm]
    cases formal with
    | mk formalName formalType =>
      cases actual with
      | mk actualName actualType =>
        change formalType = actualType at shape
        subst actualType
        rfl
  · simp [snapshotOf, eq]

private theorem wholeCall {n : Nat} {environment : ScopedEnvironment} {name : String}
    {formals actuals : List Resource} {denote : Snapshot → Except String (WireMatrix n)}
    {memory child : Snapshot} {u : WireMatrix n}
    (found : lookup environment name "scoped callee" = .ok ⟨n, formals, denote⟩)
    (rebased : memory.forward formals actuals = .ok child) (computed : denote child = .ok u) :
    environment.atCall n memory ⟨name, [List.range n], actuals⟩ = .ok u := by
  unfold ScopedEnvironment.atCall
  simp [found, Bind.bind, Except.bind, View.ofWires_range, rebased, computed,
    Pure.pure, Except.pure, View.placeMatrix_refl]

private theorem wrapper_matrix (w : Nat) (impl : Implementation) (passed : String) (memory : Snapshot)
    (supplied : impl = .qram → memory (passedBank (w+1) passed) = some (singletonImage w).bank) :
    (wrapper w impl passed).interpret (scopedEnvironment [provider w impl] [] unboundScopedOracle) memory =
      .ok (oraclePhase (target w)) := by
  let n := w+1
  let known := scopedEnvironment [provider w impl] [] unboundScopedOracle
  have found : lookup known (provider w impl).name "scoped callee" =
      .ok ⟨n, (provider w impl).banks, (provider w impl).interpret []⟩ := by
    cases impl <;> rfl
  have called : known.atCall n memory ⟨(provider w impl).name,
      [List.range n], banks impl (passedBank n passed)⟩ = .ok (oraclePhase (target w)) := by
    cases impl with
    | gate => exact wholeCall found (child := emptySnapshot) rfl (provider_gate w _)
    | qram =>
      apply wholeCall found (forwarded (formal := lookupBank n) (actual := passedBank n passed)
        rfl _ _ (supplied rfl))
      exact provider_qram w _ (snapshotOf_at _ _)
  apply ScopedModule.interpret_zero_locals _ _ _ _ _ _ _ _ _ (oraclePhase_unitary _)
  change evalWord n memory (known.atCall n memory)
    [.query (provider w impl).name [List.range n] (banks impl (passedBank n passed))] = _
  simp [evalWord, ResolvedInstruction.matrixWith, called, List.mapM_cons, Bind.bind, Except.bind,
    Pure.pure, Except.pure, Except.map, wordMatrix]

private theorem entry_interpret (n k : Nat) (impl : Implementation) (marked : Reg n)
    (known : ScopedEnvironment) (s : Snapshot)
    (called : known.atCall n s ⟨slotName, [List.range n], banks impl (entryBank n)⟩ =
      .ok (oraclePhase marked)) :
    (entry n k impl).interpret known s = .ok (iterate marked k) := by
  apply ScopedModule.interpret_zero_locals _ _ _ _ _ _ _ _ _ (iterate_unitary _ _)
  exact caller_matrix s (known.atCall n s) _ _ k called

/-- The same open caller can be proved once for every supplied singleton oracle. -/
theorem open_matrix (n k : Nat) (s : Snapshot) (marked : Reg n) :
    let ideal : ScopedOracle := fun name width _ =>
      if eq : n = width then
        if name = slotName then .ok (eq ▸ oraclePhase marked) else .error "Wrong slot"
      else .error "Wrong slot width"
    (openGraph n k).matrixWith s [slotName] ideal = .ok (iterate marked k) := by
  dsimp only
  let ideal : ScopedOracle := fun name width _ =>
    if eq : n = width then
      if name = slotName then .ok (eq ▸ oraclePhase marked) else .error "Wrong slot"
    else .error "Wrong slot width"
  let slot : ScopedModule := ⟨slotName, n, 0, [], none, 0, true, true⟩
  let known := scopedEnvironment [slot] [slotName] ideal
  have found : lookup known slotName "scoped callee" = .ok ⟨n, [], ideal slotName n⟩ := rfl
  have called : known.atCall n s ⟨slotName, [List.range n], []⟩ = .ok (oraclePhase marked) :=
    wholeCall found (child := emptySnapshot) rfl (by simp [ideal])
  have interpreted := entry_interpret n k .gate marked known s called
  have root : lookup (scopedEnvironment (openGraph n k).modules [slotName] ideal)
      entryName "scoped entry" = .ok ⟨n, [], (entry n k .gate).interpret known⟩ := rfl
  change (do
    let definition ← lookup (scopedEnvironment (openGraph n k).modules [slotName] ideal)
      entryName "scoped entry"
    if width : definition.publicWires = n then
      return width ▸ (← definition.apply s)
    else throw "Scoped entry width mismatch") = _
  rw [root]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, interpreted]
  rfl

private theorem closed_matrix (w k : Nat) (impl : Implementation) (passed : String)
    (memory : Snapshot)
    (supplied : impl = .qram → memory (entryBank (w+1)) = some (singletonImage w).bank) :
    (closedGraph w k impl passed).matrixWith memory = .ok (iterate (target w) k) := by
  let n := w+1
  let parents := scopedEnvironment [provider w impl] [] unboundScopedOracle
  let known := scopedEnvironment [provider w impl, wrapper w impl passed] [] unboundScopedOracle
  have found : lookup known slotName "scoped callee" =
      .ok ⟨n, banks impl (passedBank n passed), (wrapper w impl passed).interpret parents⟩ := by
    cases impl <;> rfl
  have called : known.atCall n memory ⟨slotName, [List.range n], banks impl (entryBank n)⟩ =
      .ok (oraclePhase (target w)) := by
    cases impl with
    | gate =>
      exact wholeCall found (child := emptySnapshot) rfl
        (wrapper_matrix w .gate passed _ (by intro eq; cases eq))
    | qram =>
      apply wholeCall found (forwarded (formal := passedBank n passed) (actual := entryBank n)
        rfl _ _ (supplied rfl))
      exact wrapper_matrix w .qram passed _ (fun _ => snapshotOf_at _ _)
  have interpreted := entry_interpret n k impl (target w) known memory called
  have root : lookup (scopedEnvironment (closedGraph w k impl passed).modules [] unboundScopedOracle)
      entryName "scoped entry" = .ok ⟨n, banks impl (entryBank n), (entry n k impl).interpret known⟩ := by
    cases impl <;> rfl
  change (do
    let definition ← lookup (scopedEnvironment (closedGraph w k impl passed).modules [] unboundScopedOracle)
      entryName "scoped entry"
    if width : definition.publicWires = n then
      return width ▸ (← definition.apply memory)
    else throw "Scoped entry width mismatch") = _
  rw [root]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, interpreted]
  rfl

structure Certificate (original bound : Program) (image : Json) (w k : Nat) (impl : Implementation) where
  link : ScopedSourceLink original bound (plan impl (w+1))
  caller : link.caller = openGraph (w+1) k
  passed : String
  closed : link.closed = closedGraph w k impl passed
  table : impl = .qram → BankImage.decode (entryBank (w+1)) image = .ok (singletonImage w)

theorem bankImage_eq_of_words {a d : Nat} (first second : BankImage a d)
    (words : first.words = second.words) : first = second := by
  cases first
  cases second
  cases words
  rfl

def certify (original bound : Program) (image : Json) (w k : Nat) (impl : Implementation) :
    Except String (Certificate original bound image w k impl) := do
  let link ← verifyScopedSourceLink original bound (plan impl (w+1))
  unless 0 < k do throw "Grover requires a positive iteration count"
  if caller : link.caller = openGraph (w+1) k then
    let passed ← if impl.isQram then do
      let wrap ← lookup (link.closed.modules.map fun m => (m.name, m)) slotName "slot"
      let [handle] := wrap.banks | throw "Grover expects one forwarded bank"
      pure handle.name
    else pure ""
    if closed : link.closed = closedGraph w k impl passed then
      match which : impl with
      | .gate => return ⟨link, caller, passed, closed, fun h => by rw [which] at h; cases h⟩
      | .qram =>
        match decoded : BankImage.decode (entryBank (w+1)) image with
        | .error reason => throw reason
        | .ok table =>
          if words : table.words.toArray = (singletonImage w).words.toArray then
            have value := bankImage_eq_of_words table (singletonImage w) (Vector.toArray_inj.mp words)
            return ⟨link, caller, passed, closed, fun _ => decoded.trans (congrArg Except.ok value)⟩
          else throw "Grover expects the requested singleton mark"
    else throw "Unexpected wide Grover bound caller or provider"
  else throw "Unexpected wide Grover open caller"

theorem Certificate.sound {original bound : Program} {image : Json} {w k : Nat} {impl : Implementation}
    (cert : Certificate original bound image w k impl) :
    ∃ memory, cert.link.closed.decodeSnapshot image = .ok memory ∧
      bound.scopedMatrix memory = .ok ⟨w+1, iterate (target w) k⟩ := by
  rw [cert.closed]
  have evaluated (memory : Snapshot)
      (supplied : impl = .qram → memory (entryBank (w+1)) = some (singletonImage w).bank) :
      bound.scopedMatrix memory = .ok ⟨w+1, iterate (target w) k⟩ := by
    have resolved := cert.link.bound_resolved
    rw [cert.closed] at resolved
    exact Program.scopedMatrix_of_resolved resolved (closed_matrix w k impl cert.passed memory supplied)
  cases impl with
  | gate =>
    exact ⟨emptySnapshot, rfl, evaluated emptySnapshot (by intro eq; cases eq)⟩
  | qram =>
    let memory := snapshotOf (entryBank (w+1)) (singletonImage w).bank
    refine ⟨memory, ?_, evaluated memory (fun _ => snapshotOf_at _ _)⟩
    unfold ScopedProgram.decodeSnapshot
    have found : lookup ((closedGraph w k .qram cert.passed).modules.map fun m => (m.name, m))
        entryName "scoped entry" = .ok (entry (w+1) k .qram) := rfl
    simp [closedGraph, Bind.bind, Except.bind, Pure.pure, Except.pure] at found ⊢
    rw [found]
    simp [entry, banks, cert.table rfl, memory, List.mapM_cons, Bind.bind,
      Except.bind, Pure.pure, Except.pure]
    rfl

theorem Certificate.probability {original bound : Program} {image : Json} {w k : Nat}
    {impl : Implementation} (cert : Certificate original bound image w k impl) :
    let θ := Real.arcsin ((Real.sqrt ((2 : ℝ) ^ (w+1)))⁻¹)
    ∃ (memory : Snapshot) (u : WireMatrix (w+1)),
      cert.link.closed.decodeSnapshot image = .ok memory ∧
      bound.scopedMatrix memory = .ok ⟨w+1, u⟩ ∧
      MeasureProb (u *ᵥ Ket (ZeroStr (w+1))) {target w} =
        (Real.sin ((2 * (k : ℝ) + 1) * θ)) ^ 2 := by
  obtain ⟨memory, decoded, matrix⟩ := cert.sound
  exact ⟨memory, iterate (target w) k, decoded, matrix, successProbability (Nat.succ_pos w) (target w) k⟩

end OracqVerify.Verification.WideGrover
