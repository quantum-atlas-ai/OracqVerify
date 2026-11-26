module

public import OracqVerify.RIR.QRAM
public import OracqVerify.RIR.ScopedResolve

/-! Decode dense, little-endian QRAM bank images at a scoped entry's declared shapes. -/

set_option warningAsError true

@[expose] public section

namespace OracqVerify.RIR

open Lean

structure BankImage (addressWidth dataWidth : Nat) where
  words : Vector Nat (2 ^ addressWidth)
  fits : ∀ address : Fin (2 ^ addressWidth), words[address.val] < 2 ^ dataWidth

def BankImage.bank {a d : Nat} (image : BankImage a d) : ReadOnlyQRAM.Bank a d :=
  fun address =>
    let index := orderedBitsIndex a address
    (orderedBitsIndex d).symm ⟨image.words[index.val], image.fits index⟩

def BankImage.decode (handle : Resource) (json : Json) :
    Except String (BankImage handle.type.addressWidth handle.type.dataWidth) := do
  let cells ← json.getObjValAs? (Array Nat) handle.name
  if size : cells.size = 2 ^ handle.type.addressWidth then
    let words : Vector Nat (2 ^ handle.type.addressWidth) := ⟨cells, size⟩
    if fits : ∀ address : Fin (2 ^ handle.type.addressWidth),
        words[address.val] < 2 ^ handle.type.dataWidth then
      return ⟨words, fits⟩
    else throw s!"Bank {handle.name} contains a word outside its data range"
  else throw s!"Bank {handle.name} has the wrong number of words"

def ScopedProgram.decodeSnapshot (program : ScopedProgram) (json : Json) : Except String Snapshot := do
  let entry ← lookup (program.modules.map fun m => (m.name, m)) program.entry "scoped entry"
  let banks ← entry.banks.mapM fun handle => do
    let image ← BankImage.decode handle json
    return (⟨handle, image.bank⟩ : Σ bank : Resource,
      ReadOnlyQRAM.Bank bank.type.addressWidth bank.type.dataWidth)
  return fun actual => (banks.findSome? fun declared =>
    if equal : declared.1 = actual then some (equal ▸ declared.2) else none)

theorem ScopedProgram.decodeSnapshot_congr_banks {first second : ScopedProgram} (json : Json)
    {firstEntry secondEntry : ScopedModule}
    (firstFound : lookup (first.modules.map fun m => (m.name, m)) first.entry "scoped entry" =
      .ok firstEntry)
    (secondFound : lookup (second.modules.map fun m => (m.name, m)) second.entry "scoped entry" =
      .ok secondEntry)
    (sameBanks : firstEntry.banks = secondEntry.banks) :
    first.decodeSnapshot json = second.decodeSnapshot json := by
  unfold ScopedProgram.decodeSnapshot
  rw [firstFound, secondFound]
  simp only [Bind.bind, Except.bind, sameBanks]

/-- Decoding a snapshot creates entries only for the resources declared by its
scoped entry, even when the JSON contains extra banks. -/
theorem ScopedProgram.decodeSnapshot_outside (program : ScopedProgram) (json : Json)
    {entry : ScopedModule} {snapshot : Snapshot}
    (found : lookup (program.modules.map fun m => (m.name, m)) program.entry "scoped entry" = .ok entry)
    (decoded : program.decodeSnapshot json = .ok snapshot)
    (bank : Resource) (outside : bank ∉ entry.banks) : snapshot bank = none := by
  let decode (handle : Resource) :
      Except String (Σ r : Resource, ReadOnlyQRAM.Bank r.type.addressWidth r.type.dataWidth) := do
    let image ← BankImage.decode handle json
    return ⟨handle, image.bank⟩
  have kept (handles : List Resource)
      (tables : List (Σ r : Resource, ReadOnlyQRAM.Bank r.type.addressWidth r.type.dataWidth))
      (checked : handles.mapM decode = .ok tables) :
      tables.map Sigma.fst = handles := by
    induction handles generalizing tables with
    | nil =>
      cases checked
      rfl
    | cons handle rest ih =>
      cases cell : BankImage.decode handle json with
      | error reason =>
        simp [List.mapM_cons, decode, cell, Bind.bind, Except.bind] at checked
      | ok image =>
        have first : decode handle = .ok ⟨handle, image.bank⟩ := by
          simp [decode, cell, Bind.bind, Except.bind, Pure.pure, Except.pure]
        cases restChecked : rest.mapM decode with
        | error reason =>
          simp [List.mapM_cons, first, restChecked, Bind.bind, Except.bind] at checked
        | ok restTables =>
          have all := ih restTables restChecked
          simp only [List.mapM_cons, first, restChecked, Bind.bind, Except.bind, Pure.pure,
            Except.pure, Except.ok.injEq] at checked
          cases checked
          exact congrArg (handle :: ·) all
  unfold ScopedProgram.decodeSnapshot at decoded
  rw [found] at decoded
  change (do
    let tables : List (Σ r : Resource, ReadOnlyQRAM.Bank r.type.addressWidth r.type.dataWidth)
      ← entry.banks.mapM decode
    return fun (actual : Resource) => tables.findSome? fun
      (declared : Σ r : Resource, ReadOnlyQRAM.Bank r.type.addressWidth r.type.dataWidth) =>
        if equal : declared.1 = actual then some (equal ▸ declared.2) else none) = .ok snapshot at decoded
  cases checked : entry.banks.mapM decode with
  | error reason => rw [checked] at decoded; cases decoded
  | ok tables =>
    rw [checked] at decoded
    cases decoded
    apply List.findSome?_eq_none_iff.mpr
    intro declared member
    have absent : declared.1 ≠ bank := by
      intro equal
      apply outside
      rw [← kept entry.banks tables checked, ← equal]
      exact List.mem_map_of_mem member
    exact dite_eq_right absent

end OracqVerify.RIR
