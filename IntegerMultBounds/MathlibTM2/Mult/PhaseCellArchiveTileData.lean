module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPacketEncoding
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! Rectangular archive rows supply the existing coefficient interchange ABI.
Rows are arbitrary computed lists; no external array or bit encoding is assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

private theorem archive_cstream_flatten (A w : ℕ) (rows : List (List GaussianInt)) :
    cstream A w rows.flatten = (rows.map (cstream A w)).flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [ih]

/-- Recover the finite row view from its checked length, preserving every entry. -/
theorem archiveRow_ofFn {M B L : ℕ} (rows : Fin M → Fin B → List GaussianInt)
    (hlen : ∀ i j, (rows i j).length = L) (i : Fin M) (j : Fin B) :
    List.ofFn (fun k : Fin L => (rows i j)[k.val]'(by rw [hlen]; exact k.isLt)) = rows i j := by
  apply List.ext_getElem (by simp [hlen])
  intro k hk hk'
  simp only [List.getElem_ofFn]

/-- The actual core-major encoded archive equals the coefficient router input. -/
theorem archiveRows_cstream {A M B L : ℕ} (w : ℕ) (rows : Fin M → Fin B → List GaussianInt)
    (hlen : ∀ i j, (rows i j).length = L) :
    cstream A w (replicaKeyWords (fun i j (k : Fin L) => (rows i j)[k.val]'(by rw [hlen]; exact k.isLt))) =
      (List.ofFn fun i => (List.ofFn fun j => cstream A w (rows i j)).flatten).flatten := by
  rw [replicaKeyWords_blocks,archive_cstream_flatten]
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [archive_cstream_flatten]
  simp only [List.map_ofFn,Function.comp_def,archiveRow_ofFn rows hlen]

/-- The same routed coefficients form one complete core list for each replica. -/
theorem routedArchiveRows_cstream {A M B L : ℕ} (w : ℕ) (rows : Fin M → Fin B → List GaussianInt)
    (hlen : ∀ i j, (rows i j).length = L) :
    cstream A w (keyReplicaWords (fun i j (k : Fin L) => (rows i j)[k.val]'(by rw [hlen]; exact k.isLt))) =
      (List.ofFn fun j => cstream A w (List.ofFn fun i => rows i j).flatten).flatten := by
  rw [keyReplicaWords_blocks,archive_cstream_flatten]
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext j
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  exact archiveRow_ofFn rows hlen i j

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
