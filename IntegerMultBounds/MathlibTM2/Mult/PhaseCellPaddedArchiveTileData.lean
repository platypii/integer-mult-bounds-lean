module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTilePaddingData

/-! Prefix padding preserves the full rectangular row address, so the real
cores remain identifiable separately in each transposed replica stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

/-- A real core's index after whole-core prefix padding. -/
def paddedCoreIndex {N C : ℕ} (hN : N ≤ C) (i : Fin N) : Fin C :=
  ⟨C-N+i.val,by have := i.isLt; omega⟩

theorem paddedCore_entry {α : Type*} {N C B L : ℕ} (hN : N ≤ C) (fill : α)
    (f : Fin N → Fin B → Fin L → α) (g : Fin C → Fin B → Fin L → α)
    (hpad : replicaKeyWords g = tilePrefixPad (C*(B*L)) fill (replicaKeyWords f))
    (i : Fin N) (j : Fin B) (k : Fin L) : g (paddedCoreIndex hN i) j k = f i j k := by
  let i' := paddedCoreIndex hN i
  have he := congrArg (fun xs : List α => xs[(i'.val*B+j.val)*L+k.val]?) hpad
  rw [replicaKeyWords_getElem?] at he
  rw [tilePrefixPad_replica_rows] at he
  have hindex : (i'.val*B+j.val)*L+k.val =
      (C-N)*(B*L)+((i.val*B+j.val)*L+k.val) := by
    dsimp only [i',paddedCoreIndex]
    ring
  rw [hindex,List.getElem?_append_right (by simp)] at he
  simp only [List.length_replicate,Nat.add_sub_cancel_left] at he
  rw [replicaKeyWords_getElem?] at he
  exact Option.some.inj he

/-- Dropping whole fixed-length rows agrees with dropping the flattened prefix. -/
theorem archiveRows_flatten_drop {α : Type*} (L n : ℕ) (rows : List (List α))
    (hlen : ∀ row ∈ rows, row.length = L) :
    rows.flatten.drop (n*L) = (rows.drop n).flatten := by
  induction n generalizing rows with
  | zero => simp
  | succ n ih =>
    cases rows with
    | nil => simp
    | cons row rows =>
      have hrow := hlen row (by simp)
      have hdrop : (row++rows.flatten).drop L = rows.flatten := by rw [←hrow,List.drop_left]
      simp only [List.flatten_cons,List.drop_succ_cons,Nat.succ_mul]
      rw [Nat.add_comm (n*L) L,←List.drop_drop,hdrop]
      exact ih rows (fun x hx => hlen x (by simp [hx]))

/-- Padding is a prefix within every replica after transpose, not a change to
any real core row or its order. -/
theorem paddedArchiveRows_drop {α : Type*} {N C B L : ℕ} (hN : N ≤ C)
    (rows : Fin N → Fin B → List α) (paddedRows : Fin C → Fin B → List α)
    (hlen : ∀ i j, (paddedRows i j).length = L)
    (hreal : ∀ i j, paddedRows (paddedCoreIndex hN i) j = rows i j) (j : Fin B) :
    (List.ofFn fun i => paddedRows i j).flatten.drop ((C-N)*L) =
      (List.ofFn fun i => rows i j).flatten := by
  rw [archiveRows_flatten_drop L (C-N) _ (by
    intro row hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact hlen i j)]
  apply congrArg List.flatten
  apply List.ext_getElem (by simp only [List.length_drop,List.length_ofFn]; omega)
  intro k hk hk'
  simp only [List.getElem_drop,List.getElem_ofFn]
  convert hreal ⟨k,by simpa only [List.length_ofFn] using hk'⟩ j using 1
  congr 1

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
