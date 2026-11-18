module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDirectoryEntry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyAfterPrefix

/-! Copy the radix digits of a physical coefficient while retaining the directory record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host RadixDigits FlatCoordinateLayout
open Mult.PhaseCellToeplitz
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q : ℕ} {P U : Type}

theorem directoryRead_exec (body : P → Pr P T Q prime U) (bank : Fin 7 ↪ Fin T)
    (m w j : ℕ) (r c : Fin m) (ancestor tail : List (Fin (prime+4)))
    (v : HS T Q prime U) (S : Stacks T prime) :
    let offset := w * suffixFields (finProdFinEquiv (c,r))
    S.R (bank 2) = ancestor ++ (LabelDirectory.digits m w j).map digitSymbol ++ tail →
    (S.R (bank 0)).length = ancestor.length + offset → (S.R (bank 1)).length = w →
    (∀ i : Fin 7, 4 ≤ i → S.R (bank i) = []) →
    ∃ z xs, z.user = v.user ∧ xs.length = w ∧ value xs = (physicalLabel m w j r c).val ∧
      Exec body (copyAfterPrefix (bank 0) (bank 1) (bank 2) (bank 3) (bank 4) (bank 5) (bank 6))
        (mk v S) (6*(ancestor.length+offset)+10*w+16)
        (mk z {S with R := Function.update S.R (bank 3) (xs.map digitSymbol ++ S.R (bank 3))}) := by
  intro offset directory skip width free
  let ds := LabelDirectory.digits m w j
  let xs := (ds.drop offset).take w
  have bound : offset+w ≤ ds.length := by
    have len : ds.length = w*(m*m) := by simp [ds,LabelDirectory.digits]
    rw [len,← Nat.mul_one w,← Nat.mul_add,Nat.mul_one]
    apply Nat.mul_le_mul_left
    have h := (finProdFinEquiv (c,r)).isLt
    change m*m-1-_+1 ≤ m*m
    omega
  have lx : xs.length = w := by simp [xs]; omega
  have lp : (ds.take offset).length = offset := by simp; omega
  have decomp : ds.take offset ++ (xs ++ (ds.drop offset).drop w) = ds := by simp [xs]
  have parts := congrArg (List.map digitSymbol) decomp
  simp only [List.map_append] at parts
  obtain ⟨z,hz,run⟩ := copyAfterPrefix_exec (body := body)
    (by simp [List.nodup_cons,bank.injective.eq_iff] : [bank 0,bank 1,bank 2,bank 3,bank 4,bank 5,bank 6].Nodup)
    v S (ancestor ++ (ds.take offset).map digitSymbol) (xs.map digitSymbol)
    (((ds.drop offset).drop w).map digitSymbol ++ tail)
    (by rw [directory]; change ancestor ++ ds.map digitSymbol ++ tail = _; rw [← parts]; simp [List.append_assoc])
    (by simpa only [List.length_append,List.length_map,lp] using skip) (by simpa [lx] using width) (free 4 (by decide)) (free 5 (by decide)) (free 6 (by decide))
  exact ⟨z,xs,hz,lx,directoryEntry_value m w j r c,by simpa only [List.length_append,List.length_map,lp,lx] using run⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
