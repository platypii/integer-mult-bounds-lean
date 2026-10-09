import IntegerMultBounds.Machine.CountedRankSplitCopy
import IntegerMultBounds.Compact.KeyValue

/-! The growing repair counter is read with literal zero extension. No minimum
counter length is required for either tape or rank-value correctness. -/
namespace IntegerMultBounds.Machine.CountedRankSplitData
noncomputable section
variable {a : ℕ}

theorem zero_reads (f : ℤ → Fin (a+4)) (cs : List Bool)
    (ht : ∀ z : ℤ, 1+cs.length ≤ z → f z = blank) (j : ℕ) :
    CopyCells.zeroFill (putWord f 1 (cs.map bitSymbol) (1+j)) = bitSymbol (cs.getD j false) := by
  by_cases hj : j < cs.length
  · rw [Gather.putWord_getD f 1 cs j hj]
    cases cs.getD j false <;> rfl
  · rw [putWord_outside f 1 (1+j) (cs.map bitSymbol) (Or.inr (by simp; omega)),ht _ (by omega)]
    rw [List.getD_eq_default cs false (by omega : cs.length ≤ j)]
    rfl

theorem cells_field (f : ℤ → Fin (a+4)) (cs : List Bool)
    (hr : ∀ j : ℕ, CopyCells.zeroFill (f (1+j)) = bitSymbol (cs.getD j false)) (m d : ℕ) :
    CopyCells.cells f (1+m) d = (Gather.field cs m d).map bitSymbol := by
  induction d generalizing m with
  | zero => rfl
  | succ d ih =>
    rw [CopyCells.cells,KeyRoutine.field_cons,List.map_cons,hr]
    have he : (1 : ℤ)+(m : ℤ)+1 = 1+((m+1 : ℕ) : ℤ) := by push_cast; ring
    rw [he,ih]

theorem cells_word (f : ℤ → Fin (a+4)) (cs : List Bool)
    (ht : ∀ z : ℤ, 1+cs.length ≤ z → f z = blank) (m d : ℕ) :
    CopyCells.cells (putWord f 1 (cs.map bitSymbol)) (1+m) d = (Gather.field cs m d).map bitSymbol :=
  cells_field _ cs (zero_reads f cs ht) m d

theorem getD_append_zero (cs : List Bool) (k j : ℕ) :
    (cs++List.replicate k false).getD j false = cs.getD j false := by
  by_cases hj : j < cs.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_eq_default cs false (by omega : cs.length ≤ j)]
    simp [List.getD_eq_getElem?_getD]

theorem field_append_zero (cs : List Bool) (k m d : ℕ) :
    Gather.field (cs++List.replicate k false) m d = Gather.field cs m d := by
  unfold Gather.field
  apply List.map_congr_left
  intro j _
  exact getD_append_zero cs k (m+j)

theorem value_append_zero (cs : List Bool) (k : ℕ) :
    Counter.value (cs++List.replicate k false) = Counter.value cs := by
  rw [ColumnTransducer.value_append,IntegerMultBounds.Compact.PowerTwo.value_replicate_false',mul_zero,add_zero]

/-- Prefix value with no full-width stored counter precondition. -/
theorem value_prefix (cs : List Bool) (d : ℕ) :
    Counter.value (Gather.field cs 0 d) = Counter.value cs % 2^d := by
  have h := IntegerMultBounds.Compact.PowerTwo.value_field_prefix (cs++List.replicate d false) d
    (by simp)
  simpa only [field_append_zero,value_append_zero] using h

/-- Higher address value with no minimum stored counter length. -/
theorem value_middle (cs : List Bool) (m d : ℕ) :
    Counter.value (Gather.field cs m d) = Counter.value cs / 2^m % 2^d := by
  have h := IntegerMultBounds.Compact.PowerTwo.value_field_middle (cs++List.replicate (m+d) false) m d
    (by simp)
  simpa only [field_append_zero,value_append_zero] using h

/-- Low/high words reconstruct every in-range rank, even from a short growing
counter. Blank-tail traversal does not alter the original stored counter. -/
theorem value_decomposition (cs : List Bool) (q b n : ℕ)
    (hb : Counter.value cs < 2^(n*q+n*b)) :
    Counter.value (Gather.field cs 0 (n*q))+
      2^(n*q)*Counter.value (Gather.field cs (n*q) (n*b)) = Counter.value cs := by
  rw [value_prefix,value_middle]
  have hdiv : Counter.value cs / 2^(n*q) < 2^(n*b) := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [← pow_add,Nat.add_comm] using hb
  rw [Nat.mod_eq_of_lt hdiv]
  exact Nat.mod_add_div _ _

/-- The existing compact rank equivalence now applies to short counters. -/
theorem rank_split (q b : ℕ) (Zb cs : List Bool) (hq : 1 ≤ q) (j : ℕ)
    (hj : j < IntegerMultBounds.Compact.PowerTwo.Mi q b Zb) (hv : Counter.value cs = j) :
    (IntegerMultBounds.Compact.PowerTwo.rankEquiv q b Zb).symm ⟨j,hj⟩ =
      IntegerMultBounds.Compact.PowerTwo.addr q b Zb cs hq := by
  have h := IntegerMultBounds.Compact.PowerTwo.rank_split q b Zb
    (cs++List.replicate (Zb.length*q+Zb.length*b) false) hq j hj
    (by rw [value_append_zero,hv]) (by simp)
  simpa only [IntegerMultBounds.Compact.PowerTwo.addr,IntegerMultBounds.Compact.PowerTwo.Vw,
    IntegerMultBounds.Compact.PowerTwo.Ww,field_append_zero] using h

end
end IntegerMultBounds.Machine.CountedRankSplitData
