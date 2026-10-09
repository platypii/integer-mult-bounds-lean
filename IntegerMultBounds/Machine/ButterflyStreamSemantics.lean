import IntegerMultBounds.Machine.ButterflyAxisSerialization

/-! Exact decoded meaning of the literal coefficient streams produced by the
paid machine. The fixed signed width is justified by the actual prefix grid;
one butterfly increases the dyadic precision by one and preserves the grid
invariant required by the next selected-axis operation. -/
namespace IntegerMultBounds.Machine.ButterflyStreamSemantics
noncomputable section
open ButterflyStreamData ButterflyAxisSerialization
open Networks.GaussianPrecision

def decode (half precision : ℕ) (x : Coefficient) : ℂ :=
  ButterflySigned.complexValue (ButterflySigned.signedValue half x.1)
    (ButterflySigned.signedValue half x.2) precision

private def ctx (x : Coefficient) : DelimitedRadixRecord.Context 2 :=
  ⟨fun _ => 0,0,[],[],x.1,x.2⟩

theorem result_exact (a b : Coefficient) (p D j : ℕ) (hj : j≤D)
    (ha : a.1.length=ButterflyGuard.width p D ∧ a.2.length=ButterflyGuard.width p D)
    (hb : b.1.length=ButterflyGuard.width p D ∧ b.2.length=ButterflyGuard.width p D)
    (hga : BoundedGrid (p+j) ((2^p)*4^j) (decode (ButterflyGuard.halfWidth p D) (p+j) a))
    (hgb : BoundedGrid (p+j) ((2^p)*4^j) (decode (ButterflyGuard.halfWidth p D) (p+j) b)) :
    decode (ButterflyGuard.halfWidth p D) (p+j+1) (result a b 0)=
      (decode (ButterflyGuard.halfWidth p D) (p+j) a+decode (ButterflyGuard.halfWidth p D) (p+j) b+
        Complex.I*(decode (ButterflyGuard.halfWidth p D) (p+j) a-decode (ButterflyGuard.halfWidth p D) (p+j) b))/2 ∧
    decode (ButterflyGuard.halfWidth p D) (p+j+1) (result a b 1)=
      (decode (ButterflyGuard.halfWidth p D) (p+j) a+decode (ButterflyGuard.halfWidth p D) (p+j) b-
        Complex.I*(decode (ButterflyGuard.halfWidth p D) (p+j) a-decode (ButterflyGuard.halfWidth p D) (p+j) b))/2 := by
  exact ButterflyRecord.exact_of_prefix_grid (ctx a) (ctx b) p D j hj ha hb
    (by intro i; fin_cases i; exact hga; exact hgb)

theorem result_grid (a b : Coefficient) (p D j : ℕ) (hj : j≤D)
    (ha : a.1.length=ButterflyGuard.width p D ∧ a.2.length=ButterflyGuard.width p D)
    (hb : b.1.length=ButterflyGuard.width p D ∧ b.2.length=ButterflyGuard.width p D)
    (hga : BoundedGrid (p+j) ((2^p)*4^j) (decode (ButterflyGuard.halfWidth p D) (p+j) a))
    (hgb : BoundedGrid (p+j) ((2^p)*4^j) (decode (ButterflyGuard.halfWidth p D) (p+j) b)) (k : Fin 2) :
    BoundedGrid (p+(j+1)) ((2^p)*4^(j+1))
      (decode (ButterflyGuard.halfWidth p D) (p+(j+1)) (result a b k)) := by
  have hh := result_exact a b p D j hj ha hb hga hgb
  have hplus := bounded_half (bounded_add (bounded_add hga hgb) (bounded_I_mul (bounded_sub hga hgb)))
  have hminus := bounded_half (bounded_sub (bounded_add hga hgb) (bounded_I_mul (bounded_sub hga hgb)))
  have he : (2^p*4^j+2^p*4^j)+(2^p*4^j+2^p*4^j)=2^p*4^(j+1) := by rw [pow_succ]; ring
  simp only [Nat.add_assoc] at hh
  fin_cases k
  · apply (congrArg (BoundedGrid (p+(j+1)) (2^p*4^(j+1))) hh.1).mpr
    simpa only [Nat.add_assoc,he] using hplus
  · apply (congrArg (BoundedGrid (p+(j+1)) (2^p*4^(j+1))) hh.2).mpr
    simpa only [Nat.add_assoc,he] using hminus

/-- Complete selected-axis coefficient output, before the literal inverse merge. -/
def transformed {H N : ℕ} (xs : Fin H → Fin 2 → Fin N → Coefficient)
    (h : Fin H) (k : Fin 2) (i : Fin N) : Coefficient := result (xs h 0 i) (xs h 1 i) k

theorem paired_transformed {H N : ℕ} (xs : Fin H → Fin 2 → Fin N → Coefficient)
    (k : Fin 2) (i : Fin (H*N)) :
    paired (transformed xs) k i=result (paired xs 0 i) (paired xs 1 i) k := rfl

/-- Every output record has the exact fixed width expected by the merge and by
all later passes, while the common precision is incremented rather than rounded. -/
theorem transformed_width {H N : ℕ} (xs : Fin H → Fin 2 → Fin N → Coefficient) (w : ℕ)
    (hw : ∀ h k i,(xs h k i).1.length=w ∧ (xs h k i).2.length=w) :
    ∀ h k i,(transformed xs h k i).1.length=w ∧ (transformed xs h k i).2.length=w := by
  intro h k i
  exact ButterflyStreamEndpoint.result_width _ _ w (hw h 0 i) (hw h 1 i) k

end
end IntegerMultBounds.Machine.ButterflyStreamSemantics
