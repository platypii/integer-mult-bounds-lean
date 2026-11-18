module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackWeightedEntry

/-! Compute all entries of a conjugated projector using one shared reciprocal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open Matrix LabelTraversal IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {m : ℕ}

/-- Cramer's rule on rows uses the same denominator for the whole label. -/
def conjugateNumerator {R : Type*} [CommRing R] (g P : Matrix (Fin m) (Fin m) R) :
    Matrix (Fin m) (Fin m) R := fun i j => (g.updateRow j ((g*P) i)).det

theorem conjugate_entry {R : Type*} [CommRing R] (g P : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    (g*P*g⁻¹) i j = Ring.inverse g.det * conjugateNumerator g P i j := by
  have numerator := congrFun (cramer_eq_adjugate_mulVec g.transpose ((g*P) i)) j
  rw [cramer_transpose_apply,← adjugate_transpose] at numerator
  rw [conjugateNumerator,numerator,Matrix.inv_def,Matrix.mul_smul,Matrix.smul_apply,smul_eq_mul]
  congr 1
  simp [Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm]

variable {T Q A M : ℕ} [NeZero M] {P U : Type}

theorem conjugateMatrix_writes (body : P → Pr P T Q A U) (r : Fin 14 ↪ Fin T)
    (g proj : Matrix (Fin m) (Fin m) (ZMod M)) (H : ℕ) (hm : M < 2^H) (tail : List (Fin (A+4))) :
    let valid := fun R : Node.Regs T A => R (r 13) = matrixWords A H (conjugateNumerator g proj) ++ tail ∧
      R (r 0) = binSyms H (Ring.inverse g.det).val ∧ R (r 2) = binSyms H M ∧
      ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (r k) = []
    Writes body valid (r 3) (sequence (fun i : Fin m => sequence (fun j : Fin m => weightedEntry (i.val*m+j.val) r)
      (List.finRange m)) (List.finRange m)) (matrixWords A H (g*proj*g⁻¹))
      (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) := by
  intro valid
  apply matrixWords_writes
  · intro R xs h
    have keep (k : Fin 14) (hk : k ≠ 3) := Function.update_of_ne (r.injective.ne hk) xs R
    exact ⟨(keep 13 (by decide)).trans h.1,(keep 0 (by decide)).trans h.2.1,(keep 2 (by decide)).trans h.2.2.1,
      fun k hk => (keep k (by omega)).trans (h.2.2.2 k hk)⟩
  · intro i j v S ready
    obtain ⟨z,n,hz,hn,run⟩ := weightedEntry_writes body r (conjugateNumerator g proj) i j (Ring.inverse g.det) H hm tail v S ready
    rw [conjugate_entry]
    have hi := i.isLt
    have hj := j.isLt
    have offset : i.val*m+j.val ≤ m*m := by nlinarith only [Nat.mul_le_mul_right m (show i.val+1 ≤ m by omega),hj]
    exact ⟨z,n,hz,by linarith [Nat.mul_le_mul_right H offset],run⟩

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
