module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderHandoffRow
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece

/-! Zero rows stay zero through the ordinary remainder, including invertible labels. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Matrix
open Shared50ModularControl (prime)
open IntegerMultBounds.Swap.Modular
open FlatCoordinateLayout
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem OriginalPortReads.zero_row {w R W parents : ℕ} {interval parent c input output}
    (reads : OriginalPortReads (w := w) R W parents interval parent c input output)
    (checked : c.Checked) (units : ∀ i, IsUnit (parent i))
    (block : Fin parents) (g : LabelPadding.Label 64 (w+1)) :
    let M := prime^(w+1)
    let j := block.val*M^(64*64)+(LabelAddress.address g).val
    ownerRow (R := R) (N := M^128*W) rfl input j = 0 →
      ownerRow (R := R) (N := M^128*W) rfl output j = 0 := by
  intro M j empty
  by_cases live : IsUnit g
  · let S := c.span interval.1 interval.2
    let P := (reduce M S).submatrix stageAxis.symm stageAxis.symm
    let G := projectorResidual finSumFinEquiv P parent (fun i => Ring.inverse (parent i)) g
    have adm := portSpan_admissible c checked interval.1 interval.2 (w+1)
    have sq : P*P = P := by
      dsimp only [P]
      rw [Matrix.submatrix_mul_equiv,← reduce_mul M adm adm,show S*S = S from Certificates.PR589.Nine.PortCertificate.span_mul_self checked _ _]
    have sign := projectorResidual_sign (by omega : 0 < w+1) finSumFinEquiv P sq parent
      (fun i => Ring.inverse (parent i)) (fun i => Ring.mul_inverse_cancel _ (units i)) g
      ((Matrix.isUnit_iff_isUnit_det _).mp live)
    have det : IsUnit G.det := by
      rcases sign with h | h <;> change G.det = _ at h <;> rw [h] <;> simp
    funext i
    obtain ⟨⟨r,k⟩,rfl⟩ := finProdFinEquiv.surjective i
    have read := (reads block g).1 live (G⁻¹ *ᵥ coordinates r) k
    change ownerRow (R := R) (N := M^128*W) rfl output j (index (G *ᵥ (G⁻¹ *ᵥ coordinates r)) k) =
      ownerRow (R := R) (N := M^128*W) rfl input j _ at read
    rw [mulVec_mulVec,G.mul_nonsing_inv det,one_mulVec,empty] at read
    simpa only [index,rank_coordinates,Pi.zero_apply] using read
  · exact ((reads block g).2 live).trans empty

/-- If each parent supplies only the identity row, the whole output bank is
again supported there, so the same physical rotation can carry it back. -/
theorem OriginalPortReads.identity_support {w W B : ℕ} {interval parent c}
    (input output : Fin ((B*(prime^(w+1))^(64*64))*((prime^(w+1))^128*W)) → ZMod 2)
    (reads : OriginalPortReads (w := w) _ W B interval parent c input output)
    (checked : c.Checked) (units : ∀ i, IsUnit (parent i)) :
    let idRow := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
    let atCell := fun (b : Fin B) j (k : Fin ((prime^(w+1))^128*W)) =>
      finProdFinEquiv (finProdFinEquiv (b,j),k)
    (∀ b j k, j ≠ idRow → input (atCell b j k) = 0) →
    ∀ b j k, output (atCell b j k) = if j = idRow then output (atCell b idRow k) else 0 := by
  intro idRow atCell support b j k
  by_cases h : j = idRow
  · simp [h]
  rw [ite_eq_right h]
  obtain ⟨g,rfl⟩ := (address_bijective (w+1)).surjective j
  let r := finProdFinEquiv (b,LabelAddress.address g)
  have addr : r.val = b.val*(prime^(w+1))^(64*64)+(LabelAddress.address g).val := by
    simp [r,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  have get (f : Fin ((B*(prime^(w+1))^(64*64))*((prime^(w+1))^128*W)) → ZMod 2)
      (k : Fin ((prime^(w+1))^128*W)) :
      ownerRow rfl f r.val k = f (atCell b (LabelAddress.address g) k) := by
    unfold ownerRow; rw [dif_pos r.isLt]; rfl
  have empty := reads.zero_row checked units b g
  dsimp only at empty
  rw [← addr] at empty
  have hz := empty (by funext t; exact (get input t).trans (support b _ t h))
  exact (get output k).symm.trans (congrFun hz k)

end IntegerMultBounds.MathlibTM2.M6.BitNode
