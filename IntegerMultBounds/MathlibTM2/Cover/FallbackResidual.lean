module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDiagonal
public import IntegerMultBounds.MathlibTM2.Cover.LabelRing

/-! The weighted reversed projector exchange is an involution. Over an odd prime-power
label ring its determinant is therefore a sign, as required by fallback elimination. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

def residual (A A' C P : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  fromBlocks A 0 0 C * fromBlocks (1-P) P P (1-P) * fromBlocks A' 0 0 C

theorem residual_mulVec (A A' C P : Matrix ι ι R) (x y : ι → R) :
    let s := M8.Exchange.transform A 1 (M8.ReversedExchange.revExchangeOf C P
      (M8.Exchange.transform A' 1 (x,y)))
    residual A A' C P *ᵥ Sum.elim x y = Sum.elim s.1 s.2 := by
  simp [residual,← mulVec_mulVec,fromBlocks_mulVec,M8.Exchange.transform,
    M8.ReversedExchange.revExchangeOf,M8.Exchange.exchange,Function.comp_def]
  rfl

theorem residual_sq (A A' C P : Matrix ι ι R) (hA : A * A' = 1)
    (hA' : A' * A = 1) (hC : C * C = 1) (hP : P * P = P) :
    residual A A' C P * residual A A' C P = 1 := by
  let frame (B : Matrix ι ι R) := fromBlocks B (0 : Matrix ι ι R) (0 : Matrix ι ι R) C
  let X := fromBlocks (1-P) P P (1-P)
  have cancel (B D : Matrix ι ι R) (h : B * D = 1) : frame B * frame D = 1 := by
    simp [frame,fromBlocks_multiply,h,hC]
  have square : X * X = 1 := by
    simp [X,fromBlocks_multiply,Matrix.mul_sub,Matrix.sub_mul,hP]
  change frame A * X * frame A' * (frame A * X * frame A') = 1
  calc
    _ = frame A * X * (frame A' * frame A) * X * frame A' := by simp only [mul_assoc]
    _ = frame A * (X * X) * frame A' := by rw [cancel _ _ hA',mul_one,mul_assoc (frame A) X X]
    _ = 1 := by rw [square,mul_one,cancel _ _ hA]

theorem residual_det_sign {q w : ℕ} [hq : Fact q.Prime] (hodd : 2 < q) (hw : 0 < w)
    (A A' C P : Matrix ι ι (ZMod (q ^ w))) (hA : A * A' = 1)
    (hA' : A' * A = 1) (hC : C * C = 1) (hP : P * P = P) :
    (residual A A' C P).det = 1 ∨ (residual A A' C P).det = -1 := by
  let := LabelRing.isLocalRing q w hw
  let x := (residual A A' C P).det
  have hx : x * x = 1 := by
    simpa [x,det_mul] using congrArg Matrix.det (residual_sq A A' C P hA hA' hC hP)
  have two : IsUnit (2 : ZMod (q ^ w)) := by
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hq.out hw (a := 2)).2
      (Nat.not_dvd_of_pos_of_lt (by decide) hodd)
  have hz : (1-x)*(1+x) = 0 := by linear_combination -hx
  have sum : IsUnit ((1-x)+(1+x)) := by
    convert two using 1
    ring
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add sum with h | h
  · obtain ⟨y,hy⟩ := h.exists_right_inv
    right
    change x = -1
    linear_combination y * hz - (1+x) * hy
  · obtain ⟨y,hy⟩ := h.exists_right_inv
    left
    change x = 1
    linear_combination -y * hz + (1-x) * hy

/-- Number the two fields consecutively (or by any common reindexing) for elimination. -/
theorem residual_pairs {q w n : ℕ} [Fact q.Prime] (hodd : 2 < q) (hw : 0 < w)
    (e : (ι ⊕ ι) ≃ Fin (n+1)) (A A' C P : Matrix ι ι (ZMod (q ^ w)))
    (hA : A * A' = 1) (hA' : A' * A = 1) (hC : C * C = 1) (hP : P * P = P) :
    let G := reindex e e (residual A A' C P)
    ∃ E, ∃ (d : Fin n → (ZMod (q ^ w))ˣ) (s : (ZMod (q ^ w))ˣ), Elim ((n+1)*n) (n+1) E ∧ (s = 1 ∨ s = -1) ∧
      E * G = diagonal (fun j => (((Fin.cons s (fun _ => 1) * ∏ i, pair i (d i) :
        Fin (n+1) → (ZMod (q ^ w))ˣ) j : (ZMod (q ^ w))ˣ) : ZMod (q ^ w))) := by
  let := LabelRing.isLocalRing q w hw
  apply fallback_pairs
  simpa only [det_reindex_self] using residual_det_sign hodd hw A A' C P hA hA' hC hP

end IntegerMultBounds.MathlibTM2.Cover.Fallback
