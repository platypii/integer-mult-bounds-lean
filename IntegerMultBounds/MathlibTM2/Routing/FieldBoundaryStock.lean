module

public import IntegerMultBounds.MathlibTM2.Host.BoundedHeaderStock
public import IntegerMultBounds.MathlibTM2.Routing.DyadicFieldLayout

/-! Dimension headers are bounded by the complete payload. The source stream
has constant length, so these four headers are the only boundary allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.FieldBoundaryStock
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main

theorem dimensions_le_volume {P B R : ℕ} (hP : 0 < P) (hB : 0 < B) (hR : 0 < R) :
    P ≤ P*(B*R) ∧ R ≤ P*(B*R) ∧ B*R ≤ P*(B*R) := by
  have hBRpos := Nat.mul_pos hB hR
  have hBR : B*R ≤ P*(B*R) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (B*R) (show 1 ≤ P by omega)
  have hR' : R ≤ B*R := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right R (show 1 ≤ B by omega)
  have hP' : P ≤ P*(B*R) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left P (show 1 ≤ B*R by omega)
  exact ⟨hP',hR'.trans hBR,hBR⟩

theorem bits_le_volume (N P B W : ℕ) (hP : 0 < P) (hB : 0 < B) (hW : 0 < W) :
    N ≤ P*(B*(2^N*W)) := by
  have hN : N ≤ 2^N := by
    induction N with
    | zero => omega
    | succ N ih =>
      have hp := Nat.two_pow_pos N
      rw [Nat.pow_succ]
      omega
  have hp : 2^N ≤ 2^N*W := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^N) (show 1 ≤ W by omega)
  exact hN.trans (hp.trans (dimensions_le_volume hP hB (Nat.mul_pos (Nat.two_pow_pos N) hW)).2.1)

theorem fieldBoundary_stock {T Q A : ℕ} {U : Type}
    (v vf : HS T Q A U) (S F : Stacks T A) (bits prefixCount volume fiberVolume src : Fin T) (V : ℕ)
    (hi : F.inp = S.inp) (ho : F.out = S.out) (hl : F.L = S.L)
    (hframe : ∀ i, i ∉ [bits,prefixCount,volume,fiberVolume,src] → F.R i = S.R i)
    (hsrc : (F.R src).length = (S.R src).length)
    (hb : (F.R bits).length ≤ V) (hp : (F.R prefixCount).length ≤ V)
    (hv : (F.R volume).length ≤ V) (hf : (F.R fiberVolume).length ≤ V) :
    mnSize (mk vf F) ≤ mnSize (mk v S)+4*V := by
  let header : Fin 4 → Fin T := ![bits,prefixCount,volume,fiberVolume]
  apply mnSize_mk_le_header_bank v vf S F header V hi ho hl
  · intro j
    fin_cases j <;> first | exact hb | exact hp | exact hv | exact hf
  · intro i hnot
    by_cases his : i = src
    · subst i; exact hsrc.le
    · rw [hframe i ?_]
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨by simpa [header] using hnot 0,by simpa [header] using hnot 1,
        by simpa [header] using hnot 2,by simpa [header] using hnot 3,his⟩

end IntegerMultBounds.MathlibTM2.Routing.FieldBoundaryStock
