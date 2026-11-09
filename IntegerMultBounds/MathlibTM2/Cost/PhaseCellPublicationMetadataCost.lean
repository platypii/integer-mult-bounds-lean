module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationMetadataVolume
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPublicationPaddedVolume
public import IntegerMultBounds.NLogN.PhaseCellCoreLocalityGeometry
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Metadata contains two replica-sized words. All remaining words are shared
scalar setup; rounding a possibly empty core group is accounted for explicitly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose


private theorem metadataVolume_le {s t k b N L W V cW cV : ℕ}
    (ht : 1 ≤ t) (hs : s ≤ t) (hk : k ≤ t) (hb : 2^b = N)
    (hL : L ≤ 3*t) (hW : W ≤ cW*t) (hV : V ≤ cV*t) :
    publicationHeaderVolume (Nat.clog 2 k) b L W V s k ≤ 2*N+(11+cW+2*cV)*t^2 := by
  have ha : Nat.clog 2 k ≤ 2^(Nat.clog 2 k) := Nat.lt_two_pow_self.le
  have hpad := pow_clog_two_le k
  have hbSmall : b ≤ N := Nat.lt_two_pow_self.le.trans_eq hb
  have hprod := Nat.mul_le_mul hk hV
  have htSq : t ≤ t^2 := Nat.le_self_pow (by decide) t
  have hone : 1 ≤ t^2 := ht.trans htSq
  have hWsq := hW.trans (Nat.mul_le_mul_left cW htSq)
  have hVsq := hV.trans (Nat.mul_le_mul_left cV htSq)
  unfold publicationHeaderVolume
  rw [hb]
  nlinarith only [ha,hpad,hbSmall,hprod,htSq,hone,hs,hk,hL,hWsq,hVsq]

theorem selectedPublicationMetadata_le (cV cW scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ k b N L W V : ℕ, k ≤ Sizes.s n i → 2^b = N → L ≤ 3*Sizes.s n i →
      W ≤ cW*Sizes.p n → V ≤ cV*Sizes.p n →
      scale*publicationHeaderVolume (Nat.clog 2 k) b L W V (Sizes.s n i) k ≤
        Sizes.T n+2*scale*N := by
  filter_upwards [selectedAxisPolynomial_le_volume (scale*(11+cW+2*cV)) 0 2] with n hn
  intro h i k b N L W V hk hb hL hW hV
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpt := selectedPrecision_le_axis h i
  have hst := (h.good.lt i).le
  have hc := metadataVolume_le (hp.trans hpt) hst (hk.trans hst) hb
    (hL.trans (Nat.mul_le_mul_left 3 hst))
    (hW.trans (Nat.mul_le_mul_left cW hpt)) (hV.trans (Nat.mul_le_mul_left cV hpt))
  have hscaled := Nat.mul_le_mul_left scale hc
  have hv : scale*(11+cW+2*cV)*(Sizes.t n i)^2 ≤ Sizes.T n := by
    simpa only [pow_zero,mul_one] using hn i
  nlinarith only [hscaled,hv]

end IntegerMultBounds.MathlibTM2.Cost
