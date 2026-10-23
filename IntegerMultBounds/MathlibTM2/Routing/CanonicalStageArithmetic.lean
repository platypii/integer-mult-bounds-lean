module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalGeneratedInput
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalStageWidths

/-! Supply every width and fit proof of a canonical stage from logarithmic
scalar widths. Only the genuine R2 density/radix assumptions remain premises. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

def canonicalStageArithmetic (p : Par) (hG : 0 < p.G) (hK : 0 < p.K) (hguard : p.G + 1 < p.K)
    (scale : ℕ) (hscale : (0 : ℝ) < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * (scale : ℝ) ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G))
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) : CanonicalStageArithmetic p := by
  let rb := canonicalScalarWidth R
  have hcount : R * 2 ^ fieldsLen (selectiveLen p 0) < 2 ^ (fieldsLen (selectiveLen p 0) + rb) := by
    have h := Nat.mul_lt_mul_of_pos_right (canonicalScalarWidth_fit R) (Nat.two_pow_pos (fieldsLen (selectiveLen p 0)))
    simpa only [rb, pow_add, Nat.mul_comm] using h
  refine {
    w := canonicalStageWidths p
    rb := rb
    wb := canonicalScalarWidth (fieldsLen (selectiveKeyLen p 0 rb) + B)
    wm := fieldsLen (selectiveLen p 0) + rb
    wp := canonicalScalarWidth B
    wk := canonicalScalarWidth (fieldsLen (selectiveKeyLen p 0 rb))
    R := R, B := B, scale := scale
    Lrow := rb, Lwidth := canonicalScalarWidth p.wc
    Lr := canonicalScalarWidth rb, Lm := canonicalScalarWidth p.wy
    LK := canonicalScalarWidth p.K, Ln := canonicalScalarWidth p.n
    Lo := canonicalScalarWidth (p.ρ + 1), Lt := canonicalScalarWidth p.m
    Lcp := canonicalScalarWidth (fieldsLen (selectiveLen p 0)), Lp := canonicalScalarWidth B
    rowBits := GrowingCounterData.advance R []
    hG := hG, hK := hK, hguard := hguard, hscale := hscale, hn := hn, hradix := hradix, hgap := hgap
    hwidth := canonicalStageWidths_selector p
    hselectorWidthFit := canonicalScalarWidth_fit _
    hkfit := canonicalStageWidths_key p
    hnfit := canonicalStageWidths_slots p
    hwfit := canonicalStageWidths_source p
    hR := hR, hB := hB, hrb := (canonicalScalarWidth_fit R).le
    hblock := canonicalScalarWidth_fit _, hrecords := hcount, hpayload := canonicalScalarWidth_fit _
    hkey := canonicalScalarWidth_fit _, hfit := canonicalStageWidths_bounds p
    hRfit := canonicalScalarWidth_fit _, hwidthFit := canonicalScalarWidth_fit _
    hr := canonicalScalarWidth_fit _, hm := canonicalScalarWidth_fit _, hsegment := canonicalScalarWidth_fit _
    hcountFit := canonicalScalarWidth_fit _, hoffset := canonicalScalarWidth_fit _, htop := canonicalScalarWidth_fit _
    hwidthPlacement := canonicalScalarWidth_fit _, hBin := canonicalScalarWidth_fit _
    hrowCanonical := GrowingCounterData.advance_canonical R [] (Or.inl rfl)
    hrowNe := by
      intro he
      have hv := GrowingCounterData.empty_value R
      rw [he] at hv
      change 0 = R at hv
      omega
    hrowValue := GrowingCounterData.empty_value R }

end
end IntegerMultBounds.MathlibTM2.Routing
