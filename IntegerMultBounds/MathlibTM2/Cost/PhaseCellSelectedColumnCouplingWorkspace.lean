module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellColumnCouplingWorkspacePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCouplingSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellColumnCouplingEnvelope

/-! Selected dimensions pay one uniform column/residual coupling reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {P₀ U : Type}

theorem selectedFeedCouplingUniformWorkspace_le (boundary : Bool) (K cw scale : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)),
      ∀ q w u band : ℕ, q ≤ w → w ≤ cw*Sizes.p m → 1 ≤ w → u ≤ Sizes.p m → band ≤ Sizes.s m i →
      scale*feedCouplingUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        boundary K (2^15*Sizes.p m) q w (Sizes.s m i) (Sizes.t m i) u band ≤ Sizes.T m := by
  let C := columnCouplingEnvelopeCoefficient (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary K cw
  obtain ⟨hCbase,hKC,hcwC,hLiftC,hPC,hpushC⟩ :=
    columnCouplingEnvelopeCoefficient_bounds (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary K cw
  let B := 10000000*(ssMulConst+1)
  filter_upwards [selectedAxisPolynomial_le_volume (scale*B*C^5) 5 5] with m hv
  intro h i q w u band hq hw hwpos hu hb
  let p := Sizes.p m
  let t := Sizes.t m i
  let s := Sizes.s m i
  let Z := C*t*p
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hst : s ≤ t := (h.good.lt i).le
  have hC : 13 ≤ C := hCbase
  have hCZ : C ≤ Z := by
    have h₁ := Nat.mul_le_mul_left C ht
    have h₂ := Nat.mul_le_mul_left (C*t) hp
    dsimp only [Z]; omega
  have hconst (x : ℕ) (hx : x ≤ C) : x ≤ Z := hx.trans hCZ
  have hlinear (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ C) : x ≤ Z := by
    have h₁ := Nat.mul_le_mul_right p hc
    have h₂ := Nat.mul_le_mul_left (C*p) ht
    dsimp only [Z]; nlinarith only [hx,h₁,h₂]
  have haxis (x c : ℕ) (hx : x ≤ c*t) (hc : c ≤ C) : x ≤ Z := by
    have h₁ := Nat.mul_le_mul_right t hc
    have h₂ := Nat.mul_le_mul_left (C*t) hp
    dsimp only [Z]; nlinarith only [hx,h₁,h₂]
  have hZ : 1 ≤ Z := (show 1 ≤ C by omega).trans hCZ
  have hpZ := hlinear p 1 (by omega) (by omega)
  have hPZ := hlinear (2^15*p) (2^15) le_rfl (by simpa only [show (2 : ℕ)^15 = 32768 by norm_num] using hPC)
  have hwZ := hlinear w cw hw hcwC
  have hqZ := hq.trans hwZ
  have hsZ := haxis s 1 (by omega) (by omega)
  have htZ := haxis t 1 (by omega) (by omega)
  have huZ := hu.trans hpZ
  have hbZ := hb.trans hsZ
  have hrowsZ := haxis (2*band+1) 3 (by omega) (by omega)
  have hLift := selectedLiftedCoefficientWidth_le cw h i q w u band hw hq hu hb
  have hLiftZ := hlinear _ (2*cw+426064) hLift hLiftC
  have hgeometry (b : ℕ) (hb : b ≤ 2*t) : publicationGeometryWidth t b ≤ 13*t := by
    have hsizeT : Nat.size t ≤ t := Nat.size_le.mpr Nat.lt_two_pow_self
    have hsizeB : Nat.size b ≤ b := Nat.size_le.mpr Nat.lt_two_pow_self
    unfold publicationGeometryWidth
    omega
  have hGZ := haxis _ 13 (hgeometry band (by omega)) (by omega)
  have hG₂Z := haxis _ 13 (hgeometry (2*band) (by omega)) (by omega)
  have hpoly := feedCouplingUniformWorkspace_poly (P₀ := P₀) (Q := Q) (A := A) (U := U)
    (K := K) (P := 2^15*p) (q := q) (w := w) (s := s) (t := t) (u := u) (band := band)
    boundary hZ ht hst hwpos (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hconst _ hKC
      all_goals assumption) (by
      intro x hx
      exact hconst x (hpushC x hx))
  have hscaled := Nat.mul_le_mul_left scale hpoly
  have heq : scale*(10000000*(ssMulConst+1)*Z^5) = (scale*B*C^5)*t^5*p^5 := by
    dsimp only [Z,B]; ring
  rw [heq] at hscaled
  exact hscaled.trans (hv i)

end IntegerMultBounds.MathlibTM2.Cost
