module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedNormalizedWorkspace

/-! Reprice the actual normalized caller's returned execution certificate at
selected sizes. The execution, step count and output store are unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedPackedNormalizedBatch_trace_volume_le {T Q A : ℕ} {P U : Type} [Fintype P]
    (body : P → Pr P T Q A U) (ct cv cB cW : ℕ)
    (hT : 280 ≤ T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (rg : TblR 25 → Fin T) (ports : Fin 4 → Fin T) (headerSrc : Fin T) :
    let program := packedKeyNormalizedBatch (P := P) (U := U) (A := A) hT hR hQ rg ports headerSrc
    let c := max (mnProgPush program) (mnPushC body)
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ B W u target a b V coreWidth k radius count : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n → a ≤ b → b ≤ Sizes.s n i →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → V ≤ cv*Sizes.p n →
      B ≤ cB*Sizes.p n → W ≤ cW*Sizes.p n →
      coreLength (Sizes.s n i) coreWidth k+2*radius ≤ b-a →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      2*q+8 ≤ W →
      ∀ (s₀ sf : Store (HΓ (T := T) A) (HS T Q A U)) (steps : ℕ),
      (∀ C, mnProgPush program ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize s₀+
          ((2*count)*((b-a)*(2*q+8))+V)+depth+(C+1)*
            packedKeyNormalizedWorkspace B p q W u l s t a b V (boundaryRecoveryTarget p (target+1))
              (target+1) 2 target coreWidth k radius count)
          depth program s₀ steps sf) →
      ∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize s₀+depth+
        (500*(c+1)+2)*count*((b-a)*W+1)+Sizes.T n) depth program s₀ steps sf := by
  dsimp only
  let program : Pr P T Q A U := packedKeyNormalizedBatch hT hR hQ rg ports headerSrc
  let c := max (mnProgPush program) (mnPushC body)
  filter_upwards [selectedPackedNormalizedWorkspace_scaled_volume_add_replicas_le ct cv cB cW (2*(c+1)),
    selectedAxisPolynomial_le_volume (2*cv) 1 0] with n hwspace hv
  intro h i _ B W u target a b V coreWidth k radius count hu ht hab hb hband hV hB hW hhalo
  intro hnative s₀ sf steps hstock depth
  have hwork := hwspace h i B W u target a b V coreWidth k radius count hu ht hab hb hband hV hB hW hhalo hnative
  have hvolume := hv i
  simp only [pow_zero,pow_one,mul_one] at hvolume
  have hV2 : 2*V ≤ Sizes.T n := by nlinarith only [hV,hvolume]
  let q := executionPrecision (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
    (initialSchurTarget (Sizes.p n) u
      (boundaryTableBits (Sizes.p n) (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2
        (haloBoundary (Sizes.s n i) (Sizes.t n i) (PhaseCellBand.width (Sizes.p n) u) a b).card) 2) 2
  let work := packedKeyNormalizedWorkspace B (Sizes.p n) q W u
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a b V
    (boundaryRecoveryTarget (Sizes.p n) (target+1)) (target+1) 2 target coreWidth k radius count
  have hbudget : V+(c+1)*work ≤ 500*(c+1)*count*((b-a)*W+1)+Sizes.T n := by
    dsimp only [work,q]
    nlinarith only [hwork,hV2]
  have hdata := Nat.mul_le_mul_left ((2*count)*(b-a)) hnative
  have ht := hstock c (Nat.le_max_left _ _) (fun f =>
    (mn_progPush_le_pushC body f).trans (Nat.le_max_right _ _)) depth
  apply ht.mono
  intro d z hz
  change mnSize z+d ≤ mnSize s₀+depth+(500*(c+1)+2)*count*((b-a)*W+1)+Sizes.T n
  change mnSize z+d ≤ mnSize s₀+((2*count)*((b-a)*(2*q+8))+V)+depth+(c+1)*work at hz
  nlinarith only [hz,hbudget,hdata]

end IntegerMultBounds.MathlibTM2.Cost
