module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFittingCyclicInputLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicReplicaSizing
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Absorb ordinary input setup once per fitting batch; repeated conversion
remains linear in the actual replica count and axis volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedFittingCyclicInputSharedWorkspace_le (cw cW : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ (H K : ReplicaHaloProblem (Sizes.s m i)) (W : ℕ),
      (∀ D ∈ [H,K], D.p = Sizes.p m ∧ D.t = Sizes.t m i ∧
        D.l = haloInverseRingLog (Sizes.s m i) (Sizes.t m i) ∧ D.u ≤ Sizes.p m ∧
        D.wordWidth ≤ cw*Sizes.p m) → W ≤ cW*Sizes.p m →
      fittingCyclicInputPush (Q := Q) (A := A) (U := U)*fittingCyclicInputSharedTime H K W ≤ Sizes.T m := by
  let C := cw+cW+21
  let push := fittingCyclicInputPush (Q := Q) (A := A) (U := U)
  filter_upwards [selectedAxisPolynomial_le_volume (push*2000006*C^2) 2 2] with m hv
  intro h i _ H K W hprofile hW
  have hp : 1 ≤ Sizes.p m := by have := h.thirteen_le_p; omega
  have hl := (haloInverseRingLog_bounds hp (h.good.lt i) (h.quarter_p_le_theta i)).1
  have hshared := fittingCyclicInputSharedTime_axis H K W (Sizes.p m) (Sizes.t m i) cw cW
    (h.good.lt i) hp hW (by
      intro D hD
      obtain ⟨hpD,htD,hlD,huD,hwD⟩ := hprofile D hD
      exact ⟨hpD,htD,hlD ▸ hl,huD,hwD⟩)
  have hscaled := Nat.mul_le_mul_left push hshared
  have hvolume := hv i
  dsimp only [C] at hvolume
  nlinarith only [hscaled,hvolume]

/-- Selected accounting for the input reserve already used by the complete
ordinary execution trace. Seed lengths describe actual supplied scalar words. -/
theorem selectedFittingCyclicInputWorkspace_le {T : ℕ} (cw cW : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ (ports : CyclicComplexCallerLayout T) (H K : ReplicaHaloProblem (Sizes.s m i))
        (W N : ℕ) (S : Stacks T A),
      (∀ D ∈ [H,K], D.p = Sizes.p m ∧ D.t = Sizes.t m i ∧
        D.l = haloInverseRingLog (Sizes.s m i) (Sizes.t m i) ∧ D.u ≤ Sizes.p m ∧
        D.wordWidth ≤ cw*Sizes.p m) → W ≤ cW*Sizes.p m →
      H.Fs.length = 2*N → K.Fs.length = 2*N → H.span+K.span < Sizes.t m i →
      (∀ k ∈ recoverySeedHeaderPorts, (S.R (ports.seedL k)).length = recoverySeedHeader H W N k) →
      (∀ k ∈ recoverySeedHeaderPorts, (S.R (ports.seedR k)).length = recoverySeedHeader K W N k) →
      fittingCyclicInputPush (Q := Q) (A := A) (U := U)*ports.inputTimeCost H K W N S ≤
        (fittingCyclicInputPush (Q := Q) (A := A) (U := U)*
          (32*cW+2*(4*cW+12*cw+28)+70))*N*Sizes.t m i*Sizes.p m+Sizes.T m := by
  filter_upwards [selectedFittingCyclicInputSharedWorkspace_le (Q := Q) (A := A) (U := U) cw cW] with m hshared
  intro h i _ ports H K W N S hprofile hW hH hK hspan hleft hright
  have hpH := hprofile H (by simp)
  have hpK := hprofile K (by simp)
  have hcost := fittingCyclicInputWorkspace_le (Q := Q) (U := U) ports H K W N cw cW S
    hH hK hleft hright (hpK.1.trans hpH.1.symm)
    (by simpa only [hpH.1] using hpH.2.2.2.2)
    (by simpa only [hpK.1] using hpK.2.2.2.2)
    (by simpa only [hpH.1] using hW) (by simpa only [hpH.2.1] using hspan)
  rw [hpH.1,hpH.2.1] at hcost
  have hs := hshared h i H K W hprofile hW
  omega

end IntegerMultBounds.MathlibTM2.Cost
