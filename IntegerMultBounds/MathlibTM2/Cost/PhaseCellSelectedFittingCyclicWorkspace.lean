module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFittingCyclicInputWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicFactorPreparationWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicComplexCoreWorkspace

/-! Reprice the named reserve of the actual ordinary fitting execution. Setup
is shared; only conversion traffic and numerical replica storage repeat. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open CyclicReplicaPlacement
variable {Q A : ℕ} {U : Type}

noncomputable def fittingCyclicWorkspaceTrafficFactor (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct cW : ℕ) : ℕ :=
  let c := 1032+8*ct
  fittingCyclicInputPush (Q := Q) (A := A) (U := U)*(32*cW+2*(4*cW+12*c+28)+70)+
    2*cyclicComplexWorkspaceTrafficFactor (A := A) (U := U) hR hQ c c cW

theorem selectedFittingCyclicWorkspace_le {T : ℕ} (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct cW : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ (ports : CyclicComplexCallerLayout T) (S C F : Stacks T A)
        (u target a n W count radius core : ℕ) (α d : ℝ),
      let p := Sizes.p m
      let s := Sizes.s m i
      let t := Sizes.t m i
      let l := haloInverseRingLog s t
      ∀ (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s),
      u ≤ p → target ≤ ct*p → a+n ≤ s → radius+core ≤ n → W ≤ cW*p → p ≤ W →
      let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
      let solveTarget := boundaryRecoveryTarget p (target+1)
      let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 N) 2
      let q := executionPrecision p l stage 2
      let w := executionWidth p l stage 2
      ∀ (Fs : List (ZMod s → GaussianInt))
        (hF : ∀ R ∈ Fs, ∀ k, ‖value q (R k)‖ ≤ (2 : ℝ)^2),
      let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Fs hF
      let K := axis.cyclicRightReplicaProblem stage 2 a n hn Fs hF
      Fs.length = 2*count →
      (∀ k ∈ recoverySeedHeaderPorts, (S.R (ports.seedL k)).length = recoverySeedHeader H W count k) →
      (∀ k ∈ recoverySeedHeaderPorts, (S.R (ports.seedR k)).length = recoverySeedHeader K W count k) →
      (∀ k, (C.R (cachedFactorSeedSource (ports.small ∘ left.plan.gather) ports.span k)).length =
        cyclicFactorMasterValues p l s t u solveTarget a n k) →
      CyclicFactorSeedInput p l s t u solveTarget a n [] (embStk (ports.small ∘ factorReg) F) →
      ∀ J L, CyclicSecondInteriorProfile H K J L p solveTarget N →
      ports.workspace (U := U) H K J L hR hQ p u l t a n solveTarget q w W N
        Fs.length count radius core S C F ≤
      fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW*count*t*p+43*Sizes.T m := by
  let c := 1032+8*ct
  filter_upwards [selectedFittingCyclicInputWorkspace_le (Q := Q) (A := A) (U := U) (T := T) c cW,
    selectedCyclicFactorPreparationWorkspace_le (Q := Q) (A := A) (U := U) (T := T) ct,
    selectedExecutedCyclicComplexCoreWorkspace_le (A := A) (U := U) hR hQ ct cW,
    selectedAxisPolynomial_le_volume (8*cW+34) 1 1] with m hinput hfactor hnumeric hcontrol
  intro h i _ ports S C F u target a n W count radius core α d
  dsimp only
  intro axis ha hn hu htarget hfit hcore hW hpW Fs hF hcount hleft hright hvalues seed J L profile
  have hwidth := (selectedCyclicReplicaSizing ct h i u target a n hu htarget axis.hband).2.2.2.1
  have hbase := selectedCyclicReplicaProblems_profile ct h i axis target a n ha hn hu htarget Fs hF
  have hinputs := hinput h i ports _ _ W count S (by
    intro D hD
    obtain ⟨hp,ht,hl,hu',_,_,_,hw,_,_,_,_⟩ := hbase D hD
    exact ⟨hp,ht,hl,hu' ▸ hu,hw ▸ hwidth⟩) hW hcount hcount
    (by change min n (Sizes.s m i-a)+(n-min n (Sizes.s m i-a)) < Sizes.t m i
        have := h.good.lt i
        omega) hleft hright
  have hfactors := hfactor h i
    ((ports.small ∘ factorReg) ∘ Fin.castLE (by decide : 224 ≤ 234))
    (cachedFactorSeedSource (ports.small ∘ left.plan.gather) ports.span) C
    (embStk (ports.small ∘ factorReg) F) u target a n hu htarget axis.hband (by omega) hn hvalues seed
  change cyclicFactorPreparationPush (Q := Q) (A := A) (U := U)*
    ports.factorTimeCost (Sizes.s m i) (Sizes.t m i) (Sizes.p m) u a n C F ≤ 2*Sizes.T m at hfactors
  have hnumerical := hnumeric h i u target a n W count radius core α d axis ha hn hu htarget hfit hcore hW hpW
    Fs hF J L profile (by omega)
  have ht : 1 ≤ Sizes.t m i := by have := h.good.lt i; omega
  have hp : 1 ≤ Sizes.p m := by have := h.thirteen_le_p; omega
  have htP := Nat.le_mul_of_pos_right (Sizes.t m i) hp
  have hpT := Nat.le_mul_of_pos_left (Sizes.p m) ht
  have hunit : 1 ≤ Sizes.t m i*Sizes.p m := Nat.mul_pos ht hp
  have hWaxis := hW.trans (Nat.mul_le_mul_left cW hpT)
  have hcoreAxis : radius+core ≤ Sizes.t m i*Sizes.p m := by
    have := h.good.lt i
    omega
  have hcontrols : 2*(4*(W+radius+core)+13) ≤ Sizes.T m := by
    have hv := hcontrol i
    simp only [pow_one] at hv
    nlinarith only [hWaxis,hcoreAxis,hunit,hv]
  rw [hcount] at hnumerical ⊢
  change _ ≤ cyclicComplexWorkspaceTrafficFactor (A := A) (U := U) hR hQ c c cW*
    (2*count)*Sizes.t m i*Sizes.p m+39*Sizes.T m at hnumerical
  unfold CyclicComplexCallerLayout.workspace fittingCyclicWorkspaceTrafficFactor
  change _ ≤ (fittingCyclicInputPush (Q := Q) (A := A) (U := U)*(32*cW+2*(4*cW+12*c+28)+70)+
    2*cyclicComplexWorkspaceTrafficFactor (A := A) (U := U) hR hQ c c cW)*count*Sizes.t m i*Sizes.p m+43*Sizes.T m
  nlinarith only [hinputs,hfactors,hnumerical,hcontrols]

end IntegerMultBounds.MathlibTM2.Cost
