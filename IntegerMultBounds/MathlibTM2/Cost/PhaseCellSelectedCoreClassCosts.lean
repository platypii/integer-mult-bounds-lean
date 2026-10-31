module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreJobWidths
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreClassJobs

/-! Uniform selected pricing for the actual ordered movement-class jobs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierSetupPlan
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
theorem selectedCoreClassJobs_costs {T Q : ℕ} {U : Type} (ct : ℕ) :
    ∃ K : ℕ, ∀ {A p u l targetOut s t width L : ℕ}, ∀ [NeZero s],
    ∀ {α gap : ℝ} {C : ZMod s → GaussianInt}, ∀ (n : ℕ) (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) (hs : s = Sizes.s n i) (hpSelected : p = Sizes.p n)
    (htSelected : t = Sizes.t n i) (hlSelected : l = haloInverseRingLog s t)
    (huSelected : u ≤ Sizes.p n) (htarget : targetOut ≤ ct*Sizes.p n)
    (hp : 2 ≤ p) (hpacket : 8*p ≤ 2^u) (hα : 0 < α)
    (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1))
    (hbudget : α^2*gap ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hC : ∀ a b, a ≤ b → b ≤ s → a < s →
      ∀ j, ‖value (packedHaloPrecision p l s t u (targetOut+1) 2 a b) (C j)‖ ≤ (2 : ℝ)^2)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hwidth : 0 < width) (hsep : L+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1),
    let jobs := coreClassJobs (A := A) hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom hwidth hsep Fs hF
    ∀ j,
      ∀ (input : SupplierInputPlan T) (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
        (pushBound : ℕ) (v : HS T Q A U) (S : Stacks T A), plan.Ready (jobs j) S →
      (coreTimeCost (U := U) producer (jobs j).Bcore (jobs j) ≤ producer.timeCost (U := U) [jobs j]+
        518*(jobs j).inputPayload.length+340*(jobs j).Fs.length+K*Sizes.t n i^6) ∧
      (coreStock (U := U) producer pushBound (jobs j).Bcore (jobs j) ≤
        (pushBound+1)*producer.workspace (U := U) [jobs j]+
        768*(jobs j).inputPayload.length+504*(jobs j).Fs.length+K*Sizes.t n i^6) := by
  obtain ⟨K,hcost⟩ := selectedDerivedCoreCosts_le_shared_add_linear (T := T) (Q := Q) (U := U) ct
  refine ⟨K,?_⟩
  intro A p u l targetOut s t width L _ α gap C n h i hs hpSelected htSelected hlSelected
    huSelected htarget hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom hwidth hsep Fs hF
  subst s p t l
  dsimp only
  intro j input plan producer pushBound v S hready
  apply hcost n h i A _ rfl rfl rfl huSelected htarget rfl rfl rfl input plan producer pushBound v S hready

end IntegerMultBounds.MathlibTM2.Cost
