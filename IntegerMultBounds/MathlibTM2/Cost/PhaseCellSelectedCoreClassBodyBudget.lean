module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreBodyBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreClassQueues

/-! One data volume and one uniform body reserve for an actual movement class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedNormalizedJob
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierSetupPlan
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main

theorem selectedCoreClassJobs_bodyBudget (ct c pushBound : ℕ) {T Q : ℕ} {U : Type} :
    ∃ K : ℕ, ∀ᶠ n : ℕ in atTop, ∀ {A p u l targetOut s t width L : ℕ}, ∀ [NeZero s],
    ∀ {α gap : ℝ} {C : ZMod s → GaussianInt}, ∀ (h : Sizes.Big n)
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
    let V := inverseCallerWordWidth p u l targetOut s t
    let W := packedHaloCommonWidth p l s u (targetOut+1) 2
    let numerical := Finset.univ.sup (fun j => (jobs j).replicaTime)
    let reserve := K*(Sizes.t n i^6*Sizes.p n^4+Fs.length*L*W+Fs.length)
    ∀ j, ∀ (input : SupplierInputPlan T) (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q),
      mnProgPush (packedNormalizedLocalBatch (P := Empty) (U := U) (A := A) producer.hR producer.hQ) ≤ c →
      ∀ (v : HS T Q A U) (F : Stacks T A), plan.Ready (jobs j) F →
      coreTimeCost (U := U) producer V (jobs j) ≤ Fs.length*numerical+reserve ∧
        coreStock (U := U) producer pushBound V (jobs j) ≤ reserve := by
  obtain ⟨K,hcost⟩ := selectedDerivedCoreBody_budget (T := T) (Q := Q) (U := U) ct c pushBound
  refine ⟨K,?_⟩
  filter_upwards [hcost] with n hn
  intro A p u l targetOut s t width L _ α gap C h i hs hpSelected htSelected hlSelected
    huSelected htarget hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom hwidth hsep Fs hF
  subst s p t l
  let jobs := coreClassJobs (A := A) hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom hwidth hsep Fs hF
  dsimp only
  intro j input plan producer hpush v F hready
  have hb := hn h i A (jobs j) rfl rfl rfl huSelected htarget rfl rfl rfl
    input plan producer hpush v F hready
  have hqueues := coreClassJobs_queues (A := A) hp hpacket hα hst hu hαu hθ hgap hbudget hband
    hpad hC hdom hwidth hsep Fs hF
  have hpayload := (hqueues.2.2 j).1
  have hFs : (jobs j).Fs = Fs := rfl
  have hB : (jobs j).Bcore = inverseCallerWordWidth (Sizes.p n) u
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) targetOut (Sizes.s n i) (Sizes.t n i) := rfl
  rw [hFs,hB,hpayload] at hb
  have hreplica : (jobs j).replicaTime ≤ Finset.univ.sup (fun j => (jobs j).replicaTime) :=
    Finset.le_sup (f := fun j => (jobs j).replicaTime) (Finset.mem_univ j)
  have hscaled := Nat.mul_le_mul_left Fs.length hreplica
  exact ⟨hb.1.trans (Nat.add_le_add_right hscaled _),hb.2⟩

end IntegerMultBounds.MathlibTM2.Cost
