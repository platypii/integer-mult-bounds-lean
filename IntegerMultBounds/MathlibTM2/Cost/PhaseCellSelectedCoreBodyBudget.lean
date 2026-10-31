module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerCostLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedJobWorkspace

/-! Full fixed-body pricing separates repeated numerical execution from shared
setup and data traffic. Compiled cleanup syntax is never normalized here. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierSetupPlan
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main

private def bodyBudget (S H G cv c C : ℕ) : ℕ :=
  (C+2)*((6*(c+1)+1)*S+33*H+7*cv+10426+(3000*(c+1)+1000)+G+768)

private theorem bodyBounds (S H G cv c C X payload replicas setup shared inputStock V
    replicaTime producerTime producerStock coreTime coreStock : ℕ)
    (hX : 1 ≤ X) (hsetup : setup ≤ S*X) (hshared : shared ≤ S*X)
    (hinput : inputStock ≤ H*X) (hV : V ≤ cv*X)
    (hproducerTime : producerTime ≤ setup+replicas*replicaTime+
      6*(c+1)*shared+(3000*(c+1)+1000)*(payload+replicas)+33*inputStock+6*V+10426)
    (hproducerStock : producerStock ≤ (6*(c+1)+1)*shared+
      (3000*(c+1)+1000)*(payload+replicas)+33*inputStock+7*V+10421)
    (hcoreTime : coreTime ≤ producerTime+518*payload+340*replicas+G*X)
    (hcoreStock : coreStock ≤ (C+1)*producerStock+768*payload+504*replicas+G*X) :
    coreTime ≤ replicas*replicaTime+bodyBudget S H G cv c C*(X+payload+replicas) ∧
      coreStock ≤ bodyBudget S H G cv c C*(X+payload+replicas) := by
  let B := (6*(c+1)+1)*S+33*H+7*cv+10426+(3000*(c+1)+1000)
  have ht := Nat.mul_le_mul_left (6*(c+1)) hshared
  have hs := Nat.mul_le_mul_left (6*(c+1)+1) hshared
  have hslack : 0 ≤ ((6*(c+1)+1)*S+33*H+7*cv+10426)*(payload+replicas)+
      (3000*(c+1)+1000)*X := Nat.zero_le _
  have hcv : 0 ≤ cv*X := Nat.zero_le _
  have htime : producerTime ≤ replicas*replicaTime+B*(X+payload+replicas) := by
    dsimp only [B]
    nlinarith only [hproducerTime,hsetup,hinput,hV,ht,hX,hslack,hcv]
  have hstock : producerStock ≤ B*(X+payload+replicas) := by
    dsimp only [B]
    nlinarith only [hproducerStock,hinput,hV,hs,hX,hslack]
  have hKt : B+G+768 ≤ bodyBudget S H G cv c C := by
    change B+G+768 ≤ (C+2)*(B+G+768)
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hKs : (C+1)*B+G+768 ≤ bodyBudget S H G cv c C := by
    change (C+1)*B+G+768 ≤ (C+2)*(B+G+768)
    nlinarith only [Nat.zero_le (C*(G+768)),Nat.zero_le B]
  have htimeBudget := Nat.mul_le_mul_right (X+payload+replicas) hKt
  have hstockBudget := Nat.mul_le_mul_right (X+payload+replicas) hKs
  have hstockScaled := Nat.mul_le_mul_left (C+1) hstock
  constructor
  · nlinarith only [hcoreTime,htime,htimeBudget]
  · nlinarith only [hcoreStock,hstockScaled,hstockBudget]

/-- The actual body has one shared polynomial bill and data-linear overhead;
only the native numerical solve remains multiplied by the replica count. -/
theorem selectedDerivedCoreBody_budget (ct c C : ℕ) {T Q : ℕ} {U : Type} :
    ∃ K : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ, ∀ r : PackedNormalizedJob A (Sizes.s n i),
      r.p = Sizes.p n → r.t = Sizes.t n i →
      r.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      r.u ≤ Sizes.p n → r.targetOut ≤ ct*Sizes.p n →
      r.V = packedHaloWorkspaceWidth r.p r.l (Sizes.s n i) r.t r.u (r.targetOut+1) 2 r.a r.b →
      r.W = packedHaloCommonWidth r.p r.l (Sizes.s n i) r.u (r.targetOut+1) 2 →
      r.Bcore = inverseCallerWordWidth r.p r.u r.l r.targetOut (Sizes.s n i) r.t →
      ∀ (input : SupplierInputPlan T) (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q),
      mnProgPush (packedNormalizedLocalBatch (P := Empty) (U := U) (A := A) producer.hR producer.hQ) ≤ c →
      ∀ (_v : HS T Q A U) (S : Stacks T A), plan.Ready r S →
      (coreTimeCost (U := U) producer r.Bcore r ≤ r.Fs.length*r.replicaTime+
        K*(Sizes.t n i^6*Sizes.p n^4+r.inputPayload.length+r.Fs.length)) ∧
      (coreStock (U := U) producer C r.Bcore r ≤
        K*(Sizes.t n i^6*Sizes.p n^4+r.inputPayload.length+r.Fs.length)) := by
  let cv := 2*(1032+8*ct)+426009
  let cW := 1032+8*ct
  obtain ⟨S,hshared⟩ := selectedDerivedCoreSharedCosts_poly_le ct
  obtain ⟨G,hbody⟩ := selectedDerivedCoreCosts_le_shared_add_linear (T := T) (Q := Q) (U := U) ct
  obtain ⟨H,hcontrol⟩ := selectedCanonicalCoreControlCosts_poly_le ct cv cW
  refine ⟨bodyBudget S H G cv c C,?_⟩
  filter_upwards [hshared] with n hn
  intro h i _ A r hp ht hl hu htarget hV hW hB input plan producer hpush v F hready
  have hwidths := selectedDerivedCoreWidths_le ct h i r hp ht hl hu htarget hV hW hB
  have hnum := hn h i A r hp ht hl hu htarget hV hW hB
  have hc := hcontrol n h i A r hp ht hl hu htarget hwidths.1 hwidths.2.1 hB
  have hb := hbody n h i A r hp ht hl hu htarget hV hW hB input plan producer C v F hready
  obtain ⟨w,headerState,k,_,_,_,hheaders,_,_,_,_⟩ := plan.generate_exec
    (body := fun f : Empty => nomatch f) r v F hready 0
  have hprod := producer.singleton_costs_le_ready r input headerState hheaders w c hpush
  let X := Sizes.t n i^6*Sizes.p n^4
  have hp1 : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have ht1 : 1 ≤ Sizes.t n i := hp1.trans (selectedPrecision_le_axis h i)
  have hX : 1 ≤ X := Nat.mul_pos (Nat.one_le_pow _ _ ht1) (Nat.one_le_pow _ _ hp1)
  have htX : Sizes.t n i^6 ≤ X := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hp1)
  have hpX : Sizes.p n ≤ X := by
    have hpPow : Sizes.p n ≤ Sizes.p n^4 := Nat.le_self_pow (by decide) _
    exact hpPow.trans (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ ht1))
  have hinput : r.inputSharedStock ≤ H*X := by
    have hI : r.inputSharedStock ≤ coreControlStock r.Bcore r+62*r.inputSharedStock :=
      (Nat.le_mul_of_pos_left _ (by decide : 0 < 62)).trans (Nat.le_add_left _ _)
    exact (hI.trans hc.2).trans (Nat.mul_le_mul_left H htX)
  have hVr : r.V ≤ cv*X := hwidths.1.trans (Nat.mul_le_mul_left cv hpX)
  have hscale := Nat.mul_le_mul_left G htX
  have htime : coreTimeCost (U := U) producer r.Bcore r ≤ producer.timeCost (U := U) [r]+
      518*r.inputPayload.length+340*r.Fs.length+G*X := hb.1.trans (Nat.add_le_add_left hscale _)
  have hstock : coreStock (U := U) producer C r.Bcore r ≤ (C+1)*producer.workspace (U := U) [r]+
      768*r.inputPayload.length+504*r.Fs.length+G*X := hb.2.trans (Nat.add_le_add_left hscale _)
  have hsetup : r.setupTime ≤ S*X := by simpa only [X,Nat.mul_assoc] using hnum.1
  have hshared : r.sharedWorkspace ≤ S*X := by simpa only [X,Nat.mul_assoc] using hnum.2
  have hbound := bodyBounds S H G cv c C X r.inputPayload.length r.Fs.length r.setupTime
    r.sharedWorkspace r.inputSharedStock r.V r.replicaTime (producer.timeCost (U := U) [r])
    (producer.workspace (U := U) [r]) (coreTimeCost (U := U) producer r.Bcore r)
    (coreStock (U := U) producer C r.Bcore r) hX hsetup hshared hinput hVr hprod.1 hprod.2 htime hstock
  exact hbound

end IntegerMultBounds.MathlibTM2.Cost
