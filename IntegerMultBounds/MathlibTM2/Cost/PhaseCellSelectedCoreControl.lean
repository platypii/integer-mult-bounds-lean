module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreControlPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawBatchKeys

/-! The actual fixed core body's scalar control costs inherit the existing
selected raw-header polynomial, independently of the number of RHS replicas. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierSetupPlan
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedCoreControlCosts_poly_le (ct cv cB cW : ℕ) :
    ∃ C : ℕ, ∀ n : ℕ, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A : ℕ, ∀ r : PackedNormalizedJob A (Sizes.s n i),
      r.p = Sizes.p n → r.t = Sizes.t n i →
      r.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      r.u ≤ Sizes.p n → r.targetOut ≤ ct*Sizes.p n →
      r.V ≤ cv*Sizes.p n → r.Bcore ≤ cB*Sizes.p n → r.W ≤ cW*Sizes.p n →
      r.Bcore = inverseCallerWordWidth r.p r.u r.l r.targetOut (Sizes.s n i) r.t →
      (coreControlTimeCost r.Bcore r+42*r.inputSharedStock ≤ C*Sizes.t n i^6) ∧
      (coreControlStock r.Bcore r+62*r.inputSharedStock ≤ C*Sizes.t n i^6) := by
  let κ := ct+cv+cB+cW+21
  let K := 20000*100000^3*(ct+21)^6
  let C := 1000*K+1000000000*κ^2
  refine ⟨C,?_⟩
  intro n h i _ A r hp ht hl hu htarget hV hB hW hBcanonical
  let t := Sizes.t n i
  let R := κ*t
  have hpt := selectedPrecision_le_axis h i
  have hp1 : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have ht1 : 1 ≤ t := hp1.trans hpt
  have htR : t ≤ R := Nat.le_mul_of_pos_left t (by dsimp [κ]; omega)
  have hR : 1 ≤ R := ht1.trans htR
  have hst := h.good.lt i
  have hsR : Sizes.s n i ≤ R := hst.le.trans htR
  have hscale (c x : ℕ) (hc : c ≤ κ) (hx : x ≤ c*Sizes.p n) : x ≤ R :=
    hx.trans ((Nat.mul_le_mul_left c hpt).trans (Nat.mul_le_mul_right t hc))
  have hpR : r.p ≤ R := by rw [hp]; exact hpt.trans htR
  have huR : r.u ≤ R := hu.trans (hpt.trans htR)
  have hlR : r.l ≤ R := by
    rw [hl]
    exact hscale 20 _ (by dsimp [κ]; omega)
      (haloInverseRingLog_bounds hp1 hst (h.quarter_p_le_theta i)).1
  have htargetR : r.targetOut ≤ R := hscale ct _ (by dsimp [κ]; omega) htarget
  have htR' : r.t ≤ R := by rw [ht]; exact htR
  have haR : r.a ≤ R := r.bounds.has.trans hsR
  have hbR : r.b ≤ R := r.bounds.hbs.trans hsR
  have hBR : r.Bcore ≤ R := hscale cB _ (by dsimp [κ]; omega) hB
  have hVR : r.V ≤ R := hscale cv _ (by dsimp [κ]; omega) hV
  have hWR : r.W ≤ R := hscale cW _ (by dsimp [κ]; omega) hW
  have hradiusR : r.radius ≤ R := by
    have hr := r.hright
    omega
  have hqR : r.q ≤ R := by have hq := r.hW; omega
  have hparams : ∀ x ∈ [r.p,r.u,r.l,r.targetOut,Sizes.s n i,r.t,r.a,r.b,r.Bcore,r.V,r.W,r.Bcore,r.radius,r.q], x ≤ R := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hband : PhaseCellBand.width (Sizes.p n) r.u ≤ Sizes.s n i := by simpa only [hp] using r.bounds.hband
  have hheaders := selectedRawHeaderCost_cuts_poly_le ct n h i r.u r.targetOut r.a r.b hu htarget
    r.bounds.has r.bounds.hbs hband
  dsimp only at hheaders
  have hraw : inverseScalarAtoms r.p (Sizes.s n i) r.t r.u r.a r.b*tblC r.Bcore 0+
      inverseMasterCopyCost r.Bcore r.factoryMasters ≤ K*t^6 := by
    rw [r.factoryMasters_eq_inverse,hBcanonical,hp,ht,hl]
    exact (Nat.le_add_right _ _).trans hheaders
  have hcost := coreControlCosts_le_header r.Bcore R (K*t^6) r hR hparams hraw
  have htPow : t^2 ≤ t^6 := Nat.pow_le_pow_right ht1 (by decide)
  have hbound : 1000*(K*t^6)+1000000000*R^2 ≤ C*t^6 := by
    calc
      _ = 1000*K*t^6+(1000000000*κ^2)*t^2 := by dsimp only [R]; ring
      _ ≤ 1000*K*t^6+(1000000000*κ^2)*t^6 := Nat.add_le_add_left (Nat.mul_le_mul_left _ htPow) _
      _ = C*t^6 := by dsimp only [C]; ring
  exact ⟨hcost.1.trans hbound,hcost.2.trans hbound⟩

/-- Selected scalar pricing applies to the actual fixed body from ordinary setup readiness. -/
theorem selectedCoreCosts_le_shared_add_linear (ct cv cB cW : ℕ) {T Q : ℕ} {U : Type} :
    ∃ C : ℕ, ∀ n : ℕ, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A : ℕ, ∀ r : PackedNormalizedJob A (Sizes.s n i),
      r.p = Sizes.p n → r.t = Sizes.t n i →
      r.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      r.u ≤ Sizes.p n → r.targetOut ≤ ct*Sizes.p n →
      r.V ≤ cv*Sizes.p n → r.Bcore ≤ cB*Sizes.p n → r.W ≤ cW*Sizes.p n →
      r.Bcore = inverseCallerWordWidth r.p r.u r.l r.targetOut (Sizes.s n i) r.t →
      ∀ (input : SupplierInputPlan T) (plan : SupplierSetupPlan input) (producer : PackedProducerPlan T Q)
        (pushBound : ℕ) (v : HS T Q A U) (S : Stacks T A), plan.Ready r S →
      (coreTimeCost (U := U) producer r.Bcore r ≤ producer.timeCost (U := U) [r]+
        518*r.inputPayload.length+340*r.Fs.length+C*Sizes.t n i^6) ∧
      (coreStock (U := U) producer pushBound r.Bcore r ≤ (pushBound+1)*producer.workspace (U := U) [r]+
        768*r.inputPayload.length+504*r.Fs.length+C*Sizes.t n i^6) := by
  obtain ⟨C,hcontrol⟩ := selectedCoreControlCosts_poly_le ct cv cB cW
  refine ⟨C,?_⟩
  intro n h i _ A r hp ht hl hu htarget hV hB hW hBcanonical input plan producer pushBound v S hready
  have hs := hcontrol n h i A r hp ht hl hu htarget hV hB hW hBcanonical
  have hc := plan.coreCosts_le_setupReady producer pushBound r.Bcore r v S hready
  constructor
  · have hscalar := hs.1; have hbody := hc.1; omega
  · have hscalar := hs.2; have hbody := hc.2; omega

end IntegerMultBounds.MathlibTM2.Cost
