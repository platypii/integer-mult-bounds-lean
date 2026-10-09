import IntegerMultBounds.Machine.ActiveRepairLayoutPermutationFiber

/-! Concrete global permutations of the actual unchanged active-target
address. Source coordinates choose the local packed operation at every fiber;
the ideal preserves the bad set and the actual agrees off that set. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutPermutation
noncomputable section
attribute [local instance] Classical.propDecidable
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairLayoutPermutationFiber
open IntegerMultBounds.Compact IntegerMultBounds.Compact.PowerTwo

private def lift {A B : Type*} (e : A ≃ B) (p : Equiv.Perm B) : Equiv.Perm A :=
  e.trans (p.trans e.symm)
private theorem lift_eval {A B : Type*} (e : A ≃ B) (p : Equiv.Perm B) (x : A) :
    e (lift e p x)=p (e x) := e.apply_symm_apply _

variable (s : Shape) (q b n before after rows rho offset width : ℕ)
variable (side : ActiveRepairRankHeadersData.SourceSide) (hq : 1≤q)

abbrev Z := controlWord before after q rho n offset width side
abbrev A := Address s (n*b) (n*q) before after rows

abbrev earlyFiber := ActiveRepairLayoutPermutationFiber.earlyEquiv s q b n before after rows rho offset width side hq
abbrev lateFiber := ActiveRepairLayoutPermutationFiber.lateEquiv s q b n before after rows rho offset width side hq

def earlyActual : Equiv.Perm (A s q b n before after rows) :=
  lift (earlyFiber s q b n before after rows rho offset width side hq)
    (VaryingControlRepairPacked.earlyActual q b (Z q n before after rho offset width side))
def earlyIdeal : Equiv.Perm (A s q b n before after rows) :=
  lift (earlyFiber s q b n before after rows rho offset width side hq)
    (VaryingControlRepairPacked.earlyIdeal q b (Z q n before after rho offset width side))
def earlyBad (x : A s q b n before after rows) :=
  VaryingControlRepairPacked.earlyBad q b (Z q n before after rho offset width side)
    (earlyFiber s q b n before after rows rho offset width side hq x)

def lateActual : Equiv.Perm (A s q b n before after rows) :=
  lift (lateFiber s q b n before after rows rho offset width side hq)
    (VaryingControlRepairPacked.lateActual q b (Z q n before after rho offset width side))
def lateIdeal : Equiv.Perm (A s q b n before after rows) :=
  lift (lateFiber s q b n before after rows rho offset width side hq)
    (VaryingControlRepairPacked.lateIdeal q b (Z q n before after rho offset width side))
def lateBad (x : A s q b n before after rows) :=
  VaryingControlRepairPacked.lateBad q b (Z q n before after rho offset width side)
    (lateFiber s q b n before after rows rho offset width side hq x)

local notation "EA" => earlyActual s q b n before after rows rho offset width side hq
local notation "EI" => earlyIdeal s q b n before after rows rho offset width side hq
local notation "EB" => earlyBad s q b n before after rows rho offset width side hq
local notation "LA" => lateActual s q b n before after rows rho offset width side hq
local notation "LI" => lateIdeal s q b n before after rows rho offset width side hq
local notation "LB" => lateBad s q b n before after rows rho offset width side hq

theorem early_actual_fiber (x : A s q b n before after rows) :
    earlyFiber s q b n before after rows rho offset width side hq (EA x)=
      VaryingControlRepairPacked.earlyActual q b (Z q n before after rho offset width side)
        (earlyFiber s q b n before after rows rho offset width side hq x) := lift_eval _ _ _
theorem early_ideal_fiber (x : A s q b n before after rows) :
    earlyFiber s q b n before after rows rho offset width side hq (EI x)=
      VaryingControlRepairPacked.earlyIdeal q b (Z q n before after rho offset width side)
        (earlyFiber s q b n before after rows rho offset width side hq x) := lift_eval _ _ _
theorem late_actual_fiber (x : A s q b n before after rows) :
    lateFiber s q b n before after rows rho offset width side hq (LA x)=
      VaryingControlRepairPacked.lateActual q b (Z q n before after rho offset width side)
        (lateFiber s q b n before after rows rho offset width side hq x) := lift_eval _ _ _
theorem late_ideal_fiber (x : A s q b n before after rows) :
    lateFiber s q b n before after rows rho offset width side hq (LI x)=
      VaryingControlRepairPacked.lateIdeal q b (Z q n before after rho offset width side)
        (lateFiber s q b n before after rows rho offset width side hq x) := lift_eval _ _ _

theorem early_inverse_fiber (x : A s q b n before after rows) :
    earlyFiber s q b n before after rows rho offset width side hq ((EA).symm x)=
      (VaryingControlRepairPacked.earlyActual q b (Z q n before after rho offset width side)).symm
        (earlyFiber s q b n before after rows rho offset width side hq x) := by
  rw [Equiv.eq_symm_apply,←early_actual_fiber,Equiv.apply_symm_apply]
theorem late_inverse_fiber (x : A s q b n before after rows) :
    lateFiber s q b n before after rows rho offset width side hq ((LA).symm x)=
      (VaryingControlRepairPacked.lateActual q b (Z q n before after rho offset width side)).symm
        (lateFiber s q b n before after rows rho offset width side hq x) := by
  rw [Equiv.eq_symm_apply,←late_actual_fiber,Equiv.apply_symm_apply]

theorem early_preserves (x : A s q b n before after rows) : EB (EI x) ↔ EB x := by
  unfold earlyBad earlyIdeal
  rw [lift_eval]
  exact not_congr (earlyIdeal_preserves_good (Bi b) (Li q) (Li_pos q) _ (controls_bits _) _)

theorem late_preserves (x : A s q b n before after rows) : LB (LI x) ↔ LB x := by
  unfold lateBad lateIdeal
  rw [lift_eval]
  exact not_congr (lateIdeal_preserves_good (Bi b) (Li q) (Li_pos q) _ (controls_bits _) _)

theorem early_agrees (x : A s q b n before after rows) (hx : ¬ EB x) : EA x=EI x := by
  apply (earlyFiber s q b n before after rows rho offset width side hq).injective
  simp only [earlyActual,earlyIdeal,lift_eval]
  cases he : earlyFiber s q b n before after rows rho offset width side hq x with
  | mk source ds =>
    rcases ds with ⟨d,spec⟩
    have hgood := not_not.mp hx
    rw [he] at hgood
    change earlyGood (Bi b) (Li q) (controls (Z q n before after rho offset width side source)).length d at hgood
    simp only [VaryingControlRepairPacked.earlyActual,VaryingControlRepairPacked.earlyIdeal,
      VaryingControlRepairFiber.perm_apply]
    rw [early_program_agrees_on_good (Bi b) (Li q) (Bi_one b) (Li_pos q) _ (controls_bits _) d hgood]

theorem late_agrees (x : A s q b n before after rows) (hx : ¬ LB x) : LA x=LI x := by
  apply (lateFiber s q b n before after rows rho offset width side hq).injective
  simp only [lateActual,lateIdeal,lift_eval]
  cases he : lateFiber s q b n before after rows rho offset width side hq x with
  | mk source ds =>
    rcases ds with ⟨d,spec⟩
    have hgood := not_not.mp hx
    rw [he] at hgood
    change lateGood (Bi b) (Li q) (controls (Z q n before after rho offset width side source)).length d at hgood
    simp only [VaryingControlRepairPacked.lateActual,VaryingControlRepairPacked.lateIdeal,
      VaryingControlRepairFiber.perm_apply]
    rw [late_program_agrees_on_good (Bi b) (Li q) (Bi_one b) (Li_pos q) _ (controls_bits _) d hgood]

theorem early_actual_preserves (x : A s q b n before after rows) : EB (EA x) ↔ EB x :=
  Compact.actual_preserves_bad EA EI EB
    (early_preserves s q b n before after rows rho offset width side hq)
    (early_agrees s q b n before after rows rho offset width side hq) x

theorem late_actual_preserves (x : A s q b n before after rows) : LB (LA x) ↔ LB x :=
  Compact.actual_preserves_bad LA LI LB
    (late_preserves s q b n before after rows rho offset width side hq)
    (late_agrees s q b n before after rows rho offset width side hq) x

theorem early_repair_exact (x : A s q b n before after rows) :
    (if EB (EA x) then EI ((EA).symm (EA x)) else EA x)=EI x := by
  classical
  exact Compact.repair_exact EA EI EB
    (early_preserves s q b n before after rows rho offset width side hq)
    (early_agrees s q b n before after rows rho offset width side hq) x

theorem late_repair_exact (x : A s q b n before after rows) :
    (if LB (LA x) then LI ((LA).symm (LA x)) else LA x)=LI x := by
  classical
  exact Compact.repair_exact LA LI LB
    (late_preserves s q b n before after rows rho offset width side hq)
    (late_agrees s q b n before after rows rho offset width side hq) x

end
end IntegerMultBounds.Machine.ActiveRepairLayoutPermutation
