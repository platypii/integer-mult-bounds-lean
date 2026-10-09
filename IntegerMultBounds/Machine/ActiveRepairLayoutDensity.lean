import IntegerMultBounds.Machine.ActiveRepairLayoutPermutation
import IntegerMultBounds.Machine.VaryingControlRepairDensity
import IntegerMultBounds.Compact.TapeRepairStage

/-! Exceptional cardinalities of the unchanged full layout, transported
through its complete source and spectator fibers. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutDensity
noncomputable section
attribute [local instance] Classical.propDecidable
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairLayoutPermutationFiber ActiveRepairLayoutPermutation

variable (s : Shape) (q b n before after rows rho offset width : ℕ)
variable (side : ActiveRepairRankHeadersData.SourceSide) (hq : 1≤q)
abbrev A := Address s (n*b) (n*q) before after rows
local notation "EB" => earlyBad s q b n before after rows rho offset width side hq
local notation "LB" => lateBad s q b n before after rows rho offset width side hq

 theorem early_bad_count (hbq : b+3≤q) :
    (Nat.card {x : A s q b n before after rows // EB x} : ℝ)≤
      VaryingControlRepairDensity.earlyDensity q b n*Nat.card (A s q b n before after rows) := by
  classical
  let e := earlyFiber s q b n before after rows rho offset width side hq
  let be : {x : A s q b n before after rows // EB x} ≃
      {x : VaryingControlRepairPacked.Early q b
        (controlWord before after q rho n offset width side)
        (EarlySpectator s (n*b) rows) //
        VaryingControlRepairPacked.earlyBad q b
          (controlWord before after q rho n offset width side) x} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  rw [Nat.card_congr be,Nat.card_congr e]
  rw [VaryingControlRepairDensity.early_card q b n hq _ (control_length _ _ _ _ _ _ _ _)]
  simpa only [Nat.cast_mul] using
    VaryingControlRepairDensity.early_bad_count (S:=EarlySpectator s (n*b) rows) q b n hbq
      (controlWord before after q rho n offset width side)
      (control_length before after q rho n offset width side)

 theorem late_bad_count (hbq : b+3≤q) :
    (Nat.card {x : A s q b n before after rows // LB x} : ℝ)≤
      VaryingControlRepairDensity.lateDensity q b n*Nat.card (A s q b n before after rows) := by
  classical
  let e := lateFiber s q b n before after rows rho offset width side hq
  let be : {x : A s q b n before after rows // LB x} ≃
      {x : VaryingControlRepairPacked.Late q b
        (controlWord before after q rho n offset width side)
        (LateSpectator s (n*b) rows) //
        VaryingControlRepairPacked.lateBad q b
          (controlWord before after q rho n offset width side) x} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  rw [Nat.card_congr be,Nat.card_congr e]
  rw [VaryingControlRepairDensity.late_card q b n hq _ (control_length _ _ _ _ _ _ _ _)]
  simpa only [Nat.cast_mul] using
    VaryingControlRepairDensity.late_bad_count (S:=LateSpectator s (n*b) rows) q b n hbq
      (controlWord before after q rho n offset width side)
      (control_length before after q rho n offset width side)

/-- A paid width-density estimate yields the natural-number sparse-hole
premise used by the physical endpoint budgets, for every complete rank order. -/
theorem holes_sparse {X : Type*} [Fintype X] {M : ℕ} (e : X ≃ Fin M)
    (bad : X → Prop) [DecidablePred bad] (data : X → List Bool) (δ : ℝ) (A D : ℕ)
    (hcount : (Nat.card {x : X // bad x} : ℝ)≤δ*Nat.card X)
    (hδ : δ*(A+1)≤D) :
    Reinsert.holes (Compact.stream e bad data)*(A+1)≤D*M := by
  rw [Compact.holes_stream,Compact.badRanks_length]
  have hc : Nat.card X=M := by rw [Nat.card_congr e,Nat.card_fin]
  rw [hc] at hcount
  have hh := mul_le_mul_of_nonneg_right hcount (by positivity : (0:ℝ)≤A+1)
  have hd := mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg M)
  have h : (Nat.card {x : X // bad x} : ℝ)*(A+1)≤(D:ℝ)*M := by nlinarith
  exact_mod_cast h

 theorem early_holes_sparse {M : ℕ} (e : A s q b n before after rows ≃ Fin M)
    (data : A s q b n before after rows → List Bool) (A D : ℕ)
    (hbq : b+3≤q) (hd : VaryingControlRepairDensity.earlyDensity q b n*(A+1)≤D) :
    Reinsert.holes (Compact.stream e EB data)*(A+1)≤D*M := by
  classical
  exact holes_sparse e EB data _ A D
    (early_bad_count s q b n before after rows rho offset width side hq hbq) hd

 theorem late_holes_sparse {M : ℕ} (e : A s q b n before after rows ≃ Fin M)
    (data : A s q b n before after rows → List Bool) (A D : ℕ)
    (hbq : b+3≤q) (hd : VaryingControlRepairDensity.lateDensity q b n*(A+1)≤D) :
    Reinsert.holes (Compact.stream e LB data)*(A+1)≤D*M := by
  classical
  exact holes_sparse e LB data _ A D
    (late_bad_count s q b n before after rows rho offset width side hq hbq) hd

end
end IntegerMultBounds.Machine.ActiveRepairLayoutDensity
