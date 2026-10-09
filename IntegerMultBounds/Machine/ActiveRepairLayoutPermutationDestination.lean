import IntegerMultBounds.Machine.ActiveRepairLayoutPermutation
import IntegerMultBounds.Machine.ActiveRepairLayoutPermutationWords

/-! Actual global inverse-then-ideal destinations change only the recovered
V/T/U fields. The words computed on tapes identify those fields exactly. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutPermutationDestination
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairLayoutPermutationFiber ActiveRepairLayoutPermutation
open IntegerMultBounds.Compact IntegerMultBounds.Compact.PowerTwo

variable (s : Shape) (q b n before after rows rho offset width : ℕ)
variable (side : ActiveRepairRankHeadersData.SourceSide) (hq : 1≤q)

abbrev A := Address s (n*b) (n*q) before after rows
abbrev Z := controlWord before after q rho n offset width side

local notation "EA" => earlyActual s q b n before after rows rho offset width side hq
local notation "EI" => earlyIdeal s q b n before after rows rho offset width side hq
local notation "LA" => lateActual s q b n before after rows rho offset width side hq
local notation "LI" => lateIdeal s q b n before after rows rho offset width side hq

def earlyLocalDestination (x : A s q b n before after rows) :=
  let z := Z q n before after rho offset width side (x.activeBefore,x.activeAfter)
  let e := ActiveRepairLayoutPermutationFields.earlyEquiv q b n z hq (control_length _ _ _ _ _ _ _ _ _)
  e.symm (Tperm q b z ((Sperm q b z).symm (e (x.target,x.t))))
def lateLocalDestination (x : A s q b n before after rows) :=
  let z := Z q n before after rho offset width side (x.activeBefore,x.activeAfter)
  let e := ActiveRepairLayoutPermutationFields.lateEquiv q b n z hq (control_length _ _ _ _ _ _ _ _ _)
  e.symm (lateTperm q b z ((lateSperm q b z).symm (e (x.u,(x.target,x.t)))))

theorem early_address (x : A s q b n before after rows) :
    EI ((EA).symm x)={x with
      target:=(earlyLocalDestination s q b n before after rows rho offset width side hq x).1,
      t:=(earlyLocalDestination s q b n before after rows rho offset width side hq x).2} := by
  apply (earlyFiber s q b n before after rows rho offset width side hq).injective
  rw [early_ideal_fiber,early_inverse_fiber]
  simp only [earlyFiber,ActiveRepairLayoutPermutationFiber.earlyEquiv,
    VaryingControlRepairPacked.earlyActual,VaryingControlRepairPacked.earlyIdeal,
    VaryingControlRepairFiber.perm_apply,VaryingControlRepairFiber.perm_symm_apply,
    Equiv.coe_fn_mk,earlyLocalDestination,Prod.mk.eta,Equiv.apply_symm_apply]

theorem late_address (x : A s q b n before after rows) :
    LI ((LA).symm x)={x with
      target:=(lateLocalDestination s q b n before after rows rho offset width side hq x).2.1,
      t:=(lateLocalDestination s q b n before after rows rho offset width side hq x).2.2,
      u:=(lateLocalDestination s q b n before after rows rho offset width side hq x).1} := by
  apply (lateFiber s q b n before after rows rho offset width side hq).injective
  rw [late_ideal_fiber,late_inverse_fiber]
  simp only [lateFiber,ActiveRepairLayoutPermutationFiber.lateEquiv,
    VaryingControlRepairPacked.lateActual,VaryingControlRepairPacked.lateIdeal,
    VaryingControlRepairFiber.perm_apply,VaryingControlRepairFiber.perm_symm_apply,
    Equiv.coe_fn_mk,lateLocalDestination,Prod.mk.eta,Equiv.apply_symm_apply]

theorem early_words (hb : 1≤b) (hbq : b+1≤q) (x : A s q b n before after rows) :
    earlyLocalDestination s q b n before after rows rho offset width side hq x=
      ActiveRepairLayoutPermutationWords.earlyRepaired q b n hb hbq
        (Z q n before after rho offset width side (x.activeBefore,x.activeAfter))
        (BinaryAddressTableData.row (n*q) x.target.val) (BinaryAddressTableData.row (n*b) x.t.val)
        (control_length _ _ _ _ _ _ _ _ _) (BinaryAddressTableData.row_length _ _)
        (BinaryAddressTableData.row_length _ _) := by
  have h := ActiveRepairLayoutPermutationWords.early_destination q b n hb hbq
    (Z q n before after rho offset width side (x.activeBefore,x.activeAfter))
    (BinaryAddressTableData.row (n*q) x.target.val) (BinaryAddressTableData.row (n*b) x.t.val)
    (control_length _ _ _ _ _ _ _ _ _) (BinaryAddressTableData.row_length _ _)
    (BinaryAddressTableData.row_length _ _)
  simpa only [ActiveRepairLayoutPermutationWords.earlyWords,
    ActiveRepairLayoutPermutationWords.wordFin_row,earlyLocalDestination] using h

theorem late_words (hb : 1≤b) (hbq : b+1≤q) (x : A s q b n before after rows) :
    lateLocalDestination s q b n before after rows rho offset width side hq x=
      ActiveRepairLayoutPermutationWords.lateRepaired q b n hb hbq
        (Z q n before after rho offset width side (x.activeBefore,x.activeAfter))
        (BinaryAddressTableData.row (n*q) x.target.val) (BinaryAddressTableData.row (n*b) x.t.val)
        (BinaryAddressTableData.row (n*b) x.u.val)
        (control_length _ _ _ _ _ _ _ _ _) (BinaryAddressTableData.row_length _ _)
        (BinaryAddressTableData.row_length _ _) (BinaryAddressTableData.row_length _ _) := by
  have h := ActiveRepairLayoutPermutationWords.late_destination q b n hb hbq
    (Z q n before after rho offset width side (x.activeBefore,x.activeAfter))
    (BinaryAddressTableData.row (n*q) x.target.val) (BinaryAddressTableData.row (n*b) x.t.val)
    (BinaryAddressTableData.row (n*b) x.u.val)
    (control_length _ _ _ _ _ _ _ _ _) (BinaryAddressTableData.row_length _ _)
    (BinaryAddressTableData.row_length _ _) (BinaryAddressTableData.row_length _ _)
  simpa only [ActiveRepairLayoutPermutationWords.lateWords,ActiveRepairLayoutPermutationWords.earlyWords,
    ActiveRepairLayoutPermutationWords.wordFin_row,lateLocalDestination] using h

end
end IntegerMultBounds.Machine.ActiveRepairLayoutPermutationDestination
