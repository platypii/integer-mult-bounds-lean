import IntegerMultBounds.Machine.ActiveRepairLayoutPermutationFields
import IntegerMultBounds.Machine.CompactActiveTargetLayout
import IntegerMultBounds.Machine.SelectedSourceBitsData
import IntegerMultBounds.Machine.BinaryAddressTableData

/-! The actual unchanged active-target address is a complete varying-source
fiber: both source coordinates and all unused tails/slack/back/payload bits
are retained, and only target and compact dirty fields enter the local map. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutPermutationFiber
noncomputable section
open CompactGadgetReservationShape CompactActiveTargetLayout
open ActiveRepairLayoutPermutationFields

instance addressFintype (s : Shape) (w m before after rows : ℕ) :
    Fintype (Address s w m before after rows) :=
  Fintype.ofEquiv (Fields s w m before after rows) (fieldsEquiv s w m before after rows).symm

abbrev Source (before after : ℕ) := Fin (2^before) × Fin (2^after)
abbrev EarlySpectator (s : Shape) (w rows : ℕ) :=
  Fin rows × Fin (2^w) × Fin (2^(s.H-w)) × Fin (2^(s.H-w)) ×
    Fin (2^s.F) × Fin (2^(s.H+s.B)) × Fin s.payload
abbrev LateSpectator (s : Shape) (w rows : ℕ) :=
  Fin rows × Fin (2^(s.H-w)) × Fin (2^(s.H-w)) ×
    Fin (2^s.F) × Fin (2^(s.H+s.B)) × Fin s.payload

def sourceWord (before after offset width : ℕ) (side : ActiveRepairRankHeadersData.SourceSide)
    (x : Source before after) :=
  match side with
  | .before => Gather.field (BinaryAddressTableData.row before x.1.val) offset width
  | .after => Gather.field (BinaryAddressTableData.row after x.2.val) offset width

def controlWord (before after q rho n offset width : ℕ)
    (side : ActiveRepairRankHeadersData.SourceSide) (x : Source before after) :=
  SelectedSourceBitsData.selected (sourceWord before after offset width side x) q rho n

@[simp] theorem control_length (before after q rho n offset width : ℕ)
    (side : ActiveRepairRankHeadersData.SourceSide) (x : Source before after) :
    (controlWord before after q rho n offset width side x).length=n :=
  SelectedSourceBitsData.selected_length _ _ _ _

variable (s : Shape) (q b n before after rows rho offset width : ℕ)
variable (side : ActiveRepairRankHeadersData.SourceSide) (hq : 1≤q)

abbrev Z := controlWord before after q rho n offset width side
abbrev A := Address s (n*b) (n*q) before after rows

def earlyEquiv : A s q b n before after rows ≃
    VaryingControlRepairPacked.Early q b (Z q n before after rho offset width side)
      (EarlySpectator s (n*b) rows) where
  toFun x := ⟨(x.activeBefore,x.activeAfter),
    (ActiveRepairLayoutPermutationFields.earlyEquiv q b n _ hq (control_length _ _ _ _ _ _ _ _ _)
      (x.target,x.t),(x.row,x.u,x.uTail,x.tTail,x.frontSlack,x.back,x.payload))⟩
  invFun x :=
    let y := (ActiveRepairLayoutPermutationFields.earlyEquiv q b n _ hq (control_length _ _ _ _ _ _ _ _ _)).symm x.2.1
    ⟨x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,y.2,x.2.2.2.2.2.1,x.2.2.2.2.2.2.1,
      x.1.1,y.1,x.1.2,x.2.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2.2⟩
  left_inv x := by
    simp only [Equiv.symm_apply_apply]
  right_inv x := by
    cases x with | mk source ds =>
      rcases source with ⟨pre,post⟩
      rcases ds with ⟨localState,spectator⟩
      simp only [Prod.mk.eta,Equiv.apply_symm_apply]

def lateEquiv : A s q b n before after rows ≃
    VaryingControlRepairPacked.Late q b (Z q n before after rho offset width side)
      (LateSpectator s (n*b) rows) where
  toFun x := ⟨(x.activeBefore,x.activeAfter),
    (ActiveRepairLayoutPermutationFields.lateEquiv q b n _ hq (control_length _ _ _ _ _ _ _ _ _)
      (x.u,(x.target,x.t)),(x.row,x.uTail,x.tTail,x.frontSlack,x.back,x.payload))⟩
  invFun x :=
    let y := (ActiveRepairLayoutPermutationFields.lateEquiv q b n _ hq (control_length _ _ _ _ _ _ _ _ _)).symm x.2.1
    ⟨x.2.2.1,y.1,x.2.2.2.1,y.2.2,x.2.2.2.2.1,x.2.2.2.2.2.1,
      x.1.1,y.2.1,x.1.2,x.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2⟩
  left_inv x := by simp only [Equiv.symm_apply_apply]
  right_inv x := by
    cases x with | mk source ds =>
      rcases source with ⟨pre,post⟩
      rcases ds with ⟨localState,spectator⟩
      simp only [Prod.mk.eta,Equiv.apply_symm_apply]

end
end IntegerMultBounds.Machine.ActiveRepairLayoutPermutationFiber
