import IntegerMultBounds.Machine.ActivePrefixStageHeadersBudget
import IntegerMultBounds.Machine.BinaryDescriptorCompare

/-! The source order used by the two original-slot stages is physically
computed from their original binary source/target slot words. Comparison
retains both words and heads; its single-bit flag has paid cleanup. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageOrderCompare
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open RecursiveChildQuotientsConstant (bits bits_value)
variable {s : Shape} {a : ℕ}

def input (v : Stage s) := BinaryDescriptorCompare.input (q:=a) (bits v.source.val) (bits v.target.val)
def output (v : Stage s) := BinaryDescriptorCompare.output (q:=a) (bits v.source.val) (bits v.target.val)
def program := BinaryDescriptorCompare.program (q:=a)
def cleanup := BinaryDescriptorCompare.eraseFlag (q:=a)
def cost (v : Stage s) := BinaryDescriptorCompare.cost (bits v.source.val) (bits v.target.val)

theorem runs (v : Stage s) : HoareTime (program (a:=a))
    (fun x => x=input v) (fun x => x=output v) (cost v) :=
  BinaryDescriptorCompare.compare_hoare _ _

theorem early_flag (v : Stage s) (horder : v.source.val<v.target.val) :
    (output (a:=a) v).tape 2 0=bitSymbol true := by
  rw [output,BinaryDescriptorCompare.result_at_zero,bits_value,bits_value]
  simp only [horder,decide_true]

theorem late_flag (v : Stage s) (horder : v.target.val<v.source.val) :
    (output (a:=a) v).tape 2 0=bitSymbol false := by
  rw [output,BinaryDescriptorCompare.result_at_zero,bits_value,bits_value]
  have h : ¬v.source.val<v.target.val := by omega
  simp only [h,decide_false]

theorem late_of_not_early (v : Stage s) (h : ¬v.source.val<v.target.val) :
    v.target.val<v.source.val := by
  have hd : v.source.val≠v.target.val := fun he => v.distinct (Fin.ext he)
  omega

theorem cleans (v : Stage s) : HoareTime (cleanup (a:=a))
    (fun x => x=output v) (fun x => x=input v) 1 :=
  BinaryDescriptorCompare.eraseFlag_hoare _ _

theorem cost_linear (v : Stage s) (rows : ℕ) (hG : 1≤s.guard)
    (hGK : s.guard+1≤s.chunk) (hrows : 0<rows) (hrecord : s.bits+1≤s.payload) :
    cost v+1≤24*(rows*s.recordWidth) := by
  have horder : ActivePrefixStageHeadersSchedule.Ordered
      (if v.source.val<v.target.val then .early else .late) v := by
    by_cases h : v.source.val<v.target.val
    · simp only [h,ite_true,ActivePrefixStageHeadersSchedule.Ordered]
    · simpa only [h,ite_false,ActivePrefixStageHeadersSchedule.Ordered] using late_of_not_early v h
  have hb := ActivePrefixStageHeadersBudget.original_bounds
    (if v.source.val<v.target.val then .early else .late) v rows hG hGK horder hrows hrecord
  have hs := hb.1 11
  have ht := hb.1 12
  change v.source.val≤rows*s.recordWidth at hs
  change v.target.val≤rows*s.recordWidth at ht
  have hxs := ActiveRepairRankHeadersCommands.bits_length v.source.val
  have hys := ActiveRepairRankHeadersCommands.bits_length v.target.val
  have hp : 0<s.payload := by omega
  have hvol : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  unfold cost BinaryDescriptorCompare.cost
  omega

end
end IntegerMultBounds.Machine.ActivePrefixStageOrderCompare
