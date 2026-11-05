module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedSeamCrops

/-! Shared placement/readiness for retained seam crops. The source is borrowed
only while archiving; retiring it restores the original blank result register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement PhaseCellInterface

structure SeamCropPlan (T : ℕ) (source : Fin T) where
  clock : Fin T
  clockSave : Fin T
  sourceSave : Fin T
  dst : Fin T
  savedSkip : Fin T
  saved : Fin T
  tmp : Fin T
  rows : Fin T
  width : Fin T
  retireCount : Fin T
  trash : Fin T
  retireTmp : Fin T
  skip : ℕ → Fin T
  count : ℕ → Fin T

namespace SeamCropPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U} {source : Fin T}

def commonPorts (plan : SeamCropPlan T source) : List (Fin T) :=
  [plan.clock,plan.clockSave,plan.sourceSave,source,plan.dst,plan.savedSkip,plan.saved,plan.tmp,
    plan.rows,plan.width,plan.retireCount,plan.trash,plan.retireTmp]

def cropPorts (plan : SeamCropPlan T source) (k : ℕ) : List (Fin T) :=
  [plan.clock,plan.clockSave,plan.sourceSave,plan.skip k,plan.count k,source,plan.dst,plan.savedSkip,
    plan.saved,plan.tmp,plan.rows,plan.width,plan.retireCount,plan.trash,plan.retireTmp]

def cleanPorts (plan : SeamCropPlan T source) : List (Fin T) :=
  [plan.clockSave,plan.sourceSave,plan.savedSkip,plan.saved,plan.tmp,plan.retireCount,plan.trash,plan.retireTmp]

def program (plan : SeamCropPlan T source) (ks : List ℕ) : Pr P T Q A U :=
  retainedSeamCrops plan.clock plan.clockSave plan.sourceSave source plan.dst plan.savedSkip plan.saved plan.tmp
    plan.rows plan.width plan.retireCount plan.trash plan.retireTmp plan.skip plan.count ks

/-- Only these port pairs affect code; mathematical core indices are metadata. -/
def portProgram (plan : SeamCropPlan T source) : List (Fin T × Fin T) → Pr P T Q A U
  | [] => .act .done
  | (skip,count)::ports => .seq
      (retainedSeamArchive plan.clock plan.clockSave plan.sourceSave skip count source plan.dst plan.savedSkip
        plan.saved plan.tmp plan.rows plan.width plan.retireCount plan.trash plan.retireTmp)
      (plan.portProgram ports)

omit [NeZero s] in
theorem program_eq_portProgram (plan : SeamCropPlan T source) (ks : List ℕ) :
    plan.program (Q := Q) (P := P) (A := A) (U := U) ks =
      plan.portProgram (ks.map (fun k => (plan.skip k,plan.count k))) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    change Prog.seq _ (plan.program ks) = Prog.seq _ (plan.portProgram _)
    rw [ih]

structure Ready (plan : SeamCropPlan T source) (p s coreWidth replicas : ℕ) (ks : List ℕ) (S : Stacks T A) : Prop where
  common : plan.commonPorts.Nodup
  regs : ∀ k ∈ ks, (plan.cropPorts k).Nodup
  clock : (S.R plan.clock).length = replicas
  skip : ∀ k ∈ ks, (S.R (plan.skip k)).length = coreStart coreWidth k*(2*p+13)
  count : ∀ k ∈ ks, (S.R (plan.count k)).length = coreLength s coreWidth k*(2*p+13)
  rows : (S.R plan.rows).length = s
  width : (S.R plan.width).length = 2*p+13
  clean : ∀ i ∈ plan.cleanPorts, S.R i = []

omit [NeZero s] in
theorem Ready.updateSource {plan : SeamCropPlan T source} {p coreWidth replicas : ℕ} {ks : List ℕ} {S : Stacks T A}
    (ready : plan.Ready p s coreWidth replicas ks S) (output : List (Fin (A+4))) :
    plan.Ready p s coreWidth replicas ks {S with R := Function.update S.R source output} := by
  have hc := ready.common
  dsimp only [commonPorts] at hc
  regs_ne hc
  refine {ready with clock := ?_,skip := ?_,count := ?_,rows := ?_,width := ?_,clean := ?_}
  · simpa only [Function.update_of_ne ‹plan.clock ≠ source›] using ready.clock
  · intro k hk
    have hr := ready.regs k hk
    dsimp only [cropPorts] at hr
    regs_ne hr
    simpa only [Function.update_of_ne ‹plan.skip k ≠ source›] using ready.skip k hk
  · intro k hk
    have hr := ready.regs k hk
    dsimp only [cropPorts] at hr
    regs_ne hr
    simpa only [Function.update_of_ne ‹plan.count k ≠ source›] using ready.count k hk
  · simpa only [Function.update_of_ne ‹source ≠ plan.rows›.symm] using ready.rows
  · simpa only [Function.update_of_ne ‹source ≠ plan.width›.symm] using ready.width
  · intro i hi
    have hoff : i ≠ source := by
      simp only [cleanPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | assumption | (apply Ne.symm; assumption)
    simpa only [Function.update_of_ne hoff] using ready.clean i hi

/-- Archive every crop from the same certified full-line result, then erase that
result. All registers except the archive destination return to the baseline. -/
theorem archiveRetire_exec_within (plan : SeamCropPlan T source) (p coreWidth : ℕ)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (ks : List ℕ) (output : List (Fin (A+4)))
    (hproduced : ExactCoreProduced p s (fun _ => 0) J r output)
    (hstart : ∀ k ∈ ks, coreStart coreWidth k ≤ s)
    (v : HS T Q A U) (S : Stacks T A) (ready : plan.Ready p s coreWidth r.inputs.length ks S)
    (hsource : S.R source = []) (depth : ℕ) :
    ∃ rss : List (List (List GaussianInt)), ∃ v' n, v'.user = v.user ∧
      n ≤ (ks.length*(80*(r.inputs.length*s*(2*p+13))+14)+1)+2*(r.inputs.length*s*(2*p+13))+2 ∧
      List.Forall₂ (SeamCropRows p coreWidth r J) ks rss ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v {S with R := Function.update S.R source output})+depth+
        2*(ks.length*(80*(r.inputs.length*s*(2*p+13))+14)+1)) depth
        (.seq (plan.program ks) (uclear source))
        (Host.mk v {S with R := Function.update S.R source output}) n
        (Host.mk v' {S with R := (Function.update S.R plan.dst
          ((rss.reverse.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++S.R plan.dst))}) := by
  let M : Stacks T A := {S with R := Function.update S.R source output}
  have readyM := ready.updateSource output
  have hc := ready.common
  dsimp only [commonPorts] at hc
  regs_ne hc
  obtain ⟨rss,v₁,F,n₁,hu₁,hn₁,he₁,hd,hi,ho,hL,hframe,hgood⟩ := retainedSeamCrops_exec (body := body)
    plan.clock plan.clockSave plan.sourceSave source plan.dst plan.savedSkip plan.saved plan.tmp
    plan.rows plan.width plan.retireCount plan.trash plan.retireTmp plan.skip plan.count ks readyM.regs
    p coreWidth r J output hproduced hstart v M (Function.update_self _ _ _) readyM.clock readyM.skip readyM.count
    readyM.rows readyM.width readyM.clean
  have hs : F.R source = output := (hframe source ‹source ≠ plan.dst›).trans (Function.update_self _ _ _)
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec (body := body) source v₁ F
  rw [hs,ExactCoreProduced.full_output_length hproduced] at he₂
  have hend : {F with R := Function.update F.R source []} =
      {S with R := (Function.update S.R plan.dst
        ((rss.reverse.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++S.R plan.dst))} := by
    refine Stacks.ext hi ho hL ?_
    funext k
    by_cases hk : k = source
    · subst k
      simp only [Function.update_self,Function.update_of_ne ‹source ≠ plan.dst›,hsource]
    by_cases hd' : k = plan.dst
    · subst k
      simpa only [Function.update_of_ne ‹source ≠ plan.dst›.symm,Function.update_self,
        M,Function.update_of_ne ‹source ≠ plan.dst›.symm] using hd
    · simp only [Function.update_of_ne hk,Function.update_of_ne hd',hframe k hd',M]
  rw [hend] at he₂
  have hw₁ := retainedSeamCrops_within he₁ hn₁ depth
  have hF := hw₁.final
  dsimp only [M] at hF
  have hclear : mnNativePushBound 0 (uclear (P := P) (Q := Q) (A := A) (U := U) source) := by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]
  have hw₂ := mn_native_exec_within he₂ 0 hclear depth (mnSize (Host.mk v₁ F)+depth) (by omega)
  refine ⟨rss,v₂,n₁+(2*(r.inputs.length*s*(2*p+13))+2),hu₂.trans hu₁,by omega,hgood,?_⟩
  exact ExecWithin.seq hw₁ (hw₂.mono (by intro d z hz; omega))

/-- At most three crops, including final erasure of the shared full-line result. -/
theorem archiveRetire_three_cost (ks : List ℕ) (hcount : ks.length ≤ 3) (volume : ℕ) :
    (ks.length*(80*volume+14)+1)+2*volume+2 ≤ 242*volume+45 ∧
      2*(ks.length*(80*volume+14)+1) ≤ 480*volume+86 := by
  have h := retainedSeamCrops_three_cost ks hcount volume
  constructor <;> omega

end SeamCropPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
