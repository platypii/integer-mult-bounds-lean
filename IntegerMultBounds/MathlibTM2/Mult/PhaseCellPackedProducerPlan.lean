module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedExactTileSchedule

/-! Static wiring and ordinary tape readiness for a packed producer. The plan
contains no execution premise. Its result bank is outside the readiness frame,
so independent producers can be composed by updating only their owned outputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

structure PackedProducerPlan (T Q : ℕ) where
  hR : rpStates ≤ Q
  hQ : SS.states ≤ Q
  work : Fin 325 → Fin T
  hwork : Function.Injective work
  src : Fin T
  saved : Fin T
  count : Fin T
  tmp : Fin T
  spare : Fin T
  result : Fin T
  clock : Fin T
  savedClock : Fin T
  hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup
  hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock]

namespace PackedProducerPlan
variable {T Q A s : ℕ} [NeZero s]

def support (plan : PackedProducerPlan T Q) : List (Fin T) :=
  List.ofFn plan.work++[plan.src,plan.saved,plan.count,plan.tmp,plan.spare,plan.clock,plan.savedClock]

structure Ready (plan : PackedProducerPlan T Q) (records : List (PackedNormalizedJob A s))
    (rest : List (Fin (A+4))) (S : Stacks T A) : Prop where
  hblank : ∀ i, S.R (plan.work i) = []
  hleft : ∀ i, S.L (plan.work i) = []
  hscratch : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = []
  hsource : S.R plan.src = descriptorScheduleTape plan.work PackedNormalizedJob.words records.reverse++rest
  hclock : (S.R plan.clock).length = records.length
  hsaved : S.R plan.saved = []
  hsavedClock : S.R plan.savedClock = []

theorem Ready.of_frame {plan : PackedProducerPlan T Q} {records : List (PackedNormalizedJob A s)}
    {rest : List (Fin (A+4))} {S F : Stacks T A} (h : plan.Ready records rest S)
    (hR : ∀ i ∈ plan.support, F.R i = S.R i) (hL : ∀ i, F.L (plan.work i) = S.L (plan.work i)) :
    plan.Ready records rest F := by
  have hw (i : Fin 325) : F.R (plan.work i) = S.R (plan.work i) :=
    hR _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  have hc (i : Fin T) (hi : i ∈ [plan.src,plan.saved,plan.count,plan.tmp,plan.spare,plan.clock,plan.savedClock]) :
      F.R i = S.R i := hR i (List.mem_append_right _ hi)
  refine ⟨fun i => (hw i).trans (h.hblank i),fun i => (hL i).trans (h.hleft i),?_,?_,?_,?_,?_⟩
  · intro i hi
    rw [hc i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto)]
    exact h.hscratch i hi
  · rw [hc _ (by simp)]; exact h.hsource
  · rw [hc _ (by simp)]; exact h.hclock
  · rw [hc _ (by simp)]; exact h.hsaved
  · rw [hc _ (by simp)]; exact h.hsavedClock

theorem Ready.update {plan : PackedProducerPlan T Q} {records : List (PackedNormalizedJob A s)}
    {rest : List (Fin (A+4))} {S : Stacks T A} (h : plan.Ready records rest S)
    (k : Fin T) (hk : k ∉ plan.support) (raw : List (Fin (A+4))) :
    plan.Ready records rest {S with R := Function.update S.R k raw} := by
  apply h.of_frame (F := {S with R := Function.update S.R k raw}) _ (fun _ => rfl)
  intro i hi
  exact Function.update_of_ne (by intro he; subst i; exact hk hi) _ _

noncomputable def program {P U : Type} (plan : PackedProducerPlan T Q) : Pr P T Q A U :=
  descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
    (packedNormalizedDescriptorStep plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result plan.hR plan.hQ)

noncomputable def timeCost {U : Type} (plan : PackedProducerPlan T Q) (records : List (PackedNormalizedJob A s)) : ℕ :=
  (records.reverse.map (fun r => takeDescriptorBankCost (placedDescriptorFields plan.work r.words)+
    r.setupTime+r.cleanup (U := U) plan.hR plan.hQ+3)).sum+
    (records.reverse.map (fun r => r.Fs.length*r.replicaTime)).sum+6*records.length+
    2*(descriptorScheduleTape plan.work PackedNormalizedJob.words records.reverse).length+10

noncomputable def workspace {U : Type} (plan : PackedProducerPlan T Q) (records : List (PackedNormalizedJob A s)) : ℕ :=
  (records.reverse.map PackedNormalizedJob.outputVolume).sum+
    (records.reverse.map (fun r => r.stepStock (U := U) plan.work plan.hR plan.hQ)).foldr max 0+6*records.length+
    2*(descriptorScheduleTape plan.work PackedNormalizedJob.words records.reverse).length+8

/-- One actual producer run retains exact bytes, per-core numerical guarantees,
its time bill, and maximum scratch stock. -/
theorem exec {P U : Type} (plan : PackedProducerPlan T Q) (body : P → Pr P T Q A U) (hA : 96 ≤ A)
    (records : List (PackedNormalizedJob A s)) (W : ℕ) (hwidth : ∀ r ∈ records, r.W = W)
    (t : ℕ) [NeZero t] (ht : ∀ r ∈ records, r.t = t)
    (hp : ∀ r ∈ records, 4 ≤ r.p) (htarget : ∀ r ∈ records, r.p+2 ≤ r.targetOut)
    (hlocal : ∀ r ∈ records, r.localityTarget = r.targetOut)
    (J : PackedNormalizedJob A s → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : ∀ r ∈ records, J r ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t r.α = 1)
    (B L : ℕ) (hreplicas : ∀ r ∈ records, r.Fs.length = B)
    (hcore : ∀ r ∈ records, IntegerMultBounds.NLogN.PhaseCellMatrix.coreLength s r.coreWidth r.k = L)
    (rest : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A) (hready : plan.Ready records rest S) :
    ∃ v' n, ∃ rows : Fin records.length → Fin B → List GaussianInt,
      v'.user = v.user ∧ n ≤ plan.timeCost (U := U) records ∧
      Exec body plan.program (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R plan.result
          ((List.ofFn fun i => (List.ofFn fun j => cstream A W (rows i j)).flatten).flatten++S.R plan.result))}) ∧
      (∀ i j, (rows i j).length = L) ∧
      (∀ i : Fin records.length, (records.get i).ExactRowOutput (J (records.get i)) (List.ofFn (rows i))) ∧
      ∀ C, mnProgPush (plan.program (P := P) (U := U) (A := A)) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(C+1)*plan.workspace (U := U) records)
          depth plan.program (Host.mk v S) n
          (Host.mk v' {S with R := (Function.update S.R plan.result
            ((List.ofFn fun i => (List.ofFn fun j => cstream A W (rows i j)).flatten).flatten++S.R plan.result))}) := by
  exact packedExactTileSchedule_exec plan.hR plan.hQ hA plan.work plan.hwork plan.src plan.saved plan.count plan.tmp plan.spare
    plan.result plan.clock plan.savedClock plan.hreg plan.hsep records W hwidth v S t ht hp htarget hlocal J hJ B L hreplicas hcore rest
    hready.hblank hready.hleft hready.hscratch hready.hsource hready.hclock hready.hsaved hready.hsavedClock

end PackedProducerPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
