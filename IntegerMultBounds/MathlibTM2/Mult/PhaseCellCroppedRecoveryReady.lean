module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedCroppedRecoveryExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix

/-! Ordinary readiness for the raw principal solve/crop, independent of how
its payload is produced. The support deliberately excludes the input port. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedRecoveryPlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {s T A : ℕ} [NeZero s]

def cropControls (plan : ComputedRecoveryPlan T) (crop : RecoveryCropPlacement plan) : List (Fin T) :=
  [plan.precision,plan.packet,plan.replicas,plan.master.word,plan.master.saved,plan.master.tmp,
    plan.master.queue,plan.count,plan.tmp,plan.spare,plan.clock,plan.saved,plan.savedClock,crop.reg 3,crop.reg 4]

def cropSupport (plan : ComputedRecoveryPlan T) (crop : RecoveryCropPlacement plan) (k : Fin T) : Prop :=
  (∃ i, plan.master.scalar i = k) ∨ (∃ i, plan.master.parameters i = k) ∨
  (∃ i, plan.master.masters i = k) ∨ k ∈ plan.cropControls crop ∨ ∃ i, i ≠ 124 ∧ plan.work i = k

theorem cropSupport_ne_payload (plan : ComputedRecoveryPlan T) (crop : RecoveryCropPlacement plan)
    (k : Fin T) (hk : plan.cropSupport crop k) : k ≠ plan.work 124 := by
  rcases hk with h | h | h | h | h
  · obtain ⟨i,rfl⟩ := h; exact plan.scalar_work i 124
  · obtain ⟨i,rfl⟩ := h; exact plan.parameters_work i 124
  · obtain ⟨i,rfl⟩ := h; exact plan.master_work i 124
  · simp only [cropControls,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (plan.seed_work 124).1
    · exact (plan.seed_work 124).2.1
    · exact (plan.seed_work 124).2.2
    · exact plan.aux_work _ (by simp) 124
    · exact plan.aux_work _ (by simp) 124
    · exact plan.aux_work _ (by simp) 124
    · exact plan.aux_work _ (by simp) 124
    · exact fun h => plan.separate 124 (by simp [h])
    · exact fun h => plan.separate 124 (by simp [h])
    · exact fun h => plan.separate 124 (by simp [h])
    · exact fun h => plan.separate 124 (by simp [h])
    · exact fun h => plan.separate 124 (by simp [h])
    · exact fun h => plan.separate 124 (by simp [h])
    · exact fun h => (crop.external 3 (by simp)).1 (List.mem_ofFn.mpr ⟨124,h.symm⟩)
    · exact fun h => (crop.external 4 (by simp)).1 (List.mem_ofFn.mpr ⟨124,h.symm⟩)
  · obtain ⟨i,hi,rfl⟩ := h
    exact fun he => hi (plan.work_injective he)

structure CroppedReady (plan : ComputedRecoveryPlan T) (crop : RecoveryCropPlacement plan)
    (d : InverseMasterInput s) (r : RawRecoveryJob s) (N offset rows : ℕ)
    (wl : List (Fin (A+4))) (S : Stacks T A) : Prop where
  precision : (S.R plan.precision).length = r.problem.p
  packet : (S.R plan.packet).length = r.W
  replicas : (S.R plan.replicas).length = N
  values : ∀ i, (S.R (plan.master.parameters i)).length = d.values i
  width : S.R (plan.master.scalar .wr) = wl
  scalar : ∀ i : TblR 25, i ≠ .wr → S.R (plan.master.scalar i) = []
  masters : ∀ i, S.R (plan.master.masters i) = []
  masterScratch : ∀ k ∈ [plan.master.word,plan.master.saved,plan.master.tmp,plan.master.queue], S.R k = []
  blank : ∀ i, i ≠ 124 → S.R (plan.work i) = []
  left : ∀ i, S.L (plan.work i) = []
  scratch : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = []
  clock : S.R plan.clock = []
  saved : S.R plan.saved = []
  savedClock : S.R plan.savedClock = []
  offset : (S.R (crop.reg 3)).length = offset
  rows : (S.R (crop.reg 4)).length = rows

theorem CroppedReady.of_frame {plan : ComputedRecoveryPlan T} {crop : RecoveryCropPlacement plan}
    {d : InverseMasterInput s} {r : RawRecoveryJob s} {N offset rows : ℕ}
    {wl : List (Fin (A+4))} {S F : Stacks T A}
    (h : plan.CroppedReady crop d r N offset rows wl S)
    (hR : ∀ k, plan.cropSupport crop k → F.R k = S.R k)
    (hL : ∀ i, F.L (plan.work i) = S.L (plan.work i)) :
    plan.CroppedReady crop d r N offset rows wl F := by
  have hc k (hk : k ∈ plan.cropControls crop) := hR k (Or.inr (Or.inr (Or.inr (Or.inl hk))))
  have hs i := hR (plan.master.scalar i) (Or.inl ⟨i,rfl⟩)
  have hv i := hR (plan.master.parameters i) (Or.inr (Or.inl ⟨i,rfl⟩))
  have hm i := hR (plan.master.masters i) (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩)))
  have hw i (hi : i ≠ 124) := hR (plan.work i) (Or.inr (Or.inr (Or.inr (Or.inr ⟨i,hi,rfl⟩))))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hc _ (by simp [cropControls])]; exact h.precision
  · rw [hc _ (by simp [cropControls])]; exact h.packet
  · rw [hc _ (by simp [cropControls])]; exact h.replicas
  · intro i; rw [hv]; exact h.values i
  · rw [hs]; exact h.width
  · intro i hi; rw [hs]; exact h.scalar i hi
  · intro i; rw [hm]; exact h.masters i
  · intro k hk
    have hm : k ∈ plan.cropControls crop := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simp [cropControls]
    rw [hc k hm]; exact h.masterScratch k hk
  · intro i hi; rw [hw i hi]; exact h.blank i hi
  · intro i; rw [hL]; exact h.left i
  · intro k hk
    have hm : k ∈ plan.cropControls crop := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simp [cropControls]
    rw [hc k hm]; exact h.scratch k hk
  · rw [hc _ (by simp [cropControls])]; exact h.clock
  · rw [hc _ (by simp [cropControls])]; exact h.saved
  · rw [hc _ (by simp [cropControls])]; exact h.savedClock
  · rw [hc _ (by simp [cropControls])]; exact h.offset
  · rw [hc _ (by simp [cropControls])]; exact h.rows

def inputState (plan : ComputedRecoveryPlan T) (source : Fin T)
    (payload tail : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update S.R source tail) (plan.work 124) payload)}

-- Supplied-counter handoff: restore from commit 221f84ae if needed.

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedRecoveryPlan
