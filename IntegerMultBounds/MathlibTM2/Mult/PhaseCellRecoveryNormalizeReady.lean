module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizeRecoveryFromUnary

/-! Ordinary normalization inputs are stable under a frame on their support.
The source and generated packet-width header are supplied by the crop stage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix
namespace RecoveryNormalizePlan
variable {T A s : ℕ} [NeZero s]

def support (plan : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue plan) (k : Fin T) : Prop :=
  (∃ i, plan.scalar i = k) ∨ (∃ i, queue.parameters i = k) ∨ (∃ i, plan.ports i = k) ∨
    k ∈ [queue.word,queue.saved,queue.tmp,plan.precision,plan.wide,plan.rows,plan.replicas,
      plan.count,plan.work,plan.saved,plan.tmp,plan.sp,plan.sg,plan.cy]

structure UnaryReady (plan : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue plan)
    (r : PackedNormalizedJob A s) (N : ℕ) (wl : List (Fin (A+4))) (S : Stacks T A) : Prop where
  width : S.R (plan.scalar .wr) = wl
  scalar : ∀ i : TblR 25, i ≠ .wr → S.R (plan.scalar i) = []
  values : ∀ i, (S.R (queue.parameters i)).length = normalizationValues r i
  queueBlank : ∀ k ∈ [queue.word,queue.saved,queue.tmp], S.R k = []
  precision : (S.R plan.precision).length = r.p
  wide : (S.R plan.wide).length = r.W
  rows : (S.R plan.rows).length = coreLength s r.coreWidth r.k
  replicas : (S.R plan.replicas).length = N
  scratch : ∀ k ∈ [plan.count,plan.work,plan.saved,plan.tmp,plan.sp,plan.sg,plan.cy], S.R k = []
  ports : ∀ i, S.R (plan.ports i) = []

theorem UnaryReady.of_frame {plan : RecoveryNormalizePlan T} {queue : RecoveryParameterQueue plan}
    {r : PackedNormalizedJob A s} {N : ℕ} {wl : List (Fin (A+4))} {S F : Stacks T A}
    (h : plan.UnaryReady queue r N wl S)
    (hframe : ∀ k, plan.support queue k → F.R k = S.R k) : plan.UnaryReady queue r N wl F := by
  have hs (i : TblR 25) := hframe (plan.scalar i) (Or.inl ⟨i,rfl⟩)
  have hv (i : Fin 8) := hframe (queue.parameters i) (Or.inr (Or.inl ⟨i,rfl⟩))
  have hp (i : Fin 4) := hframe (plan.ports i) (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩)))
  have hc (k : Fin T) (hk : k ∈ [queue.word,queue.saved,queue.tmp,plan.precision,plan.wide,plan.rows,plan.replicas,
      plan.count,plan.work,plan.saved,plan.tmp,plan.sp,plan.sg,plan.cy]) :=
    hframe k (Or.inr (Or.inr (Or.inr hk)))
  refine ⟨(hs .wr).trans h.width,fun i hi => (hs i).trans (h.scalar i hi),?_,?_,?_,?_,?_,?_,?_,
    fun i => (hp i).trans (h.ports i)⟩
  · intro i; rw [hv i]; exact h.values i
  · intro k hk; rw [hc k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)]; exact h.queueBlank k hk
  · rw [hc _ (by simp)]; exact h.precision
  · rw [hc _ (by simp)]; exact h.wide
  · rw [hc _ (by simp)]; exact h.rows
  · rw [hc _ (by simp)]; exact h.replicas
  · intro k hk; rw [hc k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)]; exact h.scratch k hk

end RecoveryNormalizePlan

structure RecoveryCropNormalizeLink {T : ℕ} (plan : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue plan) where
  reg : Fin 19 → Fin T
  injective : Function.Injective reg
  inputWidth : plan.inputWidth = reg 9
  source : plan.src = reg 12
  support_off : ∀ k, plan.support queue k → k ≠ reg 9 ∧ k ≠ reg 11 ∧ k ≠ reg 12

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
