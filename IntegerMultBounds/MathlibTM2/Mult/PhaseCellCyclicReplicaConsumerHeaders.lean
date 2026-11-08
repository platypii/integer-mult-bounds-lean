module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassPost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderCopies

/-! Borrow the four masters already retained by the cached passes. Packed
volumes are copied, rather than recomputed from ambient endpoint rulers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 834 Q A U}

def cyclicReplicaConsumerHeaderCopies : List (Fin 834 × Fin 834) :=
  [(left.plan.gather 121,factorReg 229),
   (left.plan.solver (weightCacheCoreReg 94),factorReg 130),
   (left.plan.gather 123,factorReg 168),
   (right.plan.gather 123,factorReg 171)]

def cyclicReplicaConsumerHeaders : Pr P 834 Q A U :=
  copyUnaryHeaders (factorReg 175) cyclicReplicaConsumerHeaderCopies

def cyclicReplicaConsumerHeaderState (S : Stacks 834 A) : Stacks 834 A :=
  {S with R := unaryCopiesR (fun k => (S.R k).length) S.R cyclicReplicaConsumerHeaderCopies}

theorem cyclicReplicaConsumerHeaders_exec (v : HS 834 Q A U) (S : Stacks 834 A)
    (htmp : S.R (factorReg 175) = []) :
    ∃ vf, vf.user = v.user ∧
      Exec body cyclicReplicaConsumerHeaders (mk v S)
        (copyUnaryHeadersCost (fun k => (S.R k).length) cyclicReplicaConsumerHeaderCopies)
        (mk vf (cyclicReplicaConsumerHeaderState S)) := by
  apply copyUnaryHeaders_exec (body := body) (factorReg 175) cyclicReplicaConsumerHeaderCopies
  · intro r hr
    simp only [cyclicReplicaConsumerHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide
  · intro r hr p hp
    simp only [cyclicReplicaConsumerHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr hp
    rcases hr with rfl | rfl | rfl | rfl
    all_goals rcases hp with rfl | rfl | rfl | rfl <;> decide
  · intro _ _; rfl
  · exact htmp

theorem cyclicReplicaConsumerHeaders_values {s : ℕ} [NeZero s] (H K : ReplicaHaloProblem s)
    (leftBuffers rightBuffers : ReplicaLoopBuffers A) (S₀ S₁ S : Stacks 834 A)
    (Cs Ds : List (ZMod s → GaussianInt))
    (hl : CachedReplicaPassPost H left leftBuffers S₀ S Cs)
    (hr : CachedReplicaPassPost K right rightBuffers S₁ S Ds)
    (hblank : ∀ k ∈ [(130 : Fin 234),168,171,229], S.R (factorReg k) = []) :
    let F := cyclicReplicaConsumerHeaderState S
    F.R (factorReg 130) = List.replicate H.wordWidth tick ∧
    F.R (factorReg 168) = List.replicate (H.span*H.wordWidth) tick ∧
    F.R (factorReg 171) = List.replicate (K.span*K.wordWidth) tick ∧
    F.R (factorReg 229) = List.replicate H.Fs.length tick ∧
    copyUnaryHeadersCost (fun k => (S.R k).length) cyclicReplicaConsumerHeaderCopies =
      4*(H.Fs.length+H.wordWidth+H.span*H.wordWidth+K.span*K.wordWidth)+17 := by
  have hwidth : (S.R (left.plan.solver (weightCacheCoreReg 94))).length = H.wordWidth := hl.ready.width
  have hc := hl.recoveryRhs.count
  have hvL := hl.recoveryRhs.volume
  have hvR := hr.recoveryRhs.volume
  have hat (r : Fin 834 × Fin 834) (hmem : r ∈ cyclicReplicaConsumerHeaderCopies) :
      (cyclicReplicaConsumerHeaderState S).R r.2 = List.replicate (S.R r.1).length tick++S.R r.2 :=
    unaryCopiesR_at (fun k => (S.R k).length) S.R cyclicReplicaConsumerHeaderCopies (by decide) r hmem
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [hwidth,hblank 130 (by simp),List.append_nil] using
      hat (left.plan.solver (weightCacheCoreReg 94),factorReg 130) (by simp [cyclicReplicaConsumerHeaderCopies])
  · simpa only [hvL,hblank 168 (by simp),List.append_nil] using
      hat (left.plan.gather 123,factorReg 168) (by simp [cyclicReplicaConsumerHeaderCopies])
  · simpa only [hvR,hblank 171 (by simp),List.append_nil] using
      hat (right.plan.gather 123,factorReg 171) (by simp [cyclicReplicaConsumerHeaderCopies])
  · simpa only [hc,hblank 229 (by simp),List.append_nil] using
      hat (left.plan.gather 121,factorReg 229) (by simp [cyclicReplicaConsumerHeaderCopies])
  · simp only [copyUnaryHeadersCost,cyclicReplicaConsumerHeaderCopies,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,hc,hwidth,hvL,hvR]
    omega

theorem cyclicReplicaConsumerHeaders_frame (S : Stacks 834 A) (k : Fin 834)
    (h : left.Owns k ∨ right.Owns k) :
    (cyclicReplicaConsumerHeaderState S).L k = S.L k ∧
    (cyclicReplicaConsumerHeaderState S).R k = S.R k := by
  refine ⟨rfl,?_⟩
  apply unaryCopiesR_off
  intro r hr
  simp only [cyclicReplicaConsumerHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  all_goals intro he; rcases h with h | h
  all_goals first
    | exact (factor_disjoint _).1 (he.symm ▸ h)
    | exact (factor_disjoint _).2 (he.symm ▸ h)

theorem cyclicReplicaConsumerHeaders_read (S : Stacks 834 A) (k : Fin 834)
    (h130 : k ≠ factorReg 130) (h168 : k ≠ factorReg 168)
    (h171 : k ≠ factorReg 171) (h229 : k ≠ factorReg 229) :
    (cyclicReplicaConsumerHeaderState S).R k = S.R k := by
  apply unaryCopiesR_off
  intro r hr
  simp only [cyclicReplicaConsumerHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h229.symm
  · exact h130.symm
  · exact h168.symm
  · exact h171.symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
