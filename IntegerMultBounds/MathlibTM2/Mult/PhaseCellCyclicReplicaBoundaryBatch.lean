module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryBatchLoop

/-! Generate the replica clock once, stage all paired residual rows, and publish
their folded real packets in source order. The masks and fold counters survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 180 Q A U}

def cyclicReplicaBoundaryBatch : Pr P 180 Q A U :=
  .seq (ucopy 179 176 177) (.seq (countedLoop 176 cyclicReplicaBoundaryBatchStep) (moveR 178 6 id))

def cyclicReplicaBoundaryBatchCost (replicas n N w : ℕ) :=
  (4*replicas+4)+(replicas*(cyclicReplicaBoundaryBatchStepCost n N w+3)+2+
    (2*(replicas*(N*w))+2))

/-- All repeated work is linear in the packed input and boundary row volumes. -/
theorem cyclicReplicaBoundaryBatchCost_eq (replicas n N w : ℕ) :
    cyclicReplicaBoundaryBatchCost replicas n N w =
      replicas*(28*n*w+10*n+76*N*w+69*N+60*w+137)+8 := by
  unfold cyclicReplicaBoundaryBatchCost cyclicReplicaBoundaryBatchStepCost
    foldCyclicReplicaBoundaryRhsCost stageReplicaBoundaryRhsCost realPackedBoundaryRhsFoldCost realReplicaRowsCost
  ring

theorem cyclicReplicaBoundaryBatchCost_le (replicas n N w : ℕ) :
    cyclicReplicaBoundaryBatchCost replicas n N w ≤ 137*replicas*(n+N+1)*(w+1)+8 := by
  have h : 28*n*w+10*n+76*N*w+69*N+60*w+137 ≤ 137*(n+N+1)*(w+1) := by
    nlinarith
  rw [cyclicReplicaBoundaryBatchCost_eq]
  have hm := Nat.mul_le_mul_left replicas h
  nlinarith only [hm]

theorem cyclicReplicaBoundaryBatch_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (pairs : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt))) (w : ℕ)
    (leftTail rightTail : List (Fin (A+4))) (v : HS 180 Q A U) (S : Stacks 180 A)
    (ready : CyclicReplicaBoundaryReady (s := s) t band a n w S)
    (hleft : S.R 169 = pairs.flatMap (fun z => cstream A w (packedInterval a (min n (s-a)) z.1))++leftTail)
    (hright : S.R 172 = pairs.flatMap (fun z => cstream A w (packedInterval 0 (n-min n (s-a)) z.2))++rightTail)
    (hreplicas : (S.R 179).length = pairs.length)
    (h176 : S.R 176 = []) (h177 : S.R 177 = []) (h178 : S.R 178 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ cyclicReplicaBoundaryBatchCost pairs.length n (cyclicPrincipalBoundary s t band a n).card w ∧
      Exec body cyclicReplicaBoundaryBatch (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 169 leftTail) 172 rightTail) 6
          (pairs.flatMap (fun z => cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2))))}) := by
  let N := (cyclicPrincipalBoundary s t band a n).card
  let rows := pairs.flatMap (fun z => cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2))
  have hrows : rows.length = pairs.length*(N*w) := by
    simp [rows,List.length_flatMap,N]
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := 179) (b := 176) (t := 177)
    (by decide) (by decide) (by decide) v S h177
  let J : Stacks 180 A := {S with R := Function.update S.R 176 (List.replicate pairs.length tick)}
  have he₁' : Exec body (ucopy 179 176 177) (mk v S) (4*pairs.length+4) (mk v₁ J) := by
    simpa only [J,hreplicas,h176,List.append_nil] using he₁
  have readyJ : CyclicReplicaBoundaryReady (s := s) t band a n w J := by
    apply ready.of_rightFrame
    intro k hk
    have h176' : k ≠ 176 := by intro h; subst k; exact hk (by simp)
    simp only [J,Function.update_of_ne h176']
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := cyclicReplicaBoundaryBatchLoop_exec (body := body)
    hst hA band a n ha hn pairs w leftTail rightTail v₁ J readyJ
    (by simpa [J] using hleft) (by simpa [J] using hright) (by simp [J]) (by simpa [J] using h178)
  let F : Stacks 180 A := {S with R := (Function.update (Function.update (Function.update S.R
    169 leftTail) 172 rightTail) 178 rows.reverse)}
  have he₂' : Exec body (countedLoop 176 cyclicReplicaBoundaryBatchStep) (mk v₁ J) m₂ (mk v₂ F) := by
    refine he₂.cast rfl ?_
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = 176 <;> simp [F,J,hk,h176,Function.update_apply,rows]
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body 178 6 (by decide) id v₂ F
  have he : Exec body cyclicReplicaBoundaryBatch (mk v S)
      ((4*pairs.length+4)+(m₂+(2*rows.length+2)))
      (mk v₃ {S with R := (Function.update (Function.update (Function.update S.R 169 leftTail) 172 rightTail) 6 rows)}) := by
    refine (Exec.seq he₁' (Exec.seq he₂' he₃)).cast (by simp [F]) ?_
    apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk178 : k = 178 <;> by_cases hk6 : k = 6 <;>
      simp [movedR,F,hk178,hk6,h178,ready.blank 6 (by decide) (by decide)]
  refine ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),?_,he⟩
  simpa only [hrows,cyclicReplicaBoundaryBatchCost,N] using
    Nat.add_le_add_left (Nat.add_le_add_right hm₂ (2*rows.length+2)) (4*pairs.length+4)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
