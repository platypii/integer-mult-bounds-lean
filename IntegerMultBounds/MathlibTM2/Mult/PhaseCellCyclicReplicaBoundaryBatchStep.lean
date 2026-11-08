module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFoldCyclicReplicaBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryRows

/-! A reusable row transition: consume two packed prefixes and archive one
folded row in reverse. The controls are shared by all replica transitions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure CyclicReplicaBoundaryInputs {s : ℕ} [NeZero s] (t band a n w : ℕ)
    {A : ℕ} (S : Stacks 180 A) : Prop where
  leftVolume : (S.R 168).length = min n (s-a)*w
  rightVolume : (S.R 171).length = (n-min n (s-a))*w
  leftMask : S.R 170 = couplingSourceIntervalMaskSymbols true A s t band
    a (a+min n (s-a)) a (min n (s-a))
  rightMask : S.R 173 = couplingSourceIntervalMaskSymbols true A s t band
    0 (n-min n (s-a)) 0 (n-min n (s-a))
  width : (S.R 130).length = w
  count : (S.R 116).length = (cyclicPrincipalBoundary s t band a n).card
  blank : ∀ r : Fin 180, 6 ≤ r.val → r.val < 80 → S.R r = []
  fresh : ∀ r ∈ [(134 : Fin 180),135,136,137,143,174,175], S.R r = []

structure CyclicReplicaBoundaryReady {s : ℕ} [NeZero s] (t band a n w : ℕ)
    {A : ℕ} (S : Stacks 180 A) : Prop extends CyclicReplicaBoundaryInputs (s := s) t band a n w S where
  floor : (S.R 0).length = (cyclicPrincipalBoundary s t band a n).card/2
  parity : (S.R 2).length = ((cyclicPrincipalBoundary s t band a n).card+1)/2-
    (cyclicPrincipalBoundary s t band a n).card/2
  bytes : (S.R 3).length = (((cyclicPrincipalBoundary s t band a n).card+1)/2)*w

theorem CyclicReplicaBoundaryReady.of_rightFrame {s : ℕ} [NeZero s] {t band a n w A : ℕ}
    {S R : Stacks 180 A} (h : CyclicReplicaBoundaryReady (s := s) t band a n w S)
    (hf : ∀ k : Fin 180, k ∉ [169,172,176,178] → R.R k = S.R k) :
    CyclicReplicaBoundaryReady (s := s) t band a n w R := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · rw [hf 168 (by decide)]; exact h.leftVolume
  · rw [hf 171 (by decide)]; exact h.rightVolume
  · rw [hf 170 (by decide)]; exact h.leftMask
  · rw [hf 173 (by decide)]; exact h.rightMask
  · rw [hf 130 (by decide)]; exact h.width
  · rw [hf 116 (by decide)]; exact h.count
  · intro r hr6 hr80
    have hoff : r ∉ [(169 : Fin 180),172,176,178] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      refine ⟨?_,?_,?_,?_⟩ <;> intro he <;>
        have hv := congrArg Fin.val he <;> simp at hv <;> omega
    rw [hf r hoff]
    exact h.blank r hr6 hr80
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [hf _ (by decide)]; exact h.fresh _ (by simp)
  · rw [hf 0 (by decide)]; exact h.floor
  · rw [hf 2 (by decide)]; exact h.parity
  · rw [hf 3 (by decide)]; exact h.bytes

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 180 Q A U}

def cyclicReplicaBoundaryBatchStep : Pr P 180 Q A U :=
  .seq (embProg (Fin.castLE (by decide : 176 ≤ 180)) Empty.elim (foldCyclicReplicaBoundaryRhs (P := Empty)))
    (moveR 6 178 id)

def cyclicReplicaBoundaryBatchStepCost (n N w : ℕ) :=
  foldCyclicReplicaBoundaryRhsCost n N w+(2*(N*w)+2)

theorem cyclicReplicaBoundaryBatchStep_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (C D : ZMod s → GaussianInt) (w : ℕ)
    (leftTail rightTail : List (Fin (A+4))) (v : HS 180 Q A U) (S : Stacks 180 A)
    (ready : CyclicReplicaBoundaryReady (s := s) t band a n w S)
    (hleft : S.R 169 = cstream A w (packedInterval a (min n (s-a)) C)++leftTail)
    (hright : S.R 172 = cstream A w (packedInterval 0 (n-min n (s-a)) D)++rightTail) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ cyclicReplicaBoundaryBatchStepCost n (cyclicPrincipalBoundary s t band a n).card w ∧
      Exec body cyclicReplicaBoundaryBatchStep (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 169 leftTail) 172 rightTail) 178
          ((cstream A w (cyclicReplicaBoundaryRow t band a n C D)).reverse++S.R 178))}) := by
  let e : Fin 176 → Fin 180 := Fin.castLE (by decide)
  have hinj : Function.Injective e := Fin.castLE_injective (by decide)
  obtain ⟨vi,m₁,hui,hm₁,hei⟩ := foldCyclicReplicaBoundaryRhs_exec
    (body := fun z : Empty => nomatch z) hst hA band a n ha hn C D w leftTail rightTail
    (embDn e v) (embStk e S)
    ready.leftVolume ready.rightVolume hleft hright ready.leftMask ready.rightMask
    ready.width ready.count ready.floor ready.parity ready.bytes
    (by intro r hr6 hr80; exact ready.blank (e r) hr6 hr80)
    (by intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ready.fresh _ (by simp [e]))
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun z => nomatch z) hei v rfl S rfl
  let row := cstream A w (cyclicReplicaBoundaryRow t band a n C D)
  let J : Stacks 180 A := {S with R := (Function.update (Function.update (Function.update S.R 169 leftTail) 172 rightTail) 6 row)}
  have he₁' : Exec body (embProg e Empty.elim (foldCyclicReplicaBoundaryRhs (P := Empty)))
      (mk v S) m₁ (mk v₁ J) := by
    refine he₁.cast rfl ?_
    apply congrArg (mk v₁)
    rw [embOvr_updateR_updateR_updateR hinj]
    rfl
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body 6 178 (by decide) id v₁ J
  have hrow : row.length = (cyclicPrincipalBoundary s t band a n).card*w := by
    simp [row]
  refine ⟨v₂,m₁+(2*row.length+2),hu₂.trans (hu₁.trans hui),
    by simpa only [hrow,cyclicReplicaBoundaryBatchStepCost] using Nat.add_le_add_right hm₁ (2*row.length+2),
    (Exec.seq he₁' he₂).cast (by simp [J]) ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk6 : k = 6 <;> by_cases hk178 : k = 178 <;>
    simp [movedR,J,row,hk6,hk178,ready.blank 6 (by decide) (by decide)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
