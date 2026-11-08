module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryFoldCounters

/-! Generate and retire the joint fold counters once for the whole replica bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 180 Q A U}

def cyclicReplicaBoundaryCounterState (N w : ℕ) (S : Stacks 180 A) : Stacks 180 A :=
  {S with R := (Function.update (Function.update (Function.update S.R
    0 (List.replicate (N/2) tick)) 2 (List.replicate ((N+1)/2-N/2) tick))
    3 (List.replicate (((N+1)/2)*w) tick))}

theorem CyclicReplicaBoundaryInputs.withCounters {s : ℕ} [NeZero s] {t band a n w : ℕ}
    {S : Stacks 180 A} (h : CyclicReplicaBoundaryInputs (s := s) t band a n w S) :
    CyclicReplicaBoundaryReady (s := s) t band a n w
      (cyclicReplicaBoundaryCounterState (cyclicPrincipalBoundary s t band a n).card w S) := by
  let N := (cyclicPrincipalBoundary s t band a n).card
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · simpa [cyclicReplicaBoundaryCounterState] using h.leftVolume
  · simpa [cyclicReplicaBoundaryCounterState] using h.rightVolume
  · simpa [cyclicReplicaBoundaryCounterState] using h.leftMask
  · simpa [cyclicReplicaBoundaryCounterState] using h.rightMask
  · simpa [cyclicReplicaBoundaryCounterState] using h.width
  · simpa [cyclicReplicaBoundaryCounterState] using h.count
  · intro r hr6 hr80
    have h0 : r ≠ 0 := by intro he; have := congrArg Fin.val he; simp at this; omega
    have h2 : r ≠ 2 := by intro he; have := congrArg Fin.val he; simp at this; omega
    have h3 : r ≠ 3 := by intro he; have := congrArg Fin.val he; simp at this; omega
    simpa [cyclicReplicaBoundaryCounterState,h0,h2,h3] using h.blank r hr6 hr80
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simpa [cyclicReplicaBoundaryCounterState] using h.fresh _ (by simp)
  · simp [cyclicReplicaBoundaryCounterState]
  · simp [cyclicReplicaBoundaryCounterState]
  · simp [cyclicReplicaBoundaryCounterState]

def initializedCyclicReplicaBoundaryBatch : Pr P 180 Q A U :=
  .seq (embProg (Fin.castLE (by decide : 168 ≤ 180)) Empty.elim (packedBoundaryFoldCounters (P := Empty)))
    (.seq cyclicReplicaBoundaryBatch (clearWords [0,2,3]))

def initializedCyclicReplicaBoundaryBatchCost (replicas n N w : ℕ) :=
  boundaryFoldCountersCost N w+(cyclicReplicaBoundaryBatchCost replicas n N w+(2*(N+N*w)+7))

theorem initializedCyclicReplicaBoundaryBatch_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (pairs : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt))) (w : ℕ)
    (leftTail rightTail : List (Fin (A+4))) (v : HS 180 Q A U) (S : Stacks 180 A)
    (inputs : CyclicReplicaBoundaryInputs (s := s) t band a n w S)
    (hblank : ∀ r : Fin 180, r.val < 6 → S.R r = [])
    (hleft : S.R 169 = pairs.flatMap (fun z => cstream A w (packedInterval a (min n (s-a)) z.1))++leftTail)
    (hright : S.R 172 = pairs.flatMap (fun z => cstream A w (packedInterval 0 (n-min n (s-a)) z.2))++rightTail)
    (hreplicas : (S.R 179).length = pairs.length)
    (h176 : S.R 176 = []) (h177 : S.R 177 = []) (h178 : S.R 178 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ initializedCyclicReplicaBoundaryBatchCost pairs.length n (cyclicPrincipalBoundary s t band a n).card w ∧
      Exec body initializedCyclicReplicaBoundaryBatch (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 169 leftTail) 172 rightTail) 6
          (pairs.flatMap (fun z => cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2))))}) := by
  let N := (cyclicPrincipalBoundary s t band a n).card
  let rows := pairs.flatMap (fun z => cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2))
  let e : Fin 168 → Fin 180 := Fin.castLE (by decide)
  have hinj : Function.Injective e := Fin.castLE_injective (by decide)
  obtain ⟨vi,m₁,hui,hm₁,hei⟩ := packedBoundaryFoldCounters_exec
    (body := fun z : Empty => nomatch z) N w (embDn e v) (embStk e S)
    inputs.count inputs.width (by intro r hr; exact hblank (e r) hr)
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun z => nomatch z) hei v rfl S rfl
  let J := cyclicReplicaBoundaryCounterState N w S
  have he₁' : Exec body (embProg e Empty.elim (packedBoundaryFoldCounters (P := Empty)))
      (mk v S) m₁ (mk v₁ J) := by
    refine he₁.cast rfl ?_
    apply congrArg (mk v₁)
    rw [embOvr_updateR_updateR_updateR hinj]
    rfl
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := cyclicReplicaBoundaryBatch_exec (body := body)
    hst hA band a n ha hn pairs w leftTail rightTail v₁ J inputs.withCounters
    (by simpa [J,cyclicReplicaBoundaryCounterState] using hleft)
    (by simpa [J,cyclicReplicaBoundaryCounterState] using hright)
    (by simpa [J,cyclicReplicaBoundaryCounterState] using hreplicas)
    (by simpa [J,cyclicReplicaBoundaryCounterState] using h176)
    (by simpa [J,cyclicReplicaBoundaryCounterState] using h177)
    (by simpa [J,cyclicReplicaBoundaryCounterState] using h178)
  let K : Stacks 180 A := {J with R := (Function.update (Function.update (Function.update J.R
    169 leftTail) 172 rightTail) 6 rows)}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [0,2,3] (by decide) v₂ K
  have hclear : 2*([(0 : Fin 180),2,3].map (fun r => (K.R r).length)).sum+2*([(0 : Fin 180),2,3].length)+1 ≤
      2*(N+N*w)+7 := by
    simp only [K,J,cyclicReplicaBoundaryCounterState,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil,Function.update_of_ne (by decide : (0 : Fin 180) ≠ 6),
      Function.update_of_ne (by decide : (2 : Fin 180) ≠ 6),
      Function.update_of_ne (by decide : (3 : Fin 180) ≠ 6)]
    simp only [Function.update_apply]
    norm_num
    have hhalf : N/2+((N+1)/2-N/2) = (N+1)/2 := by omega
    have hle : (N+1)/2 ≤ N := by omega
    have hm := Nat.mul_le_mul_right w hle
    omega
  have hfinal : {K with R := fun k => if k ∈ [(0 : Fin 180),2,3] then [] else K.R k} =
      {S with R := (Function.update (Function.update (Function.update S.R 169 leftTail) 172 rightTail) 6 rows)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h0 : k = 0 <;> by_cases h2 : k = 2 <;> by_cases h3 : k = 3
    all_goals simp [K,J,cyclicReplicaBoundaryCounterState,h0,h2,h3,Function.update_apply,
      hblank 0 (by decide),hblank 2 (by decide),hblank 3 (by decide)]
  exact ⟨v₃,_,hu₃.trans (hu₂.trans (hu₁.trans hui)),
    Nat.add_le_add hm₁ (Nat.add_le_add hm₂ hclear),
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl (congrArg (mk v₃) hfinal)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
