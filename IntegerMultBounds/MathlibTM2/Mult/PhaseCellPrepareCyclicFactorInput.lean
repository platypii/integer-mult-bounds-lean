module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicBoundaryPageReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualBatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaPlacement

/-! The existing computed cyclic page producer establishes the factor caller's
complete input contract. Arithmetic headers are retained; numerical pages are
produced rather than assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 234 Q A U}

noncomputable def cyclicFactorInputPage {s : ℕ} [NeZero s] (t band a n : ℕ)
    (S : Stacks 154 A) : Stacks 154 A :=
  let R := Function.update (Function.update (Function.update (Function.update (Function.update S.R
    141 []) 142 []) 144 (List.replicate a tick)) 145 (List.replicate (a+min n (s-a)) tick))
      146 (List.replicate (n-min n (s-a)) tick)
  {S with R := (Function.update (Function.update (Function.update R
    115 (List.replicate (publicationGeometryWidth t band) tick))
    116 (List.replicate (cyclicPrincipalBoundary s t band a n).card tick))
    109 (cstream A (publicationGeometryWidth t band)
      ((bFoldOrder s (cyclicPrincipalBoundary s t band a n)).map
        (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))))}

def prepareCyclicFactorInput : Pr P 234 Q A U :=
  embProg (Fin.castLE (by decide : 154 ≤ 234)) Empty.elim (prepareCyclicBoundaryPage (P := Empty))

/-- Ordinary scalar seeds and fresh factor workspace, before any cyclic
boundary page or split endpoints have been computed. -/
structure CyclicFactorSeedInput {A : ℕ} (p l s t u target a n : ℕ) [NeZero s]
    (tail : List (Fin (A+4))) (S : Stacks 234 A) : Prop where
  sourceLength : (S.R 121).length = s
  targetLength : (S.R 122).length = t
  band : (S.R 124).length = PhaseCellBand.width p u
  origin : (S.R 141).length = a
  span : (S.R 142).length = n
  fresh : ∀ k ∈ [(106 : Fin 234),108,109,115,116,127,135,138,139,143,144,145,146,147,151,152,153], S.R k = []
  low : ∀ k : Fin 234, k.val < 77 → S.R k = []
  left : ∀ k, S.L k = []
  new : ∀ k : Fin 234, 154 ≤ k.val → S.R k = []
  arithmetic : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg
        (embStk preparedBoundaryCoreReg (embStk preparedBoundaryBatchCoreReg S))))))

theorem prepareCyclicFactorInput_exec {p l s t u target a n : ℕ} [NeZero s]
    (hst : s < t) (ha : a < s) (hn : n ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (v : HS 234 Q A U) (S : Stacks 234 A) (tail : List (Fin (A+4)))
    (seed : CyclicFactorSeedInput p l s t u target a n tail S) :
    ∃ v' G steps, v'.user = v.user ∧
      steps ≤ prepareCyclicBoundaryPageCost (embStk (Fin.castLE (by decide : 154 ≤ 234)) S).R
        s t (PhaseCellBand.width p u) a n ∧
      Exec body prepareCyclicFactorInput (mk v S) steps (mk v' G) ∧
      CyclicResidualBatchInput p l s t u target a n tail [] G ∧
      G.inp = S.inp ∧ G.out = S.out ∧ G.L = S.L ∧
      (∀ k : Fin 234, 154 ≤ k.val → G.R k = S.R k) := by
  rcases seed with ⟨hs,ht,hb,haSrc,hnSrc,hfresh,hlow,hleft,hnew,hready⟩
  let e := Fin.castLE (by decide : 154 ≤ 234)
  let I := embStk e S
  let F := cyclicFactorInputPage (s := s) t (PhaseCellBand.width p u) a n I
  have hready' : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2)
      l s t u (PhaseCellBand.width p u) 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg I))) := hready
  obtain ⟨vf,m,hu,hm,hex,hread⟩ := prepareCyclicBoundaryPage_ready_exec
    (body := fun f : Empty => nomatch f) hst ha hn hband (embDn e v) I hs ht hb haSrc hnSrc
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals apply hfresh; simp [e])
    (fun k hk => hlow (e k) hk) (fun k => hleft (e k)) tail hready'
  change Exec (fun f : Empty => nomatch f) prepareCyclicBoundaryPage (mk (embDn e v) I) m (mk vf F) at hex
  change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _ (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg F))) at hread
  obtain ⟨v',G,hex',hv,hu',hview,hoff⟩ := exec_emb (ι := Empty.elim) (body' := body)
    (Fin.castLE_injective _) (fun f => nomatch f) hex v rfl S rfl
  have hR (k : Fin 154) : G.R (e k) = F.R k := congrArg (fun B : Stacks 154 A => B.R k) hview
  have hI : G.inp = S.inp := congrArg (fun B : Stacks 154 A => B.inp) hview
  have hO : G.out = S.out := congrArg (fun B : Stacks 154 A => B.out) hview
  have hhigh (k : Fin 234) (hk : 154 ≤ k.val) : G.L k = S.L k ∧ G.R k = S.R k := by
    apply hoff k
    intro i he
    have hv := congrArg Fin.val he
    change i.val = k.val at hv
    have := i.isLt
    omega
  have hL : G.L = S.L := by
    funext k
    by_cases hk : k.val < 154
    · have hh := congrArg (fun B : Stacks 154 A => B.L ⟨k.val,hk⟩) hview
      exact hh
    · exact (hhigh k (by omega)).1
  refine ⟨v',G,m,hu'.trans hu,hm,hex',?_,hI,hO,hL,fun k hk => (hhigh k hk).2⟩
  constructor
  · change (G.R (e 116)).length = _
    rw [hR]; simp [F,cyclicFactorInputPage]
  · change (G.R (e 115)).length = _
    rw [hR]; simp [F,cyclicFactorInputPage]
  · change G.R (e 109) = _
    rw [hR]; simp [F,cyclicFactorInputPage]
  · change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk e G))))
    rw [hview]; exact hread
  · change (G.R (e 144)).length = _
    rw [hR]; simp [F,cyclicFactorInputPage]
  · change (G.R (e 145)).length = _
    rw [hR]; simp [F,cyclicFactorInputPage]
  · change (G.R (e 146)).length = _
    rw [hR]; simp [F,cyclicFactorInputPage]
  · intro k hk
    have hklt : k.val < 154 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    let j : Fin 154 := ⟨k.val,hklt⟩
    change G.R (e j) = []
    rw [hR]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [F,cyclicFactorInputPage,I,embStk,e,j,hfresh,hlow]
  · intro i
    rw [hL]; exact hleft _
  · intro i hi
    apply (hhigh _ hi).2.trans
    exact hnew _ hi
  · intro k hk
    have hi : 154 ≤ k.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hhigh k hi).2.trans (hnew k hi)

/-- Factor-page preparation runs inside its disjoint physical bank and
preserves both cached numerical inputs, ready for the existing cyclic core. -/
theorem prepareCyclicFactorInput_placed_exec {T p l s t u target a n : ℕ} [NeZero s]
    (bank : Fin 834 → Fin T) (hbank : Function.Injective bank)
    (hst : s < t) (ha : a < s) (hn : n ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (H K : ReplicaHaloProblem s) (buffersL buffersR : ReplicaLoopBuffers A)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (seed : CyclicFactorSeedInput p l s t u target a n tail (embStk (bank ∘ CyclicReplicaPlacement.factorReg) S))
    (hleft : CachedReplicaPassInput H (CyclicReplicaPlacement.left.reindex bank hbank) buffersL S)
    (hright : CachedReplicaPassInput K (CyclicReplicaPlacement.right.reindex bank hbank) buffersR S)
    {outerBody : P → Pr P T Q A U} :
    ∃ v' G steps, v'.user = v.user ∧
      steps ≤ prepareCyclicBoundaryPageCost
        (embStk (Fin.castLE (by decide : 154 ≤ 234)) (embStk (bank ∘ CyclicReplicaPlacement.factorReg) S)).R
        s t (PhaseCellBand.width p u) a n ∧
      Exec outerBody (embProg (bank ∘ CyclicReplicaPlacement.factorReg) id prepareCyclicFactorInput)
        (mk v S) steps (mk v' G) ∧
      CyclicResidualBatchInput p l s t u target a n tail [] (embStk (bank ∘ CyclicReplicaPlacement.factorReg) G) ∧
      CachedReplicaPassInput H (CyclicReplicaPlacement.left.reindex bank hbank) buffersL G ∧
      CachedReplicaPassInput K (CyclicReplicaPlacement.right.reindex bank hbank) buffersR G ∧
      (∀ k, (∀ i, bank (CyclicReplicaPlacement.factorReg i) ≠ k) → G.L k = S.L k ∧ G.R k = S.R k) := by
  let e := bank ∘ CyclicReplicaPlacement.factorReg
  obtain ⟨vf,F,m,hu,hm,hex,hinput,hI,hO,hL,hhigh⟩ := prepareCyclicFactorInput_exec
    (body := fun f : Empty => nomatch f) hst ha hn hband (embDn e v) (embStk e S) tail seed
  obtain ⟨v',G,hex',hv,hu',hview,hoff⟩ := exec_emb (ι := Empty.elim) (body' := outerBody)
    (hbank.comp CyclicReplicaPlacement.factorReg_injective) (fun f => nomatch f) hex v rfl S rfl
  have hin : G.inp = S.inp := (congrArg (fun B : Stacks 234 A => B.inp) hview).trans hI
  have hout : G.out = S.out := (congrArg (fun B : Stacks 234 A => B.out) hview).trans hO
  refine ⟨v',G,m,hu'.trans hu,hm,?_,?_,?_,?_,hoff⟩
  · exact hex'
  · rw [hview]; exact hinput
  · apply hleft.of_frame hin hout
    intro k hk
    apply hoff k
    have hplacement : CyclicReplicaPlacement.left.reindex bank hbank =
        CachedReplicaPassPlacement.standard.reindex (bank ∘ CyclicReplicaPlacement.leftReg)
          (hbank.comp CyclicReplicaPlacement.leftReg_injective) := rfl
    rw [hplacement] at hk
    obtain ⟨j,hj⟩ := CachedReplicaPassPlacement.reindex_source _ _ _ hk
    intro i heq
    have hv := congrArg Fin.val (hbank (heq.trans hj.symm))
    change 600+i.val = j.val at hv
    have := j.isLt
    omega
  · apply hright.of_frame hin hout
    intro k hk
    apply hoff k
    have hplacement : CyclicReplicaPlacement.right.reindex bank hbank =
        CachedReplicaPassPlacement.standard.reindex (bank ∘ CyclicReplicaPlacement.rightReg)
          (hbank.comp CyclicReplicaPlacement.rightReg_injective) := rfl
    rw [hplacement] at hk
    obtain ⟨j,hj⟩ := CachedReplicaPassPlacement.reindex_source _ _ _ hk
    intro i heq
    have hv := congrArg Fin.val (hbank (heq.trans hj.symm))
    change 600+i.val = 300+j.val at hv
    have := j.isLt
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
