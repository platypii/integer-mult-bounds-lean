module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedBatchWeightSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCacheBatchWeightPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWeightCache

/-! Generate and retain the exact grouped weight page used by the batch runtime. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

def generatedBatchWeightCache : Pr P₀ 121 Q A U :=
  .seq (embProg weightCacheCoreReg Empty.elim (sharedBatchWeightSetup (P₀ := Empty))) cacheBatchWeightPage

def generatedBatchWeightCacheCost (P s t u q L w B : ℕ) : ℕ :=
  sharedBatchWeightSetupCost P s t u q L w B+cacheBatchWeightPageCost B L w

theorem generatedBatchWeightCache_exec (P s t u q L w B : ℕ) (lo : ℕ → ℕ)
    (v : HS 121 Q A U) (S : Stacks 121 A) (tail : List (Fin (A+4)))
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hrows : (S.R 103).length = L)
    (hw : (S.R 94).length = w) (hB : (S.R 116).length = B)
    (hpacket : S.R 109 = (List.range B).flatMap
      (fun i => binSyms (weightWorkspaceWidth P q w t u) (lo i))++tail)
    (hblank : ∀ r, (embStk weightCacheCoreReg S).R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ ([(64 : Fin 121),65,96,104,105,106,107,108,111,115,118,119,120] : List (Fin 121)), S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hlo : ∀ i < B, lo i < s) (hL : L ≤ s) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedBatchWeightCacheCost P s t u q L w B ∧
      Exec body generatedBatchWeightCache (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 109 tail)
          117 (batchWeightPage A w q P s t u B L lo++S.R 117))
          118 (List.replicate (2*(B*(L*w))) tick))}) := by
  obtain ⟨vi,m₁,hu₁,hm₁,he₁⟩ := sharedBatchWeightSetup_exec
    (body := fun p : Empty => nomatch p) P s t u q L w B lo
    (embDn weightCacheCoreReg v) (embStk weightCacheCoreReg S) tail
    hP' hs' ht' hu' hq hL' hrows hw hB hpacket hblank (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hfresh _ (by simp [weightCacheCoreReg])) hP hs hst hu hlo hL
  obtain ⟨v₁,hv₁,hu₁',he₁'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    weightCacheCoreReg_injective (fun p => nomatch p) he₁ v rfl S rfl
  let page := batchWeightPage A w q P s t u B L lo
  let T : Stacks 121 A := {S with R := (Function.update (Function.update S.R 109 tail)
    110 (page++S.R 110))}
  have he₁'' : Exec body (embProg weightCacheCoreReg Empty.elim (sharedBatchWeightSetup (P₀ := Empty)))
      (mk v S) m₁ (mk v₁ T) := by
    refine he₁'.cast rfl ?_
    apply congrArg (mk v₁)
    change embOvr weightCacheCoreReg
      ({({embStk weightCacheCoreReg S with R := Function.update (embStk weightCacheCoreReg S).R 109 tail})
        with R := (Function.update (Function.update (embStk weightCacheCoreReg S).R 109 tail) 110
          (page++S.R 110))} : Stacks 117 A).get S = T
    rw [embOvr_updR weightCacheCoreReg_injective,embOvr_updR weightCacheCoreReg_injective,embOvr_stk]
    rfl
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := cacheBatchWeightPage_exec (body := body) v₁ T page (S.R 110) B L w
    (by simp [page]) (by simp [T]) (by simpa [T] using hB)
    (by simpa [T] using hrows) (by simpa [T] using hw) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [T] using hfresh _ (by simp))
  refine ⟨v₂,m₁+m₂,hu₂.trans (hu₁'.trans hu₁),by dsimp [generatedBatchWeightCacheCost]; omega,
    (Exec.seq he₁'' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h109 : i = 109 <;> by_cases h110 : i = 110 <;>
    simp [T,page,Function.update_apply,h109,h110]

/-- Exact retained stock, counting the page, replay clock, scratch and borrowed suffix together. -/
theorem batchWeightCache_volume {A : ℕ} (S : Stacks 121 A)
    (w q P s t u B L : ℕ) (lo : ℕ → ℕ) (tail : List (Fin (A+4)))
    (hpage : S.R 117 = batchWeightPage A w q P s t u B L lo++tail)
    (hcount : (S.R 118).length = 2*(B*(L*w)))
    (h119 : S.R 119 = []) (h120 : S.R 120 = []) :
    (([(117 : Fin 121),118,119,120] : List (Fin 121)).map (fun i => (S.R i).length)).sum =
      4*(B*(L*w))+tail.length := by
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hpage,List.length_append,
    batchWeightPage_length,hcount,h119,h120,List.length_nil]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
