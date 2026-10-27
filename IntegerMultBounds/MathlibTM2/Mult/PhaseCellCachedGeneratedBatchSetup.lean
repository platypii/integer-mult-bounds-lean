module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchWeightedSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWeightCache
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightPage

/-! Route raw RHS blocks and install runtime controls after cached grouped weighting. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

noncomputable def cachedGeneratedBatchSetup (hQ : SS.states ≤ Q) : Pr P₀ 121 Q A U :=
  .seq (cachedBatchWeightedSetup hQ)
    (embProg weightCacheCoreReg Empty.elim (prepareBatchRuntime (P₀ := Empty)))

def cachedGeneratedBatchSetupCost (P N q s t u band l L B : ℕ) : ℕ :=
  cachedBatchWeightedSetupCost P N q s t u band L B+prepareBatchRuntimeCost P N q l B L (2*q+8)

theorem cachedGeneratedBatchSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q N l B : ℕ} (lo : ℕ → ℕ)
    (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1)) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hL : 0 < L) (v : HS 121 Q A U) (S : Stacks 121 A)
    (rhs borrowed tail cacheTail : List (Fin (A+4)))
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hN : (S.R 101).length = N)
    (hB : S.R 116 = List.replicate B tick) (hpacket : S.R 109 = tail)
    (hl : tail.length = l) (hsrc : S.R 110 = rhs++borrowed) (hrhs : rhs.length = B*L*(2*q+8))
    (hclean : CClean mul (embStk weightCacheCoreReg S))
    (hblank : ∀ r, (embStk weightCacheCoreReg S).R (cr r) = [])
    (hfresh : ∀ k ∈ ([(64 : Fin 121),65,94,96,104,105,106,107,108,111,113,115,119,120] : List (Fin 121)), S.R k = [])
    (hcache : S.R 117 = batchWeightPage A (2*q+8) q P s t u B L lo++cacheTail)
    (hcacheCount : (S.R 118).length = 2*(B*(L*(2*q+8)))) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ cachedGeneratedBatchSetupCost P N q s t u band l L B ∧
      Exec body (cachedGeneratedBatchSetup hQ) (mk v S) m (mk v' S') ∧
      embStk weightCacheCoreReg S' =
        generatedBatchBank (embStk weightCacheCoreReg S) P s t u band L q N l B lo rhs borrowed tail ∧
      ∀ i, 117 ≤ i.val → S'.L i = S.L i ∧ S'.R i = S.R i := by
  obtain ⟨v₁,M,m₁,hu₁,hm₁,he₁,hproj,hoff₁⟩ := cachedBatchWeightedSetup_exec (body := body)
    hQ hA lo hP hqMax hs hst hu hL v S tail cacheTail hprecision hsR htR huR hband hrows hcount
    hq hN hB hpacket hclean hblank hfresh hcache hcacheCount
  obtain ⟨vi,m₂,hu₂,hm₂,he₂⟩ := weightedBatchRuntime_exec
    (body := fun p : Empty => nomatch p) P N q l s t u band L B lo
    (embDn weightCacheCoreReg v₁) (embStk weightCacheCoreReg S) rhs borrowed tail
    hprecision hN hq hcount hl hsrc hrhs (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals exact hfresh _ (by simp [weightCacheCoreReg]))
  rw [← hproj] at he₂
  obtain ⟨v₂,T,he₂',hv₂,hu₂',hproj₂,hoff₂⟩ := exec_emb (body' := body) (ι := Empty.elim)
    weightCacheCoreReg_injective (fun p => nomatch p) he₂ v₁ rfl M rfl
  refine ⟨v₂,T,m₁+m₂,hu₂'.trans (hu₂.trans hu₁),?_,Exec.seq he₁ he₂',hproj₂,?_⟩
  · dsimp only [cachedGeneratedBatchSetupCost]
    omega
  · intro i hi
    have h := hoff₂ i (by
      intro j he
      have hv := congrArg (fun k : Fin 121 => k.val) he
      dsimp [weightCacheCoreReg] at hv
      omega)
    exact ⟨h.1.trans (hoff₁ i hi).1,h.2.trans (hoff₁ i hi).2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
