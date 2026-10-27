module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBatchWeightedSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightedSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWeightCache
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightPage

/-! Replay retained grouped weights into the actual inverse-setup ABI. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

noncomputable def cachedBatchWeightedSetup (hQ : SS.states ≤ Q) : Pr P₀ 121 Q A U :=
  .seq (copyPrefix 118 117 110 119 120)
    (embProg weightCacheCoreReg Empty.elim (preparedBatchWeightedSetup (P₀ := Empty) hQ))

def cachedBatchWeightedSetupCost (P N q s t u band L B : ℕ) : ℕ :=
  20*(B*(L*(2*q+8)))+10+preparedBatchWeightedSetupCost P N q s t u band L B

theorem preparedBatchWeightedBank_weights {A : ℕ} (S : Stacks 117 A)
    (P s t u band L q N B : ℕ) (lo : ℕ → ℕ) (tail : List (Fin (A+4))) :
    preparedBatchWeightedBank
      {S with R := Function.update S.R 110 (batchWeightPage A (2*q+8) q P s t u B L lo++S.R 110)}
      P s t u band L q N B tail = batchWeightedBank S P s t u band L q N B lo tail := by
  unfold preparedBatchWeightedBank batchWeightedBank batchWeightedBase
  congr 1
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = 110 <;> simp [Function.update_apply,hi]

theorem cachedBatchWeightedSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q N B : ℕ} (lo : ℕ → ℕ)
    (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1)) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hL : 0 < L) (v : HS 121 Q A U) (S : Stacks 121 A)
    (tail cacheTail : List (Fin (A+4)))
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hN : (S.R 101).length = N)
    (hB : S.R 116 = List.replicate B tick) (hpacket : S.R 109 = tail)
    (hclean : CClean mul (embStk weightCacheCoreReg S))
    (hblank : ∀ r, (embStk weightCacheCoreReg S).R (cr r) = [])
    (hfresh : ∀ k ∈ ([(64 : Fin 121),65,94,96,104,105,106,107,108,111,113,115,119,120] : List (Fin 121)), S.R k = [])
    (hcache : S.R 117 = batchWeightPage A (2*q+8) q P s t u B L lo++cacheTail)
    (hcacheCount : (S.R 118).length = 2*(B*(L*(2*q+8)))) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ cachedBatchWeightedSetupCost P N q s t u band L B ∧
      Exec body (cachedBatchWeightedSetup hQ) (mk v S) m (mk v' S') ∧
      embStk weightCacheCoreReg S' =
        batchWeightedBank (embStk weightCacheCoreReg S) P s t u band L q N B lo tail ∧
      ∀ i, 117 ≤ i.val → S'.L i = S.L i ∧ S'.R i = S.R i := by
  let page := batchWeightPage A (2*q+8) q P s t u B L lo
  obtain ⟨v₁,hu₁,he₁⟩ := copyPrefix_exec (body := body)
    (show [(118 : Fin 121),117,110,119,120].Nodup by decide) v S page cacheTail hcache
    (by simpa [page] using hcacheCount) (hfresh 119 (by simp)) (hfresh 120 (by simp))
  let W : Stacks 121 A := {S with R := Function.update S.R 110 (page++S.R 110)}
  have hcleanW : CClean mul (embStk weightCacheCoreReg W) := by
    intro i
    have hne : weightCacheCoreReg (mul i) ≠ (110 : Fin 121) := by
      intro he
      have hv := congrArg (fun k : Fin 121 => k.val) he
      simp only [weightCacheCoreReg,mul] at hv
      omega
    exact ⟨(hclean i).1, by simpa [W,embStk,hne] using (hclean i).2⟩
  have hblankW : ∀ r, (embStk weightCacheCoreReg W).R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have hne : weightCacheCoreReg (cr r) ≠ (110 : Fin 121) := by
      intro he
      have hv := congrArg (fun k : Fin 121 => k.val) he
      simp only [weightCacheCoreReg] at hv
      omega
    simpa [W,embStk,hne] using hblank r
  obtain ⟨vi,m,hu,hm,he⟩ := preparedBatchWeightedSetup_exec
    (body := fun p : Empty => nomatch p) hQ hA hP hqMax hs hst hu hL
    (embDn weightCacheCoreReg v₁) (embStk weightCacheCoreReg W) tail
    hprecision hsR htR huR hband hrows hcount hq hN hB hpacket hcleanW hblankW (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [W,embStk,weightCacheCoreReg] using hfresh _ (by simp))
  obtain ⟨v₂,M,he₂,hv₂,hu₂,hproj,hoff⟩ := exec_emb (body' := body) (ι := Empty.elim)
    weightCacheCoreReg_injective (fun p => nomatch p) he v₁ rfl W rfl
  refine ⟨v₂,M,10*page.length+10+m,hu₂.trans (hu.trans hu₁),?_,Exec.seq he₁ he₂,?_,?_⟩
  · simp only [cachedBatchWeightedSetupCost,page,batchWeightPage_length]
    omega
  · rw [hproj]
    have hv : embStk weightCacheCoreReg W =
        {embStk weightCacheCoreReg S with R := (Function.update (embStk weightCacheCoreReg S).R 110
          (page++S.R 110))} := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i = 110
      · subst i; rfl
      have hne : weightCacheCoreReg i ≠ (110 : Fin 121) := by
        intro he
        apply hi
        apply Fin.ext
        exact congrArg (fun k : Fin 121 => k.val) he
      simp [W,embStk,Function.update_of_ne hi,Function.update_of_ne hne]
    rw [hv]
    exact preparedBatchWeightedBank_weights _ _ _ _ _ _ _ _ _ _ _ _
  · intro i hi
    have hne : i ≠ (110 : Fin 121) := by intro he; subst i; norm_num at hi
    have h := hoff i (by
      intro j he
      have hv := congrArg (fun k : Fin 121 => k.val) he
      dsimp [weightCacheCoreReg] at hv
      omega)
    simpa [W,hne] using h

/-- Weight replay and inverse expansion have a linear cell increment, with no weight evaluation. -/
theorem cachedBatchWeightedSetupCost_affine (P N q s t u band L B : ℕ) :
    cachedBatchWeightedSetupCost P N q s t u band L B =
      cachedBatchWeightedSetupCost P N q s t u band L 0+
        B*(58*(L*(2*q+8))+49) := by
  dsimp only [cachedBatchWeightedSetupCost,preparedBatchWeightedSetupCost]
  rw [batchInverseSetupCost_affine P N q s t u band L B]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
