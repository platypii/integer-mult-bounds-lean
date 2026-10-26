module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchSetupHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInverseSetup

/-! Finish a generated weight page with one shared inverse construction.
This continuation is independent of how equal-key weight replicas were built. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def finishBatchSetup (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq saveBatchInverseHeader (batchInverseSetup hQ)

def finishBatchSetupCost (P N q s t u band L B : ℕ) : ℕ :=
  (6*B+2*(2*q+8)+10)+batchInverseSetupCost P N q s t u band L B

theorem finishBatchSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q N B : ℕ} (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1))
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hN : (S.R 101).length = N)
    (hB : S.R 116 = List.replicate B tick) (hw : (S.R 94).length = 2*q+8) (hpacket : S.R 109 = tail)
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117),104,105,106,107,108,113,115], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ finishBatchSetupCost P N q s t u band L B ∧
      Exec body (finishBatchSetup hQ) (mk v S) n
        (mk v' (batchInverseBank { S with R := Function.update S.R 116 [] } B P s t u band L q N tail)) := by
  obtain ⟨v₁,hu₁,he₁⟩ := saveBatchInverseHeader_exec (body := body) B (2*q+8) v S hB hw (hfresh 107 (by simp))
  let T : Stacks 117 A := { S with R := (Function.update (Function.update (Function.update S.R
    109 (List.replicate B tick++blank::S.R 109)) 94 []) 116 []) }
  have hcleanT : CClean mul T := by
    intro i
    refine ⟨(hclean i).1,?_⟩
    have hn (k : Fin 117) (hk : 64 ≤ k.val) : mul i ≠ k := by
      intro he; have hv := congrArg Fin.val he; have hi := i.isLt; simp only [mul] at hv; omega
    simpa [T,hn 109 (by decide),hn 94 (by decide),hn 116 (by decide)] using (hclean i).2
  have hblankT : ∀ r, T.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have h94 : cr r ≠ (94 : Fin 117) := by intro he; exact hr.2.2.2 (congrArg Fin.val he)
    have hn (k : Fin 117) (hk : 96 ≤ k.val) : cr r ≠ k := by intro he; rw [he] at hr; omega
    simpa [T,h94,hn 109 (by decide),hn 116 (by decide)] using hblank r
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := batchInverseSetup_exec (body := body) (band := band) (B := B)
    hQ hA hP hqMax hs hst hu hL v₁ T tail
    (by simpa [T] using hprecision) (by simpa [T] using hsR) (by simpa [T] using htR)
    (by simpa [T] using huR) (by simpa [T] using hband) (by simpa [T] using hrows)
    (by simpa [T] using hcount) (by simpa [T] using hq) (by simpa [T] using hN)
    (by simp [T,hpacket]) hcleanT hblankT (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [T]
      · simpa [T] using hfresh 96 (by simp)
      · simpa [T] using hfresh 104 (by simp)
      · simpa [T] using hfresh 105 (by simp)
      · simpa [T] using hfresh 106 (by simp)
      · simpa [T] using hfresh 107 (by simp)
      · simpa [T] using hfresh 108 (by simp)
      · simpa [T] using hfresh 113 (by simp)
      · simpa [T] using hfresh 115 (by simp)
      · simp [T])
  refine ⟨v₂,(6*B+2*(2*q+8)+10)+n₂,hu₂.trans hu₁,
    by dsimp only [finishBatchSetupCost]; omega,(Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases h94 : k = 94
  · subst k; simp [batchInverseBank]
  by_cases h109 : k = 109
  · subst k; simp [batchInverseBank]
  simp [batchInverseBank,consumedGeometryBank,T,Function.update_apply,h94,h109]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
