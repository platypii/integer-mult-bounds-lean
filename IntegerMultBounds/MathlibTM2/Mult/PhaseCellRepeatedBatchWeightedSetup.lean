module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatedWeightSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishBatchSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightedSetup

/-! Equal-origin replicas share both their numerical inverse and exact weights.
The owned unary origin is released before entering the ordinary batch ABI. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def repeatedBatchWeightedSetup (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq generateRuntimeWidth (.seq repeatedWeightSetup (.seq (uclear 111) (finishBatchSetup hQ)))

def repeatedBatchWeightedSetupCost (P N q s t u band L lo B : ℕ) : ℕ :=
  (4*q+5)+repeatedWeightSetupCost P s t u q L lo (2*q+8) B+
    (2*lo+2)+finishBatchSetupCost P N q s t u band L B

theorem repeatedBatchWeightedSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q N lo B : ℕ}
    (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1)) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hL : 0 < L) (hLs : L ≤ s) (hlo : lo < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hN : (S.R 101).length = N)
    (hB : S.R 116 = List.replicate B tick) (hloR : (S.R 111).length = lo)
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(64 : Fin 117),65,94,96,104,105,106,107,108,113,115], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ repeatedBatchWeightedSetupCost P N q s t u band L lo B ∧
      Exec body (repeatedBatchWeightedSetup hQ) (mk v S) n
        (mk v' (batchWeightedBank { S with R := Function.update S.R 111 [] }
          P s t u band L q N B (fun _ => lo) (S.R 109))) := by
  obtain ⟨v₁,hu₁,he₁⟩ := generateRuntimeWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 104 (by simp))
  let Sw : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate (2*q+8) tick) }
  have htable : ∀ r, Sw.R (coefficientReg r) = [] := by
    intro r
    have hr := coefficientReg_range r
    have hn : coefficientReg r ≠ (94 : Fin 117) := by intro he; rw [he] at hr; omega
    simpa [Sw,hn,mul] using (hclean ⟨(coefficientReg r).val,by omega⟩).2
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := repeatedWeightSetup_exec (body := body)
    P s t u q L lo (2*q+8) B v₁ Sw
    (by simpa [Sw] using hprecision) (by simpa [Sw] using hsR) (by simpa [Sw] using htR)
    (by simpa [Sw] using huR) (by simpa [Sw] using hq) (by simpa [Sw] using hrows)
    (by simpa [Sw] using hcount) (by simpa [Sw] using hloR) (by simp [Sw])
    (by simp [Sw,hB]) htable (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [Sw] using hfresh _ (by simp)) hP hs hst hu hlo hLs
  let T : Stacks 117 A := { Sw with R := (Function.update Sw.R 110
    (batchWeightPage A (2*q+8) q P s t u B L (fun _ => lo)++S.R 110)) }
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 111 v₂ T
  let V : Stacks 117 A := { T with R := Function.update T.R 111 [] }
  have he₃' : Exec body (uclear 111) (mk v₂ T) (2*lo+2) (mk v₃ V) := by
    simpa [V,T,Sw,hloR] using he₃
  have hcleanV : CClean mul V := by
    intro i
    refine ⟨(hclean i).1,?_⟩
    have hn (k : Fin 117) (hk : 64 ≤ k.val) : mul i ≠ k := by
      intro he; have hv := congrArg Fin.val he; have hi := i.isLt; simp only [mul] at hv; omega
    simpa [V,T,Sw,hn 94 (by decide),hn 110 (by decide),hn 111 (by decide)] using (hclean i).2
  have hblankV : ∀ r, V.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have h94 : cr r ≠ (94 : Fin 117) := by intro he; exact hr.2.2.2 (congrArg Fin.val he)
    have hn (k : Fin 117) (hk : 96 ≤ k.val) : cr r ≠ k := by intro he; rw [he] at hr; omega
    simpa [V,T,Sw,h94,hn 110 (by decide),hn 111 (by decide)] using hblank r
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := finishBatchSetup_exec (body := body) (band := band) (B := B)
    hQ hA hP hqMax hs hst.le hu hL v₃ V (S.R 109)
    (by simpa [V,T,Sw] using hprecision) (by simpa [V,T,Sw] using hsR)
    (by simpa [V,T,Sw] using htR) (by simpa [V,T,Sw] using huR)
    (by simpa [V,T,Sw] using hband) (by simpa [V,T,Sw] using hrows)
    (by simpa [V,T,Sw] using hcount) (by simpa [V,T,Sw] using hq)
    (by simpa [V,T,Sw] using hN) (by simpa [V,T,Sw] using hB)
    (by simp [V,T,Sw]) (by simp [V,T,Sw]) hcleanV hblankV (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [V,T,Sw] using hfresh _ (by simp))
  refine ⟨v₄,(4*q+5)+(n₂+((2*lo+2)+n₄)),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    by dsimp only [repeatedBatchWeightedSetupCost]; omega,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄))).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases h94 : k = 94
  · subst k; simp [batchWeightedBank,batchInverseBank]
  by_cases h109 : k = 109
  · subst k; simp [batchWeightedBank,batchInverseBank]
  by_cases h110 : k = 110
  · subst k; simp [batchWeightedBank,batchInverseBank,batchWeightedBase,consumedGeometryBank,geometryHeaderPorts,V,T,Sw]
  by_cases h116 : k = 116
  · subst k; simp [batchWeightedBank,batchInverseBank,batchWeightedBase,consumedGeometryBank,geometryHeaderPorts,V,T,Sw]
  by_cases h111 : k = 111
  · subst k; simp [batchWeightedBank,batchInverseBank,batchWeightedBase,consumedGeometryBank,geometryHeaderPorts,V,T,Sw]
  simp [batchWeightedBank,batchInverseBank,batchWeightedBase,consumedGeometryBank,V,T,Sw,
    Function.update_apply,h94,h109,h110,h116,h111]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
