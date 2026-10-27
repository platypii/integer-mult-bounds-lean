module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedGeneratedBatchSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInputBank

/-! The cached batch ABI has raw RHS words and control headers, without repeated origin packets. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def cachedCoreInputBank {A : ℕ} (P N q l s t u band L B : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := batchInputBank P N q l s t u band L B lo rhs borrowed outTail inp out
  {S with R := Function.update S.R 109 (List.replicate l tick)}

theorem generatedBatchBank_cachedCore {A : ℕ} (P N q l s t u band L B : ℕ) (lo : ℕ → ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    generatedBatchBank (cachedCoreInputBank P N q l s t u band L B lo rhs borrowed outTail inp out)
      P s t u band L q N l B lo rhs borrowed (List.replicate l tick) =
    generatedBatchBank (batchInputBank P N q l s t u band L B lo rhs borrowed outTail inp out)
      P s t u band L q N l B lo rhs borrowed (List.replicate l tick) := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = 109 <;>
    simp [generatedBatchBank,batchHeaderBank,batchWeightedBank,batchInverseBank,batchWeightedBase,
      consumedGeometryBank,cachedCoreInputBank,Function.update_apply,hi]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

theorem cachedBatchInputBank_setup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (P N q l s t u band L B : ℕ) (lo : ℕ → ℕ) (hP : 13 ≤ P) (hqMax : q ≤ 2*(N+1))
    (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hL : 0 < L)
    (rhs borrowed outTail cacheTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (v : HS 121 Q A U) (S : Stacks 121 A) (hrhs : rhs.length = B*L*(2*q+8))
    (hinput : embStk weightCacheCoreReg S =
      cachedCoreInputBank P N q l s t u band L B lo rhs borrowed outTail inp out)
    (hcache : S.R 117 = batchWeightPage A (2*q+8) q P s t u B L lo++cacheTail)
    (hcacheCount : (S.R 118).length = 2*(B*(L*(2*q+8))))
    (h119 : S.R 119 = []) (h120 : S.R 120 = []) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ cachedGeneratedBatchSetupCost P N q s t u band l L B ∧
      Exec body (cachedGeneratedBatchSetup hQ) (mk v S) m (mk v' S') ∧
      embStk weightCacheCoreReg S' =
        generatedBatchBank (batchInputBank P N q l s t u band L B lo rhs borrowed outTail inp out)
          P s t u band L q N l B lo rhs borrowed (List.replicate l tick) ∧
      ∀ i, 117 ≤ i.val → S'.L i = S.L i ∧ S'.R i = S.R i := by
  let E := cachedCoreInputBank P N q l s t u band L B lo rhs borrowed outTail inp out
  have hlow (k : Fin 117) (hk : k.val < 93) : E.R k = [] := by
    have hn (n : ℕ) (h : 93 ≤ n) : k.val ≠ n := by omega
    simp [E,cachedCoreInputBank,batchInputBank,Function.update_apply,Fin.ext_iff,
      hn 101 (by decide),hn 102 (by decide),hn 103 (by decide),hn 97 (by decide),hn 98 (by decide),
      hn 99 (by decide),hn 100 (by decide),hn 109 (by decide),hn 112 (by decide),hn 114 (by decide),
      hn 116 (by decide),hn 110 (by decide),hn 93 (by decide)]
  have hclean : CClean mul (embStk weightCacheCoreReg S) := by
    rw [hinput]
    intro i
    refine ⟨rfl,hlow (mul i) ?_⟩
    have hi := i.isLt
    dsimp [mul]
    omega
  have hblank : ∀ r, (embStk weightCacheCoreReg S).R (cr r) = [] := by
    rw [hinput]
    intro r
    obtain ⟨_,hhi,h93,_⟩ := cr_range r
    have hn (n : ℕ) (h : 97 ≤ n) : (cr r).val ≠ n := by omega
    simp [cachedCoreInputBank,batchInputBank,Function.update_apply,Fin.ext_iff,
      hn 101 (by decide),hn 102 (by decide),hn 103 (by decide),hn 97 (by decide),hn 98 (by decide),
      hn 99 (by decide),hn 100 (by decide),hn 109 (by decide),hn 112 (by decide),hn 114 (by decide),
      hn 116 (by decide),hn 110 (by decide),h93]
  have hread (i : Fin 117) : S.R (weightCacheCoreReg i) = E.R i :=
    congrArg (fun T : Stacks 117 A => T.R i) hinput
  obtain ⟨v',S',m,huser,hcost,hexec,hproj,hoff⟩ := cachedGeneratedBatchSetup_exec (body := body) (l := l)
    hQ hA lo hP hqMax hs hst hu hL v S rhs borrowed (List.replicate l tick) cacheTail
    (by simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using congrArg List.length (hread 114))
    (by simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using congrArg List.length (hread 97))
    (by simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using congrArg List.length (hread 98))
    (by simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using congrArg List.length (hread 99))
    (by simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using congrArg List.length (hread 100))
    (by simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using congrArg List.length (hread 102))
    (by simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using congrArg List.length (hread 103))
    (by simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using congrArg List.length (hread 112))
    (by simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using congrArg List.length (hread 101))
    (by simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 116)
    (by simpa [E,cachedCoreInputBank,weightCacheCoreReg] using hread 109)
    (by simp) (by simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 110)
    hrhs hclean hblank (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      any_goals exact h119
      any_goals exact h120
      all_goals first
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 64
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 65
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 94
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 96
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 104
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 105
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 106
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 107
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 108
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 111
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 113
        | simpa [E,cachedCoreInputBank,batchInputBank,weightCacheCoreReg] using hread 115)
    hcache hcacheCount
  refine ⟨v',S',m,huser,hcost,hexec,?_,hoff⟩
  rw [hproj,hinput,generatedBatchBank_cachedCore]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
