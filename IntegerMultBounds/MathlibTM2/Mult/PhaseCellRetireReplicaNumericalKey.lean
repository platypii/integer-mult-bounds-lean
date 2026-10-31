module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseWeightCache
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Derive the RHS ownership count from the retained replay clock, retire both
owned numerical prefixes, and release the clock. Borrowed tails survive exactly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

def retireReplicaNumericalKey : Pr P 121 Q A U :=
  .seq (udiv 2 118 116 119)
    (.seq (discardPrefix 116 110 119 120) (.seq (uclear 116) releaseWeightCache))

def retiredReplicaNumericalKeyBank (S : Stacks 121 A)
    (rhsTail cacheTail : List (Fin (A+4))) : Stacks 121 A :=
  {S with R := (Function.update (Function.update (Function.update S.R 110 rhsTail) 117 cacheTail) 118 [])}

theorem retireReplicaNumericalKey_exec (n : ℕ)
    (rhs rhsTail page cacheTail : List (Fin (A+4)))
    (hrhsLen : rhs.length = n) (hpageLen : page.length = 2*n)
    (v : HS 121 Q A U) (S : Stacks 121 A)
    (hrhs : S.R 110 = rhs++rhsTail) (hpage : S.R 117 = page++cacheTail)
    (hclock : (S.R 118).length = 2*n)
    (hclean : ∀ k ∈ [(116 : Fin 121),119,120], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 32*n+20 ∧
      Exec body retireReplicaNumericalKey (mk v S) m
        (mk v' (retiredReplicaNumericalKeyBank S rhsTail cacheTail)) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := udiv_exec (body := body) (c := 2) (a := 118) (b := 116) (t := 119)
    (by decide) (by decide) (by decide) (by decide) v S (hclean _ (by simp))
  let M : Stacks 121 A := {S with R := Function.update S.R 116 (List.replicate n tick)}
  have hhalf : 2*n/2 = n := by omega
  have he₁' : Exec body (udiv 2 118 116 119) (mk v S) m₁ (mk v₁ M) := by
    simpa only [hclock,hclean 116 (by simp),List.append_nil,hhalf] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := 116) (src := 110) (trash := 119) (tmp := 120) (by decide) rhs rhsTail v₁ M
    (by simpa [M] using hrhs) (by simp [M,hrhsLen])
    (by simpa [M] using hclean 119 (by simp)) (by simpa [M] using hclean 120 (by simp))
  let N : Stacks 121 A := {M with R := Function.update M.R 110 rhsTail}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 116 v₂ N
  let K : Stacks 121 A := {N with R := Function.update N.R 116 []}
  obtain ⟨v₄,hu₄,he₄⟩ := releaseWeightCache_exec (body := body) v₃ K page cacheTail n hpageLen
    (by simpa [K,N,M] using hpage) (by simpa [K,N,M] using hclock)
    (by simpa [K,N,M] using hclean 119 (by simp)) (by simpa [K,N,M] using hclean 120 (by simp))
  have hlenN : (N.R 116).length = n := by simp [N,M]
  refine ⟨v₄,m₁+((6*rhs.length+6)+((2*(N.R 116).length+2)+(16*n+8))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,?_⟩
  · rw [hclock] at hm₁
    rw [hrhsLen,hlenN]
    omega
  · have hex := Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))
    have hbank : {K with R := (Function.update (Function.update K.R 117 cacheTail) 118 [])} =
        retiredReplicaNumericalKeyBank S rhsTail cacheTail := by
      ext1
      · rfl
      · rfl
      · rfl
      · funext k
        by_cases h116 : k = 116
        · subst k; simp [K,N,M,retiredReplicaNumericalKeyBank,hclean 116 (by simp)]
        simp [K,N,M,retiredReplicaNumericalKeyBank,Function.update_apply,h116]
    simpa only [retireReplicaNumericalKey,hbank] using hex

theorem retireReplicaNumericalKey_pushBound :
    mnNativePushBound 3 (retireReplicaNumericalKey (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [retireReplicaNumericalKey,releaseWeightCache,discardPrefix,udiv,divChain,
    transfer,scanR,keepIn,transferAct,moveR,moveStep,uclear,drainR,popDo,whileR,peekR,
    mnNativePushBound,mnActPush]

theorem retireReplicaNumericalKey_exec_within (n : ℕ)
    (rhs rhsTail page cacheTail : List (Fin (A+4)))
    (hrhsLen : rhs.length = n) (hpageLen : page.length = 2*n)
    (v : HS 121 Q A U) (S : Stacks 121 A)
    (hrhs : S.R 110 = rhs++rhsTail) (hpage : S.R 117 = page++cacheTail)
    (hclock : (S.R 118).length = 2*n)
    (hclean : ∀ k ∈ [(116 : Fin 121),119,120], S.R k = []) (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 32*n+20 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*(32*n+20)) depth
        retireReplicaNumericalKey (mk v S) m (mk v' (retiredReplicaNumericalKeyBank S rhsTail cacheTail)) := by
  obtain ⟨v',m,hu,hm,he⟩ := retireReplicaNumericalKey_exec n rhs rhsTail page cacheTail hrhsLen hpageLen
    v S hrhs hpage hclock hclean
  exact ⟨v',m,hu,hm,mn_native_exec_within he 3 retireReplicaNumericalKey_pushBound depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
