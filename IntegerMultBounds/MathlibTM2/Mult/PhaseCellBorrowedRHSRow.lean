module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConsumedIntegerRow

/-! Stage an RHS from a retained physical prefix above the precision header,
execute the row and remove the staged word without changing that header. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def borrowedRHSRow (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (copyPrefix 94 93 112 97 98)
    (.seq (consumedIntegerRow hQ) (discardPrefix 94 112 97 98))

theorem borrowedRHSRow_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L q w : ℕ} (hw : 1 ≤ w) (hqw : q ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w xs++tailX) (ha : S.R 111 = cstream A w as++tailA)
    (hrhs : S.R 93 = csyms A w rhs++tailR) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w q)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) (h109 : S.R 109 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ L*(rmulCost w+61*w+32)+30*w+92 ∧
      Exec body (borrowedRHSRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          113 (csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++S.R 113))
          110 tailX) 111 tailA) 102 [])}) := by
  have h97 : S.R 97 = [] := hwork 97 (by simp [integerRowWork])
  have h98 : S.R 98 = [] := hwork 98 (by simp [integerRowWork])
  obtain ⟨v₁,hu₁,he₁⟩ := copyPrefix_exec (body := body)
    (count := 94) (src := 93) (dst := 112) (saved := 97) (tmp := 98) (by decide)
    v S (csyms A w rhs) tailR hrhs (by simp [hwR]) h97 h98
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 112 (csyms A w rhs++S.R 112)}
  have hcr (r : CR) : cr r ≠ (112 : Fin 117) := by
    have hr := (cr_range r).2.1
    intro he
    have hv := congrArg Fin.val he
    omega
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := consumedIntegerRow_exec (body := body) hQ hA hw hqw xs as rhs
    hxlen halen hxs has v₁ S₁ tailX tailA (S.R 112)
    (by simpa [S₁] using hL) (by simpa [S₁] using hwR)
    (by simpa [S₁] using hx) (by simpa [S₁] using ha) (by simp [S₁])
    (by intro i
        have hn : mul i ≠ (112 : Fin 117) := by
          intro he
          have hv := congrArg Fin.val he
          have hi := i.isLt
          simp only [mul] at hv
          omega
        simpa [S₁,hn] using hc i)
    (by simpa only [S₁,Function.update_of_ne (hcr _)] using hready)
    (by intro k hk
        have hn : k ≠ 112 := by
          simp only [integerRowWork,List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h
          all_goals subst k; first | exact hcr _ | decide
        simpa [S₁,hn] using hwork k hk)
    (by simpa [S₁] using h109)
  let z := rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update (Function.update (Function.update (Function.update S₁.R
    113 (csyms A w z++S₁.R 113)) 110 tailX) 111 tailA) 102 [])}
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := 94) (src := 112) (trash := 97) (tmp := 98) (by decide)
    (csyms A w rhs) (S.R 112) v₂ S₂ (by simp [S₂,S₁])
    (by simp [S₂,S₁,hwR]) (by simpa [S₂,S₁] using h97) (by simpa [S₂,S₁] using h98)
  refine ⟨v₃,(10*w+10)+(m₂+(6*w+6)),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by simp) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h : k = 112 <;> simp [S₂,S₁,h,z,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
