module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBorrowedRHSRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReadiness

/-! Generate and release readiness around one row with a borrowed physical RHS. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def generatedReadyRow (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq couplingReadiness (.seq (borrowedRHSRow hQ) (clearWords [cr .wn,cr .pn,cr .nn]))

def generatedReadyRowCost (L q w band : ℕ) : ℕ :=
  prepareCost q w+L*(rmulCost w+61*w+32)+32*w+8*q+4*band+2*Schoenhage.Schedule.topN w+109

theorem generatedReadyRow_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L q w : ℕ} (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w) (hq : (S.R 112).length = q)
    (hx : S.R 110 = cstream A w xs++tailX) (ha : S.R 111 = cstream A w as++tailA)
    (hrhs : S.R 93 = csyms A w rhs++tailR) (hc : CClean mul S)
    (hblank : ∀ r : CR, S.R (cr r) = []) (hleft : S.L 100 = [])
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) (h109 : S.R 109 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedReadyRowCost L q w (S.R 100).length ∧
      Exec body (generatedReadyRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          113 (csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++S.R 113))
          110 tailX) 111 tailA) 102 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := couplingReadiness_exec (body := body) q w hw5 hqw v S hq hwR hleft h109
    (by intro k hk
        let i : Fin 64 := ⟨k.val,by omega⟩
        have hi : mul i = k := Fin.ext rfl
        simpa only [hi] using (hc i).2)
    (by intro r _; exact hblank r)
  let S₁ : Stacks 117 A := {S with R := counterR q w S.R}
  have hoff (k : Fin 117) (hk : 95 < k.val) : S₁.R k = S.R k := by
    have hn (r : CR) : k ≠ cr r := by
      have hr := (cr_range r).2.1
      intro he
      have hv := congrArg Fin.val he
      omega
    simp [S₁,counterR,hn]
  have hwork₁ : ∀ k ∈ integerRowWork, S₁.R k = [] := by
    have hd : ∀ k ∈ integerRowWork, k ≠ cr .wn ∧ k ≠ cr .pn ∧ k ≠ cr .nn := by decide
    intro k hk
    simpa [S₁,counterR,(hd k hk).1,(hd k hk).2.1,(hd k hk).2.2] using hwork k hk
  have hclean₁ : CClean mul S₁ := by
    intro i
    simpa [S₁,counterR,Ne.symm (cr_mul _ i)] using hc i
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := borrowedRHSRow_exec (body := body) hQ hA (by omega) (by omega)
    xs as rhs hxlen halen hxs has v₁ S₁ tailX tailA tailR
    (by simpa [hoff 102 (by decide)] using hL)
    (by simpa [S₁,counterR,cr,OutputPlacement.code] using hwR)
    (by simpa [hoff 110 (by decide)] using hx)
    (by simpa [hoff 111 (by decide)] using ha)
    (by simpa [S₁,counterR,cr,OutputPlacement.code] using hrhs)
    hclean₁ (counterR_ready q w S.R hblank) hwork₁ (by simpa [hoff 109 (by decide)] using h109)
  let z := rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update (Function.update (Function.update (Function.update S₁.R
    113 (csyms A w z++S₁.R 113)) 110 tailX) 111 tailA) 102 [])}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [cr .wn,cr .pn,cr .nn] (by decide) v₂ S₂
  have hsum : ([cr .wn,cr .pn,cr .nn].map (fun k => (S₂.R k).length)).sum =
      w+q+Schoenhage.Schedule.topN w := by simp [S₂,S₁,counterR,cr,OutputPlacement.code,Nat.add_assoc]
  refine ⟨v₃,m₁+(m₂+(2*(w+q+Schoenhage.Schedule.topN w)+7)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp only [generatedReadyRowCost]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hwn : k = cr .wn
    · subst k
      simpa [S₂,S₁,counterR,cr,OutputPlacement.code] using (hblank CR.wn).symm
    by_cases hpn : k = cr .pn
    · subst k
      simpa [S₂,S₁,counterR,cr,OutputPlacement.code] using (hblank CR.pn).symm
    by_cases hnn : k = cr .nn
    · subst k
      simpa [S₂,S₁,counterR,cr,OutputPlacement.code] using (hblank CR.nn).symm
    have hn₁ : (113 : Fin 117) ≠ cr .wn := by decide
    have hn₂ : (113 : Fin 117) ≠ cr .pn := by decide
    have hn₃ : (113 : Fin 117) ≠ cr .nn := by decide
    simp [S₂,S₁,counterR,hwn,hpn,hnn,hn₁,hn₂,hn₃,z,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
