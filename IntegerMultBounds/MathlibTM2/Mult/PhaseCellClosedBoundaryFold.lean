module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryFold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryFoldInputs
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Generate the canonical folded boundary page and release its temporary controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def boundaryInputReg (i : Fin 117) : Fin 148 := ⟨i.val,by omega⟩

theorem boundaryInputReg_injective : Function.Injective boundaryInputReg := by
  intro i j h
  exact Fin.ext (congrArg (fun r : Fin 148 => r.val) h)

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def closedBoundaryFold : Pr P₀ 148 Q A U :=
  .seq (embProg boundaryInputReg id preparedBoundaryFoldInputs)
    (.seq retainedBoundaryFold (.seq (moveR 6 1 id)
      (.seq (moveR 1 109 id) (clearWords [0,2,3]))))

def closedBoundaryFoldCost (s t band a b : ℕ) [NeZero s] : ℕ :=
  preparedBoundaryFoldInputsCost s t band a b+
    70*((haloBoundary s t band a b).card+1)*(publicationGeometryWidth t band+1)+71

theorem closedBoundaryFold_exec {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h115 : S.R 115 = []) (h116 : S.R 116 = []) (h109 : S.R 109 = [])
    (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 148, r.val < 77 → S.R r = []) (hleft : ∀ r, S.L r = []) :
    let V := publicationGeometryWidth t band
    let n := (haloBoundary s t band a b).card
    let output := cstream A V ((bFoldOrder s (haloBoundary s t band a b)).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
    ∃ v' m, v'.user = v.user ∧ m ≤ closedBoundaryFoldCost s t band a b ∧
      Exec (embTab boundaryInputReg body) closedBoundaryFold (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          115 (List.replicate V tick)) 116 (List.replicate n tick)) 109 output)}) := by
  dsimp only
  let V := publicationGeometryWidth t band
  let n := (haloBoundary s t band a b).card
  let output := cstream A V ((bFoldOrder s (haloBoundary s t band a b)).map
    (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := preparedBoundaryFoldInputs_exec (body := body)
    hst haS hbS hbandS (embDn boundaryInputReg v) (embStk boundaryInputReg S)
    (by simpa [embStk,boundaryInputReg] using hs) (by simpa [embStk,boundaryInputReg] using ht)
    (by simpa [embStk,boundaryInputReg] using hband) (by simpa [embStk,boundaryInputReg] using ha)
    (by simpa [embStk,boundaryInputReg] using hb) (by simpa [embStk,boundaryInputReg] using h115)
    (by simpa [embStk,boundaryInputReg] using h116) (by simpa [embStk,boundaryInputReg] using h109)
    (by simpa [embStk,boundaryInputReg] using h106) (by simpa [embStk,boundaryInputReg] using h108)
    (by intro r hr; exact hblank _ (by simp [boundaryInputReg]; omega))
  have hbody : ∀ p, (embTab boundaryInputReg body) (id p) = embProg boundaryInputReg id (body p) := fun _ => rfl
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := id) (body' := embTab boundaryInputReg body)
    boundaryInputReg_injective hbody he₁ v rfl S rfl
  let S₁ : Stacks 148 A := {S with R := (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update S.R 115 (List.replicate V tick))
      109 (boundaryOrderSymbols A V s t band a b)) 116 (List.replicate n tick))
      0 (List.replicate (n/2) tick)) 2 (List.replicate ((n+1)/2-n/2) tick))
      3 (List.replicate (((n+1)/2)*V) tick))}
  have he₂' : Exec (embTab boundaryInputReg body) (embProg boundaryInputReg id preparedBoundaryFoldInputs)
      (mk v S) m₁ (mk v₂ S₁) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    let B₀ := embStk boundaryInputReg S
    let B₁ : Stacks 117 A := {B₀ with R := Function.update B₀.R 115 (List.replicate V tick)}
    let B₂ : Stacks 117 A := {B₁ with R := Function.update B₁.R 109 (boundaryOrderSymbols A V s t band a b)}
    let B₃ : Stacks 117 A := {B₂ with R := Function.update B₂.R 116 (List.replicate n tick)}
    let B₄ : Stacks 117 A := {B₃ with R := Function.update B₃.R 0 (List.replicate (n/2) tick)}
    let B₅ : Stacks 117 A := {B₄ with R := Function.update B₄.R 2 (List.replicate ((n+1)/2-n/2) tick)}
    let B₆ : Stacks 117 A := {B₅ with R := Function.update B₅.R 3 (List.replicate (((n+1)/2)*V) tick)}
    symm
    change embOvr boundaryInputReg B₆.get S = S₁
    rw [embOvr_updR boundaryInputReg_injective B₅ S 3 _,
      embOvr_updR boundaryInputReg_injective B₄ S 2 _,
      embOvr_updR boundaryInputReg_injective B₃ S 0 _,
      embOvr_updR boundaryInputReg_injective B₂ S 116 _,
      embOvr_updR boundaryInputReg_injective B₁ S 109 _,
      embOvr_updR boundaryInputReg_injective B₀ S 115 _,embOvr_stk]
    rfl
  have hlow (r : Fin 148) (hr : 6 ≤ r.val) (hr' : r.val < 77) : S₁.R r = [] := by
    have h0 : r ≠ 0 := by intro he; subst r; norm_num at hr
    have h2 : r ≠ 2 := by intro he; subst r; norm_num at hr
    have h3 : r ≠ 3 := by intro he; subst r; norm_num at hr
    have h109' : r ≠ 109 := by intro he; subst r; norm_num at hr'
    have h115' : r ≠ 115 := by intro he; subst r; norm_num at hr'
    have h116' : r ≠ 116 := by intro he; subst r; norm_num at hr'
    simpa [S₁,h0,h2,h3,h109',h115',h116'] using hblank r hr'
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := retainedBoundaryFold_exec (body := embTab boundaryInputReg body)
    hst band a b V hbS v₂ S₁ (by simp [S₁,n]) (by simp [S₁,n]) (by simp [S₁,n])
    (by simp [S₁,n]) (by simp [S₁,n]) (by simp [S₁,n]) hlow hleft
  let S₂ : Stacks 148 A := {S₁ with R := Function.update (Function.update S₁.R 109 []) 6 output}
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec (embTab boundaryInputReg body) 6 1 (by decide) id v₃ S₂
  let S₃ : Stacks 148 A := {S₂ with R := movedR S₂.R 6 1 id (S₂.R 6)}
  have h1 : S₂.R 1 = [] := by simpa [S₂,S₁] using hblank 1 (by decide)
  have houtlen : output.length = n*V := by
    simp [output,n,bFoldOrder]
  have h1len : (S₃.R 1).length = n*V := by simp [S₃,movedR,S₂,S₁,hblank 1 (by decide),houtlen]
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec (embTab boundaryInputReg body) 1 109 (by decide) id v₄ S₃
  let S₄ : Stacks 148 A := {S₃ with R := movedR S₃.R 1 109 id (S₃.R 1)}
  obtain ⟨v₆,hu₆,he₆⟩ := clearWords_exec (body := embTab boundaryInputReg body)
    [(0 : Fin 148),2,3] (by decide) v₅ S₄
  have hsum : ([(0 : Fin 148),2,3].map (fun r => (S₄.R r).length)).sum =
      n/2+((n+1)/2-n/2)+((n+1)/2)*V := by simp [S₄,S₃,S₂,S₁,movedR,Nat.add_assoc]
  refine ⟨v₆,m₁+(m₃+((2*(n*V)+2)+((2*(n*V)+2)+(2*(n/2+((n+1)/2-n/2)+((n+1)/2)*V)+7)))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),?_,
    (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆)))).cast ?_ ?_⟩
  · change _ ≤ preparedBoundaryFoldInputsCost s t band a b+70*(n+1)*(V+1)+71
    have hhalf : (n+1)/2 ≤ n := by omega
    have hpar : n/2+((n+1)/2-n/2) = (n+1)/2 := by omega
    have hprod := Nat.mul_le_mul_right V hhalf
    rw [hpar]
    nlinarith only [hm₁,hm₃,hhalf,hprod]
  · simp only [S₂,Function.update_self,houtlen,h1len,hsum,List.length_cons,List.length_nil]
  · apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h0 : k = 0 <;> by_cases h1' : k = 1 <;> by_cases h2 : k = 2 <;>
      by_cases h3 : k = 3 <;> by_cases h6 : k = 6 <;> by_cases h109' : k = 109 <;>
      simp [S₄,S₃,S₂,S₁,movedR,h0,h1',h2,h3,h6,h109',output,V,n,
        hblank 0 (by decide),hblank 1 (by decide),hblank 2 (by decide),
        hblank 3 (by decide),hblank 6 (by decide),Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
