module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginalColumnInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginalColumnPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseColumnSources

/-! Generate, compute and release an original-matrix column from ordinary coupling headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def generatedOriginalColumn (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq originalColumnInputs (.seq (borrowedCouplingPass hQ true) releaseColumnSources)

def generatedOriginalColumnCost (p q w s t u a b : ℕ) : ℕ :=
  originalColumnInputsCost s w q+
    (borrowedCouplingPassCost true (2^15*p) q w s t u (PhaseCellBand.width p u) a b+releaseColumnSourcesCost s w)

theorem generatedOriginalColumn_spec (hQ : SS.states ≤ Q)
    {p q w s t u a b : ℕ} [NeZero s] {α d : ℝ}
    (hA : 96 ≤ A) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)+2 ≤ w)
    (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (j : ZMod s) (hj : j ∈ haloBoundary s t (PhaseCellBand.width p u) a b)
    (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady (2^15*p) q w s t u (PhaseCellBand.width p u) a b tail (embStk groupReg S))
    (hcoordinate : (S.R 136).length = j.val) (hindex : S.R 107 = [])
    (h143 : S.R 143 = []) (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = [])
    (h137 : S.R 137 = []) (h138 : S.R 138 = []) :
    let band := PhaseCellBand.width p u
    let column := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
    let output := cstream A w (chirpLine s column)++tail
    let S' : Stacks 144 A := {S with R := Function.update S.R 110 output}
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedOriginalColumnCost p q w s t u a b ∧
      Exec (embTab groupReg body) (generatedOriginalColumn hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (column i).im = 0) ∧
      (∀ i, ‖value q (column i)‖ ≤ 2+3*(2*band+1)*(1/(2 : ℝ)^q)) ∧
      (∀ i, |publishedCellRead q w (0 : ZMod s) (S'.R 110) i-realMatrix s t p u i j| ≤
        3*(2*band+1)*(1/(2 : ℝ)^q)) ∧
      CouplingReady (2^15*p) q w s t u band a b output (embStk groupReg S') := by
  dsimp only
  let band := PhaseCellBand.width p u
  let column := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
  let rhs := cstream A w (chirpLine s (fun _ => 0))++tail
  let basis := cstream A w (chirpLine s (negativeUnitField q j))++S.R 132
  let result := cstream A w (chirpLine s column)
  have hs : (S.R 97).length = s := hready.axis
  have hwS : (S.R 94).length = w := hready.width
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hready₁⟩ := originalColumnInputs_exec (body := body) (by omega : q ≤ w)
    j tail v S hready hcoordinate h131 h134 h135 h137
  let S₁ : Stacks 144 A := {S with R := Function.update (Function.update S.R 110 rhs) 132 basis}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂,hnorm,hreal,hnorm',herror⟩ := originalColumnPass_spec (body := body)
    hQ hA hp hwidth hα hst hαu hθ hgap hbudget hw haS hbS hbandS j hj tail (S.R 132) v₁ S₁ hready₁
    (by simpa [S₁] using hindex) (by simp [S₁,basis]) (by simpa [S₁] using h143)
    (by simpa [S₁] using h131) (by simpa [S₁] using h134) (by simpa [S₁] using h135)
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 113 (result++S.R 113)}
  have he₂' : Exec (embTab groupReg body) (borrowedCouplingPass hQ true) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,result,column,band] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := releaseColumnSources_exec (body := embTab groupReg body) s w
    (cstream A w (chirpLine s (fun _ => 0))) (cstream A w (chirpLine s (negativeUnitField q j)))
    result tail (S.R 132) (S.R 113) (by simp) (by simp) (by simp [result]) v₂ S₂
    (by simpa [S₂,S₁] using hs) (by simpa [S₂,S₁] using hwS)
    (by simp [S₂,S₁,rhs]) (by simp [S₂,S₁,basis]) (by simp [S₂])
    (by simpa [S₂,S₁] using h131) (by simpa [S₂,S₁] using h134) (by simpa [S₂,S₁] using h135)
    (by simpa [S₂,S₁] using h137) (by simpa [S₂,S₁] using h138)
  let S₃ : Stacks 144 A := {S₂ with R := (Function.update (Function.update (Function.update S₂.R
    110 (result++tail)) 132 (S.R 132)) 113 (S.R 113))}
  let Sfinal : Stacks 144 A := {S with R := Function.update S.R 110 (result++tail)}
  have hframe : S₃ = Sfinal := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> by_cases h132 : k = 132 <;> by_cases h113 : k = 113 <;>
      simp [S₃,S₂,S₁,Sfinal,h110,h132,h113]
  have he₃' : Exec (embTab groupReg body) releaseColumnSources (mk v₂ S₂) m₃ (mk v₃ S₃) := he₃
  rw [hframe] at he₃'
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),Nat.add_le_add hm₁ (Nat.add_le_add hm₂ hm₃),
    Exec.seq he₁ (Exec.seq he₂' he₃'),hreal,hnorm',?_,?_⟩
  · intro i
    have hfit (k : ZMod s) : Fits w (column k) := fits_of_value_power hw _ (hnorm k)
    have hw0 : 0 < w := by omega
    change |publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s column)++tail) i-
      realMatrix s t p u i j| ≤ 3*(2*band+1)*(1/(2 : ℝ)^q)
    rw [publishedCellRead_encodedField (by omega) hw0 column tail hfit i]
    have hh := herror i
    have hh' : |publishedCellRead q w (0 : ZMod s) (result++S.R 113) i-realMatrix s t p u i j| ≤
        3*(2*band+1)*(1/(2 : ℝ)^q) := by simpa [S₁,result,column,band] using hh
    rw [publishedCellRead_encodedField (by omega) hw0 column (S.R 113) hfit i] at hh'
    exact hh'
  · apply hready.of_source_frame (S' := embStk groupReg Sfinal) (raw' := result++tail)
      (by simp [Sfinal,embStk,groupReg]) rfl
    intro k _ _ _ h110
    have hne : groupReg k ≠ (110 : Fin 144) := by simpa [groupReg,Fin.ext_iff] using h110
    simp [Sfinal,embStk,Function.comp_def,hne]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
