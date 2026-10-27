module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedOriginalColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSchurColumnResult
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginalColumnBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseSchurColumnReady

/-! Generate a computed Schur column with allocated entry accuracy and full source release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def generatedSchurColumn (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 148 Q A U :=
  .seq (retainedOriginalColumn hQ) (.seq (releasedSchurResidual hR hQ) releaseSchurColumnInput)

def generatedSchurColumnCost (p u l s t a b target j : ℕ) : ℕ :=
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  restoredOriginalColumnCost p q s t u a b j+
    (releasedSchurResidualCost p l s t u target 2 a b+releaseSchurColumnInputCost q s)

theorem generatedSchurColumn_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (j : ZMod s) (hj : j ∈ haloBoundary s t (PhaseCellBand.width p u) a b)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail : List (Fin (A+4)))
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg S))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hcoordinate : (S.R 139).length = j.val)
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) :
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
    ∃ v' m, ∃ D : ZMod s → GaussianInt,
      let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
      let output := cstream A w (chirpLine s C)++tail
      let S' : Stacks 148 A := {S with R := Function.update S.R 110 output}
      v'.user = v.user ∧ m ≤ generatedSchurColumnCost p u l s t a b target j.val ∧
      Exec (embTab componentReg (embTab groupReg body)) (generatedSchurColumn hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ haloBoundary s t band a b,
        |publishedCellRead q w (0 : ZMod s) (S'.R 110) i-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^target) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u band 0 0 output (embStk componentReg S') := by
  dsimp only
  let firstTarget := initialSchurTarget p u target 2
  let q := executionPrecision p l firstTarget 2
  let w := executionWidth p l firstTarget 2
  let band := PhaseCellBand.width p u
  let B := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
  let δ : ℝ := 3*(2*band+1)*(1/(2 : ℝ)^q)
  have hwq : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hwcol : q+couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)+2 ≤ 2*q+8 := by
    have hh := originalColumn_width p u l firstTarget 2
    simpa only [← hwq] using hh
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hBreal,hBnorm,hBerror,hready₁⟩ := retainedOriginalColumn_spec (body := body)
    hQ hA hp hwidth hα hst hαu hθ hgap hbudget hwcol has hbs hband j hj tail v S hready
    haMaster hbMaster hcoordinate h143 h138
  let inputB := cstream A w (chirpLine s B)++tail
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 110 inputB}
  have he₁' : Exec (embTab componentReg (embTab groupReg body)) (retainedOriginalColumn hQ)
      (mk v S) m₁ (mk v₁ S₁) := by simpa only [← hwq] using he₁
  have hready₁' : LengthKeyReady (2^15*p) (executionStagePrecision p l firstTarget 2+1)
      q l s t u band 0 0 inputB (embStk componentReg S₁) := by
    simpa only [← hwq] using hready₁
  have hB (i : ZMod s) : ‖value q (B i)‖ ≤ (2 : ℝ)^2 :=
    (hBnorm i).trans (originalColumn_magnitude_budget p u l target 2)
  have hBfit (i : ZMod s) : Fits w (B i) := fits_of_value_power
    (by dsimp [w,q,executionWidth,executionPrecision]; omega) _ (hB i)
  have hcolumn : ∀ k ∈ haloVertices s a b, |(value q (B k)).re-realMatrix s t p u k j| ≤ δ := by
    intro k _
    have hh : |publishedCellRead q w (0 : ZMod s) (cstream A w (chirpLine s B)++tail) k-
        realMatrix s t p u k j| ≤ δ := by
      simpa [S₁,← hwq,δ,B,band,q,firstTarget] using hBerror k
    rw [publishedCellRead_encodedField (by omega) (by dsimp [w,executionWidth]; omega) B tail hBfit k] at hh
    exact hh
  obtain ⟨v₂,m₂,D,R,hRsolve,hu₂,hm₂,he₂,hCreal,hCnorm,hCerror,hentry,hread,hready₂⟩ := releasedSchurColumn_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad B hB v₁ S₁ tail
    (by simpa [S₁] using h127) (by simpa [S₁] using h138) (by simpa [S₁] using h143)
    (by simpa [S₁] using haMaster) (by simpa [S₁] using hbMaster) hready₁'
    (by simpa [S₁] using h147) j hj δ (by dsimp [δ]; positivity) hcolumn
  let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let result := cstream A w (chirpLine s C)
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 110 (result++inputB)}
  have he₂' : Exec (embTab componentReg (embTab groupReg body)) (releasedSchurResidual hR hQ)
      (mk v₁ S₁) m₂ (mk v₂ S₂) := by simpa [S₂,S₁,inputB,result,C,q,w,band,firstTarget] using he₂
  have hready₂' : LengthKeyReady (2^15*p) (executionStagePrecision p l firstTarget 2+1)
      q l s t u band 0 0 (result++(cstream A w (chirpLine s B)++tail)) (embStk componentReg S₂) := by
    simpa [S₂,S₁,inputB,result,C,q,w,band,firstTarget] using hready₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃,hready₃⟩ := releaseSchurColumnInput_ready (body := embTab groupReg body) (q := q)
    result (cstream A w (chirpLine s B)) tail (by simp [result,hwq]) (by simp [hwq]) v₂ S₂ hready₂'
    (by simpa [S₂,S₁] using h138) (by simpa [S₂,S₁] using h147)
  let S₃ : Stacks 148 A := {S₂ with R := Function.update S₂.R 110 (result++tail)}
  let Sfinal : Stacks 148 A := {S with R := Function.update S.R 110 (result++tail)}
  have hframe : S₃ = Sfinal := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h110 : k = 110 <;> simp [S₃,S₂,S₁,Sfinal,h110]
  have he₃' : Exec (embTab componentReg (embTab groupReg body)) releaseSchurColumnInput
      (mk v₂ S₂) m₃ (mk v₃ S₃) := he₃
  rw [hframe] at he₃'
  have hready₃' : LengthKeyReady (2^15*p) (executionStagePrecision p l firstTarget 2+1)
      q l s t u band 0 0 (result++tail) (embStk componentReg S₃) := hready₃
  rw [hframe] at hready₃'
  refine ⟨v₃,m₁+(m₂+m₃),D,hu₃.trans (hu₂.trans hu₁),Nat.add_le_add hm₁ (Nat.add_le_add hm₂ hm₃),
    Exec.seq he₁' (Exec.seq he₂' he₃'),hCreal,hCnorm,?_,hready₃'⟩
  intro i hi
  have htail : publishedCellRead q w (0 : ZMod s) (result++tail) i =
      publishedCellRead q w (0 : ZMod s) (result++inputB) i := by
    simp only [publishedCellRead,ZMod.val_zero,Nat.sub_zero]
    rw [cstream_word w (chirpLine s C) tail i.val (by simpa using i.val_lt),
      cstream_word w (chirpLine s C) inputB i.val (by simpa using i.val_lt)]
  have hh : |publishedCellRead q w (0 : ZMod s) (result++inputB) i-
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b) (haloInterior s t band a b).toList).1 i j| ≤
      (1/(2 : ℝ)^(recoveryTarget p target+2))/(8*(p : ℝ))+(1+16*(p : ℝ))*δ := by
    simpa [S₂,S₁,inputB,result,C,B,q,w,band,firstTarget] using hentry i hi
  change |publishedCellRead q w (0 : ZMod s) (result++tail) i-_| ≤ _
  rw [htail]
  exact hh.trans (originalColumn_schur_budget p u l target 2 (by omega))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
