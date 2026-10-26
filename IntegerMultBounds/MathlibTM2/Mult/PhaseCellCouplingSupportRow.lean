module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowPerturb

/-! An executed coupling row indexed by its advertised support. The result
includes RHS, coefficient and computed-input errors explicitly; no identity
with a scalar-rounding reference implementation is assumed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem couplingSupportRow_spec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {ι : Type*} (entries : List ι) (input coeff : ι → GaussianInt) (rhs : GaussianInt)
    (a y : ι → ℝ) (b K δ ε rhsError : ℝ) (hε : 0 ≤ ε)
    {q w rhsExp inputExp coeffExp countExp : ℕ}
    (hw : q+couplingRowExponent rhsExp inputExp coeffExp countExp+2 ≤ w)
    (hcount : entries.length ≤ 2^countExp) (hrhsBound : ‖value q rhs‖ ≤ (2 : ℝ)^rhsExp)
    (hinput : ∀ j ∈ entries, ‖value q (input j)‖ ≤ (2 : ℝ)^inputExp)
    (hcoeff : ∀ j ∈ entries, ‖value q (coeff j)‖ ≤ (2 : ℝ)^coeffExp ∧ (coeff j).im = 0)
    (haError : ∀ j ∈ entries, |(value q (coeff j)).re-a j| ≤ δ)
    (hxError : ∀ j ∈ entries, |(value q (input j)).re-y j| ≤ ε)
    (hmass : (entries.map (fun j => |a j|)).sum ≤ K)
    (hrhsError : |(value q rhs).re-b| ≤ rhsError)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : (S.R 102).length = entries.length) (hwR : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w (entries.map input)++tailX)
    (ha : S.R 111 = cstream A w (entries.map coeff)++tailA)
    (hrhs : S.R 112 = csyms A w rhs++tailR) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w q) (hwork : ∀ k ∈ integerRowWork, S.R k = []) :
    let z := rhs-(entries.map (fun j => tdivN q (input j*coeff j))).sum
    ∃ v' m, v'.user = v.user ∧ m ≤ entries.length*(rmulCost w+43*w+21)+14*w+55 ∧
      Exec body (integerRowCall hQ) (mk v S) m
        (mk v' {S with R := Function.update S.R 113 (csyms A w z++S.R 113)}) ∧
      |(value q (decodeWord ((csyms A w z++S.R 113).take w))).re-
        (b-(entries.map (fun j => y j*a j)).sum)| ≤
          entries.length*(2/(2 : ℝ)^q)+rhsError+
            entries.length*((2 : ℝ)^inputExp*δ)+K*ε := by
  dsimp only
  obtain ⟨v',m,hu,hm,he,hrow⟩ := couplingRowCall_spec (body := body) hQ hA hw
    (entries.map input) (entries.map coeff) rhs (by simp) (by simp) hcount hrhsBound
    (by intro x hx; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx; exact hinput j hj)
    (by intro c hc; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hc; exact hcoeff j hj)
    v S tailX tailA tailR hL hwR hx ha hrhs hc hready hwork
  rw [supportRow_zipWith] at he hrow
  rw [supportRow_zipWith] at hrow
  refine ⟨v',m,hu,hm,he,?_⟩
  apply coupling_residual_perturb entries a (fun j => (value q (coeff j)).re)
    (fun j => (value q (input j)).re) y (value q rhs).re b _ ((2 : ℝ)^inputExp)
    δ ε K _ rhsError (by positivity) hε
  · intro j hj
    exact (Complex.abs_re_le_norm _).trans (hinput j hj)
  · exact haError
  · exact hxError
  · exact hmass
  · exact hrow
  · exact hrhsError

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
