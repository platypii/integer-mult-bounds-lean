module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSupportRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientAccuracy

/-! Apply the restoring row arithmetic to the generated coefficient words.
The target is the original masked coupling, with every periodic alias retained. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem offsetCouplingRow_spec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {s t p u q w rhsExp inputExp countExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hs : 0 < s) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ w)
    (T : Finset (ZMod s)) (x : ZMod s → ℝ) (i : ZMod s)
    (input : ℤ → GaussianInt) (rhs : GaussianInt) (b K ε rhsError : ℝ) (hε : 0 ≤ ε)
    (hcount : 2*PhaseCellBand.width p u+1 ≤ 2^countExp)
    (hrhsBound : ‖value q rhs‖ ≤ (2 : ℝ)^rhsExp)
    (hinput : ∀ δ ∈ (couplingOffsets (PhaseCellBand.width p u)).reverse,
      ‖value q (input δ)‖ ≤ (2 : ℝ)^inputExp)
    (hxError : ∀ δ ∈ (couplingOffsets (PhaseCellBand.width p u)).reverse,
      |(value q (input δ)).re-(if i+(δ : ZMod s) ∈ T then x (i+(δ : ZMod s)) else 0)| ≤ ε)
    (hmass : (((couplingOffsets (PhaseCellBand.width p u)).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u) i.val (i.val+δ) : ℝ)|)).sum ≤ K)
    (hrhsError : |(value q rhs).re-b| ≤ rhsError)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : (S.R 102).length = 2*PhaseCellBand.width p u+1) (hwR : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w (((couplingOffsets (PhaseCellBand.width p u)).reverse).map input)++tailX)
    (ha : S.R 111 = cstream A w (couplingCoefficientWords (2^15*p) q s t u
      (PhaseCellBand.width p u) i.val)++tailA)
    (hrhs : S.R 112 = csyms A w rhs++tailR) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w q) (hwork : ∀ k ∈ integerRowWork, S.R k = []) :
    let entries := (couplingOffsets (PhaseCellBand.width p u)).reverse
    let coeff := fun δ => rationalWord q (PhaseCellCrossCell.entry (2^15*p) s t u
      (PhaseCellBand.width p u) i.val (i.val+δ))
    let z := rhs-(entries.map (fun δ => tdivN q (input δ*coeff δ))).sum
    ∃ v' m, v'.user = v.user ∧
      m ≤ (2*PhaseCellBand.width p u+1)*(rmulCost w+43*w+21)+14*w+55 ∧
      Exec body (integerRowCall hQ) (mk v S) m
        (mk v' {S with R := Function.update S.R 113 (csyms A w z++S.R 113)}) ∧
      |(value q (decodeWord ((csyms A w z++S.R 113).take w))).re-
        (b-SchurDominance.couple (realMatrix s t p u) T x i)| ≤
          (2*PhaseCellBand.width p u+1)*(2/(2 : ℝ)^q)+rhsError+
            (2*PhaseCellBand.width p u+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  dsimp only
  let band := PhaseCellBand.width p u
  let entries := (couplingOffsets band).reverse
  let a := fun δ : ℤ => (PhaseCellCrossCell.entry (2^15*p) s t u band i.val (i.val+δ) : ℝ)
  let coeff := fun δ : ℤ => rationalWord q (PhaseCellCrossCell.entry (2^15*p) s t u band i.val (i.val+δ))
  let y := fun δ : ℤ => if i+(δ : ZMod s) ∈ T then x (i+(δ : ZMod s)) else 0
  have hlen : entries.length = 2*band+1 := by simp [entries]
  have hcouple : (entries.map (fun δ => y δ*a δ)).sum =
      SchurDominance.couple (realMatrix s t p u) T x i := by
    have hh := (couple_eq_offsetList (t := t) p u T x i).symm
    simpa only [entries,band,a,y,List.map_reverse,List.sum_reverse,ite_mul,zero_mul,mul_comm] using hh
  obtain ⟨v',m,hu,hm,he,herror⟩ := couplingSupportRow_spec (body := body) hQ hA
    entries input coeff rhs a y b K (1/(2 : ℝ)^q) ε rhsError hε hw
    (by simpa [hlen] using hcount) hrhsBound hinput
    (by intro δ _
        exact ⟨selected_coefficient_norm _ _ hp hs hst hαu hθ hgap hbudget,rfl⟩)
    (by intro δ _; exact rationalWord_error q _) hxError hmass hrhsError
    v S tailX tailA tailR (by simpa [hlen] using hL) hwR hx
    (by simpa only [entries,coeff,couplingCoefficientWords] using ha) hrhs hc hready hwork
  refine ⟨v',m,hu,by simpa only [hlen] using hm,he,?_⟩
  simpa only [hcouple,hlen,band,entries,coeff,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
