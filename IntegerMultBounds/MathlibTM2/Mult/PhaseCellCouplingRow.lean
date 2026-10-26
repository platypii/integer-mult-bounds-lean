module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowCall
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowFits

/-! A restoring fixed-point residual/recovery row call with a decoded error and
word fits derived from magnitudes. Coefficient generation and row selection
are separate; the arithmetic operates on their computed operands. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem couplingRowCall_spec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L q w rhsExp inputExp coeffExp countExp : ℕ}
    (hw : q+couplingRowExponent rhsExp inputExp coeffExp countExp+2 ≤ w)
    (xs as : List GaussianInt) (rhs : GaussianInt) (hxlen : xs.length = L) (halen : as.length = L)
    (hcount : L ≤ 2^countExp) (hrhsBound : ‖value q rhs‖ ≤ (2 : ℝ)^rhsExp)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ)^inputExp)
    (has : ∀ a ∈ as, ‖value q a‖ ≤ (2 : ℝ)^coeffExp ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w xs++tailX) (ha : S.R 111 = cstream A w as++tailA)
    (hrhs : S.R 112 = csyms A w rhs++tailR) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w q)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) :
    let z := rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum
    ∃ v' m, v'.user = v.user ∧ m ≤ L*(rmulCost w+43*w+21)+14*w+55 ∧
      Exec body (integerRowCall hQ) (mk v S) m
        (mk v' {S with R := Function.update S.R 113 (csyms A w z++S.R 113)}) ∧
      |(value q (decodeWord ((csyms A w z++S.R 113).take w))).re-
        ((value q rhs).re-(List.zipWith (fun x a => (value q x).re*(value q a).re) xs as).sum)| ≤
          L*(2/(2 : ℝ)^q) := by
  dsimp only
  have hwpos : 1 ≤ w := by dsimp [couplingRowExponent] at hw; omega
  have hqw : q ≤ w := by omega
  have hinput : q+inputExp+2 ≤ w := by dsimp [couplingRowExponent] at hw; omega
  have hcoeff : q+coeffExp+2 ≤ w := by dsimp [couplingRowExponent] at hw; omega
  obtain ⟨v',m,hu,hm,he⟩ := fixedPointRowCall_exec (body := body) hQ hA hwpos hqw xs as rhs hxlen halen
    (fun x hx => fits_of_value_power hinput x (hxs x hx))
    (fun a ha => ⟨fits_of_value_power hcoeff a (has a ha).1,(has a ha).2⟩)
    v S tailX tailA tailR hL hwR hx ha hrhs hc hready hwork
  refine ⟨v',m,hu,hm,he,?_⟩
  let z := rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum
  have hfit : Fits w z := fixedPointRow_fits hw rhs xs as (hxlen.trans halen.symm)
    (by omega) hrhsBound hxs (fun a ha => (has a ha).1)
  have hword : (csyms A w z++S.R 113).take w = csyms A w z := by
    have hlen : (csyms A w z).length = w := by simp [csyms]
    simp only [List.take_append,hlen,Nat.sub_self,List.take_zero,List.append_nil]
    simpa only [hlen] using (show (csyms A w z).take (csyms A w z).length = csyms A w z from List.take_length)
  rw [hword,decodeWord_of_fits (by omega) hwpos z hfit]
  simpa only [hxlen] using fixedPointRow_error q rhs xs as (hxlen.trans halen.symm)
    (fun a ha => (has a ha).2)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
