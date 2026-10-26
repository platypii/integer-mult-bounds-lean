module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowCall
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCouplingOperands

/-! Execute a prepared row, then consume its owned operand prefixes and count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def consumedIntegerRow (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (integerRowCall hQ) retireCouplingOperands

theorem consumedIntegerRow_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {L q w : ℕ} (hw : 1 ≤ w) (hqw : q ≤ w) (xs as : List GaussianInt) (rhs : GaussianInt)
    (hxlen : xs.length = L) (halen : as.length = L)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A+4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hx : S.R 110 = cstream A w xs++tailX) (ha : S.R 111 = cstream A w as++tailA)
    (hrhs : S.R 112 = csyms A w rhs++tailR) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w q)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) (h109 : S.R 109 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ L*(rmulCost w+61*w+32)+14*w+76 ∧
      Exec body (consumedIntegerRow hQ) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          113 (csyms A w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)++S.R 113))
          110 tailX) 111 tailA) 102 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := fixedPointRowCall_exec (body := body) hQ hA hw hqw xs as rhs
    hxlen halen hxs has v S tailX tailA tailR hL hwR hx ha hrhs hc hready hwork
  let z := rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 113 (csyms A w z++S.R 113)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := retireCouplingOperands_exec (body := body) L w
    (cstream A w xs) (cstream A w as) tailX tailA v₁ S₁
    (by simpa [S₁] using hL) (by simpa [S₁] using hwR)
    (by simpa [S₁] using hx) (by simpa [S₁] using ha)
    (by simp [hxlen]) (by simp [halen]) (by simpa [S₁] using h109)
    (by simpa [S₁] using hwork 104 (by simp [integerRowWork]))
    (by simpa [S₁] using hwork 105 (by simp [integerRowWork]))
    (by simpa [S₁] using hwork 106 (by simp [integerRowWork]))
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
