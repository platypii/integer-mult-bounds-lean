module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowsStock

/-! The numerical generator row jobs instantiate the shared row-scan resource theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem integerGeneratorStep_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L n w : ℕ} (hW : P * (n + 1) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A + 4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hcount : (S.R 103).length = L) (hsaved : S.R 108 = [])
    (hx : S.R 110 = cstream A w (rowColumnWords P s t u band L n) ++ tailX)
    (ha : S.R 111 = cstream A w ((generatorRowJobs P s t u band L n).flatMap Prod.fst) ++ tailA)
    (hr : S.R 112 = cstream A w ((generatorRowJobs P s t u band L n).map Prod.snd) ++ tailR)
    (hc : CClean mul S) (hready : Ready (fun r => S.R (cr r)) w 0)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ L * (integerRowCost L w + 5) + 4 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(3*L+consumeIntegerRowWorkspace C L w+2))
        depth (integerRows hQ) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R 111 tailA) 112 tailR)
          113 (cstream A w (rowColumnWords P s t u band L (n + 1)) ++ S.R 113)) })) ∧
      ∀ i < L, Fits w (⟨(columnNumerators P s t u band L (n + 1)).getD i 0, 0⟩ : GaussianInt) := by
  have hcolW : P * n + 3 ≤ w := by nlinarith
  have hcoefW : P + 2 ≤ w := by nlinarith
  have hctx : IntegerRowContext L w (rowColumnWords P s t u band L n) tailX S := by
    refine ⟨by nlinarith, by simp [rowColumnWords], ?_, hL, hwR, hx, hc, hready, hwork⟩
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact columnNumerator_fits hcolW hP hs hst hu hn k (List.mem_range.mp hk)
  obtain ⟨v', m, hv, hm, he⟩ := integerRows_exec_within (body := body) hQ hA C hpush
    (rowColumnWords P s t u band L n) (generatorRowJobs P s t u band L n) v S tailX tailA tailR hctx
    (generatorRowJobs_fits hcoefW hP) (by simpa using hcount) hsaved ha hr
  refine ⟨v', m, hv, by simpa using hm, ?_, ?_⟩
  · simpa only [generatorRowJobs_results, generatorRowJobs_length] using he
  · intro i hi
    exact columnNumerator_fits hW hP hs hst hu (by omega) i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
