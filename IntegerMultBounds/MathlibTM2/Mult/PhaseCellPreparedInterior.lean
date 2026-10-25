module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedGenerators
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInteriorProducts

/-! # Interior execution with constructed inverse-generator words

The input bank contains the computable encoded setup, rather than arbitrary
generators and a scalar with range hypotheses. This composes its numerical
constructor with the existing execution theorem. Producing that bank on tape
and paying its setup cost remain separate obligations.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.ToeplitzInverse

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

/-- All four products, merge and scalar arithmetic execute on the constructed
setup data. Their range and reality conditions follow from the constructors. -/
theorem preparedInterior_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {precision s t u band q l w M L j : ℕ} (hprecision : 13 ≤ precision)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L) (hq : j + 2 ≤ q)
    (hw : q + 4 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (V : ℕ → List GaussianInt) (hlenV : ∀ n < M, (V n).length = L)
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let X : ℕ → List GaussianInt := fun _ => columnWords precision s t u band L q (j + 2)
    let Z : ℕ → List GaussianInt := fun _ => reversedColumnWords precision s t u band L q (j + 2)
    let a := reciprocalWord precision s t u band L q (j + 2)
    let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V)
      tail (csyms A w a ++ borrowed) [] inp out
    let SF := { S with R := (Function.update (ScalarPlacement.counterR q w S.R) 93
      (cstream A w ((branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ interiorProductsCost q l w M L ∧
      Exec body (interiorProducts hR hQ)
        (mk v (singleBranchInputWithXTail q l w M L X Z V tail (csyms A w a ++ borrowed) inp out)) m
        (mk v' SF) ∧
      (∀ i : Fin (M * L),
        ‖value q (decodeWord (((SF.R 93).drop (i.val * w)).take w)) -
          (value q (pairNumerator q l M L X V i) - value q (pairNumerator q l M L Z V i)) * value q a‖ ≤
          2 / (2 : ℝ) ^ q) ∧
      (∀ i < L, |2 * (value q (block (X 0) i)).re -
        col (natInv L (IntegerMultBounds.NLogN.PhaseCellToeplitz.coeff precision s t u band)) i| ≤
          1 / (2 : ℝ) ^ j) ∧
      (∀ i < L, |2 * (value q (block (Z 0) i)).re -
        rev L (natInv L (IntegerMultBounds.NLogN.PhaseCellToeplitz.coeff precision s t u band)) i| ≤
          1 / (2 : ℝ) ^ j) ∧
      |(value q a).re -
        1 / natInv L (IntegerMultBounds.NLogN.PhaseCellToeplitz.coeff precision s t u band) 0 0| ≤
          1 / (2 : ℝ) ^ j := by
  dsimp only
  obtain ⟨v', m, huser, hcost, he, herr⟩ := interiorProducts_exec (body := body)
    (q := q) (l := l) (w := w) (M := M) (L := L) hR hQ hA (by omega) hw hpad
    (fun _ => columnWords precision s t u band L q (j + 2))
    (fun _ => reversedColumnWords precision s t u band L q (j + 2)) V
    (by intro n hn; simp) (by intro n hn; simp) hlenV
    (fun _ _ => columnWords_disk hprecision hs hst hu (by omega) (by omega))
    (fun _ _ => reversedColumnWords_disk hprecision hs hst hu (by omega) (by omega)) hV
    (reciprocalWord precision s t u band L q (j + 2))
    (reciprocalWord_norm hprecision hs hst hu hL (by omega)) rfl v tail borrowed inp out
  refine ⟨v', m, huser, hcost, he, herr, ?_, ?_, ?_⟩
  · exact columnWords_error_precision hprecision hs hst hu hq
  · exact reversedColumnWords_error_precision hprecision hs hst hu hq
  · exact reciprocalWord_error_precision hprecision hs hst hu hq hL

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
