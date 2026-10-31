module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizationHeaderStock

/-! The ordinary-input interior chain carries shared numerical reserves and
linear native data traffic through normalization and final counter retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

private theorem canonical_cr_fresh (q l w M L : ℕ) (X V : ℕ → List GaussianInt)
    (tail tailX : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) (r : CR) :
    (Fixed.startWithTails q l w M L L X V tail tailX [] inp out).R (ScalarPlacement.cr r) = [] := by
  have hr := (ScalarPlacement.cr_range r).2.1
  have h110 : (ScalarPlacement.cr r).val ≠ 110 := by omega
  have h111 : (ScalarPlacement.cr r).val ≠ 111 := by omega
  simpa [Fixed.startWithTails,Fixed.inputBankWithTails,Fixed.start,h110,h111] using
    ScalarPlacement.cr_fresh q l w M L X V tail inp out r

theorem closedInputInterior_exec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q l w M L cExp e j : ℕ} (hquarter : q = 4 * (cExp + e + 1)) (hw : q + (cExp + e + 1) + 4 ≤ w)
    (hq : cExp + e + 1 + j + 1 ≤ q) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z C : ℕ → List GaussianInt) (D : ℕ → List ℚ)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenC : ∀ n < M, (C n).length = L) (hlenD : ∀ n < M, (D n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hC : ∀ n < M, ∀ z ∈ C n, ‖value q z‖ ≤ (2 : ℝ) ^ cExp)
    (hD : ∀ n < M, ∀ a ∈ D n, 1 / (2 : ℝ) ^ e ≤ (a : ℝ))
    (a : GaussianInt) (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock ScalarPlacement.cr
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) ScalarPlacement.mul
        ScalarPlacement.mul_injective (by decide) hQ ScalarPlacement.cr)) ≤ K) (depth : ℕ) :
    let V := fun n => weightedInputNumerators q cExp e (C n) (D n)
    let tailX := csyms A w a ++ borrowed
    let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail tailX [] inp out
    let SF := { S with R := (Function.update S.R 93
      (cstream A w ((branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ (22 * (cExp + e + 1) + 10) + inputStageCost q cExp e w M L + interiorProductsCost q l w M L + ScalarPlacement.releaseWeightCountersCost q w ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (inputSourceBank q l w M L 0 X Z ((List.range M).flatMap C)
          (reciprocalWeightWords q ((List.range M).flatMap D)) tail (csyms A w a++borrowed) inp out))+depth+
          normalizedInteriorWorkspace R K q l w M L cExp e) depth (closedInputInterior hR hQ)
        (mk v (inputSourceBank q l w M L 0 X Z ((List.range M).flatMap C)
          (reciprocalWeightWords q ((List.range M).flatMap D)) tail tailX inp out)) m (mk v' SF) ∧
      ∀ i : Fin (M * L),
        ‖value q (decodeWord (((SF.R 93).drop (i.val * w)).take w)) -
          (value q (pairNumerator q l M L X V i) - value q (pairNumerator q l M L Z V i)) * value q a‖ ≤
            2 / (2 : ℝ) ^ q := by
  dsimp only
  obtain ⟨vf,nf,huf,hnf,hef,herrf⟩ := closedInputInterior_exec (body := body)
    hR hQ hA hquarter hw hq hpad X Z C D hlenX hlenZ hlenC hlenD hX hZ hC hD a ha har
    v tail borrowed inp out
  let V := fun n => weightedInputNumerators q cExp e (C n) (D n)
  let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V)
    tail (csyms A w a ++ borrowed) [] inp out
  let result := cstream A w ((branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))) ++ tail
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, herr⟩ := inputInteriorFromPrecision_exec_within (body := body)
    hR hQ hA hquarter hw hq hpad X Z C D hlenX hlenZ hlenC hlenD hX hZ hC hD a ha har
    v tail borrowed inp out R K hpushR hpushK depth
  obtain ⟨v₂, hu₂, he₂⟩ := ScalarPlacement.releaseWeightCounters_exec (body := body)
    q w v₁ S result (fun r _ => canonical_cr_fresh q l w (M+M) L
      (rowBank M X Z) (rowBank M V V) tail (csyms A w a++borrowed) inp out r)
  have ht₂ := mn_native_exec_within he₂ 0 ScalarPlacement.releaseWeightCounters_native
    depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add he₁ ht₂
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  refine ⟨vf,nf,huf,hnf,ht.mono ?_,herrf⟩
  intro d z hz
  simp only [Nat.zero_mul,Nat.add_zero] at hz
  exact hz

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
