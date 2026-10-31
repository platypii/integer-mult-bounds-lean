module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizationHeader
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputInteriorStock

/-! The ordinary-input interior chain carries shared numerical reserves and
linear native data traffic through normalization and final counter retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

private theorem prepareNormalization_native :
    mnNativePushBound 3 (prepareNormalization (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [prepareNormalization,quarterCount,halfCount,halfPairAct,moveR,moveStep,whileR,peekR,
    uclear,drainR,popDo,mnNativePushBound,mnActPush]

def normalizedInteriorWorkspace (R K q l w M L cExp e : ℕ) : ℕ :=
  3*(22*(cExp+e+1)+10)+inputInteriorWorkspace R K q l w M L cExp e

theorem inputInteriorFromPrecision_exec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    let SF := { S with R := (Function.update (ScalarPlacement.counterR q w S.R) 93
      (cstream A w ((branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ (22 * (cExp + e + 1) + 10) + inputStageCost q cExp e w M L + interiorProductsCost q l w M L ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (inputSourceBank q l w M L 0 X Z ((List.range M).flatMap C)
          (reciprocalWeightWords q ((List.range M).flatMap D)) tail tailX inp out))+depth+
          normalizedInteriorWorkspace R K q l w M L cExp e) depth (inputInteriorFromPrecision hR hQ)
        (mk v (inputSourceBank q l w M L 0 X Z ((List.range M).flatMap C)
          (reciprocalWeightWords q ((List.range M).flatMap D)) tail tailX inp out)) m (mk v' SF) ∧
      ∀ i : Fin (M * L),
        ‖value q (decodeWord (((SF.R 93).drop (i.val * w)).take w)) -
          (value q (pairNumerator q l M L X V i) - value q (pairNumerator q l M L Z V i)) * value q a‖ ≤
            2 / (2 : ℝ) ^ q := by
  dsimp only
  let source := (List.range M).flatMap C
  let factors := reciprocalWeightWords q ((List.range M).flatMap D)
  let tailX := csyms A w a ++ borrowed
  let S := inputSourceBank q l w M L 0 X Z source factors tail tailX inp out
  obtain ⟨v₁, hu₁, he₁⟩ := prepareNormalization_exec (body := body) (cExp + e + 1) v S
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank, hquarter])
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputSourceBank, singleBranchInputWithXTail, Fixed.startWithTails,
      Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank])
    (by simp [S, inputSourceBank])
  have he₁' : Exec body prepareNormalization (mk v S) (22 * (cExp + e + 1) + 10)
      (mk v₁ (inputSourceBank q l w M L (cExp + e + 1) X Z source factors tail tailX inp out)) := by
    refine he₁.cast rfl ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = (116 : Fin 117)
    · subst k; simp [S, inputSourceBank]
    · simp [S, inputSourceBank, Function.update_apply, hk]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, herr⟩ := inputInterior_exec_within (body := body)
    (q := q) (l := l) (w := w) (M := M) (L := L) (cExp := cExp) (e := e) (j := j)
    hR hQ hA hw hq hpad X Z C D hlenX hlenZ hlenC hlenD hX hZ hC hD a ha har v₁ tail borrowed inp out R K hpushR hpushK depth
  have ht₁ := mn_native_exec_within he₁' 3 prepareNormalization_native depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add ht₁ he₂
  exact ⟨v₂,(22*(cExp+e+1)+10)+m₂,hu₂.trans hu₁,by omega,ht,herr⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
