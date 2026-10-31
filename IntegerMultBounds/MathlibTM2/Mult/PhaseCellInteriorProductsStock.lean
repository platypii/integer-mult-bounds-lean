module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInteriorProducts
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergedBranchesStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarCanonicalStock

/-! Four triangular products, branch merge, generated scalar readiness and
actual scalar application share numerical reserves plus linear batch traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

private theorem fetchScalar_native :
    mnNativePushBound 3 (fetchScalar (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [fetchScalar,unaryProduct,copyAfterPrefix,copyPrefix,copyR,copyStep,transfer,transferAct,
    clearWords,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

def interiorWorkspace (R C q l w M L : ℕ) : ℕ :=
  18*(M*L*w)+18+compactPairWorkspace R q l w (M+M) L+3*fixedMergeCost w M L+
    3*fetchScalarCost (M+M) L w+ScalarPlacement.applyWorkspace C q M L w

theorem interiorProducts_exec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 4 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (a : GaussianInt) (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (R C : ℕ)
    (hpushR : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushC : mnProgPush (cmulBlock ScalarPlacement.cr
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) ScalarPlacement.mul
        ScalarPlacement.mul_injective (by decide) hQ ScalarPlacement.cr)) ≤ C) (depth : ℕ) :
    let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V)
      tail (csyms A w a ++ borrowed) [] inp out
    let SF := { S with R := (Function.update (ScalarPlacement.counterR q w S.R) 93
      (cstream A w ((branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ interiorProductsCost q l w M L ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (singleBranchInputWithXTail q l w M L X Z V tail (csyms A w a++borrowed) inp out))+
          depth+interiorWorkspace R C q l w M L) depth (interiorProducts hR hQ)
        (mk v (singleBranchInputWithXTail q l w M L X Z V tail (csyms A w a ++ borrowed) inp out)) m
        (mk v' SF) ∧
      ∀ i : Fin (M * L),
        ‖value q (decodeWord (((SF.R 93).drop (i.val * w)).take w)) -
          (value q (pairNumerator q l M L X V i) - value q (pairNumerator q l M L Z V i)) * value q a‖ ≤
          2 / (2 : ℝ) ^ q := by
  dsimp only
  obtain ⟨vf,nf,huf,hnf,hef,herr⟩ := interiorProducts_exec (body := body) hR hQ hA
    hq hw hpad X Z V hlenX hlenZ hlenV hX hZ hV a ha har v tail borrowed inp out
  let ds := branchDifference q l M L X Z V
  let scalarTail := csyms A w a ++ borrowed
  let XB := rowBank M X Z
  let VB := rowBank M V V
  let S₀ := Fixed.startWithTails q l w (M + M) L L XB VB tail scalarTail [] inp out
  let SP := ScalarPlacement.scalarInputWithXTail q l w M L XB VB ds a tail scalarTail inp out
  let SD : Stacks 117 A := { SP with R := (Function.update (ScalarPlacement.counterR q w SP.R) 93
    (cstream A w (ds.map (fun x => tdivN q (x * a))) ++ tail)) }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := mergedBranches_with_x_tail_exec_within (body := body) (q := q) (l := l) (w := w) (M := M) (L := L)
    hR hA hq (by omega) hpad X Z V hlenX hlenZ hlenV hX hZ hV v tail scalarTail inp out R hpushR depth
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := fetchCanonical_exec (body := body)
    q l w (M + M) L XB VB (rowBank_length X Z hlenX hlenZ) a v₁ (cstream A w ds ++ tail) borrowed inp out
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃, _⟩ := ScalarPlacement.applyCanonical_with_x_tail_exec_within (body := body) (q := q) (l := l) (w := w) (M := M) (L := L)
    hQ hA hq hw XB VB ds a (by simp [ds, branchDifference])
    (branchDifference_norm hpad X Z V hlenX hlenZ hlenV hX hZ hV) ha har v₂ tail scalarTail inp out C hpushC depth
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body 96 v₃ SD
  have ht₂ := mn_native_exec_within he₂ 3 fetchScalar_native depth
    (mnSize (mk v₁ (Fixed.startWithTails q l w (M+M) L L XB VB
      (cstream A w ds++tail) scalarTail [] inp out))+depth+3*fetchScalarCost (M+M) L w)
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm₂) _)
  have ht₄ := mn_native_exec_within he₄ 0
    (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add he₁ (mn_seq_within_add ht₂ (mn_seq_within_add he₃ ht₄))
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  refine ⟨vf,nf,huf,hnf,ht.mono ?_,herr⟩
  intro d z hz
  simp only [Nat.zero_mul,Nat.add_zero] at hz
  dsimp only [scalarTail] at hz
  dsimp only [interiorWorkspace]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
