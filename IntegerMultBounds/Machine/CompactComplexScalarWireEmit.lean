import IntegerMultBounds.Machine.CompactComplexScalarIntegerRows
import IntegerMultBounds.Machine.RawLinearCombinationComplexEmit
import IntegerMultBounds.Machine.CompactNativeRoleHeaders

/-! Actual complex25 scalar-row output expressions, in the original named wire
ordering. The target executes its literal integer sparse expression; every
other stored wire executes an actual doubling kernel, so the common dyadic
denominator advances once on all real and imaginary output fields. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarWireEmit
noncomputable section
open CompactComplexScalarIntegerRows
open ButterflySigned
open Networks.GaussianPrecision
attribute [local irreducible] Networks.ComplexRank25.program gates gate wireIndex

def expressionAt (r : RowIndex) (i : Wire) :
    RadixLinearCombinationRefresh.Expr (Fintype.card Wire) :=
  if i=(gate r).target then expression r else .term (wireIndex i) 2

def word (r : RowIndex) (i : Wire) (xs : ℕ → List (Fin 2)) :=
  RadixLinearCombination.result (expressionAt r i).erase xs

def program (r : RowIndex) (i : Wire) := RawLinearCombinationComplexEmit.program (q:=2) (expressionAt r i)
def input (r : RowIndex) (i : Wire) (xs ys : ℕ → List (Fin 2)) (f : ℤ → Fin 6) (p : ℤ) :=
  RawLinearCombinationComplexEmit.bank (expressionAt r i) xs ys f p
def output (r : RowIndex) (i : Wire) (xs ys : ℕ → List (Fin 2)) (f : ℤ → Fin 6) (p : ℤ) :=
  RawLinearCombinationComplexEmit.output (expressionAt r i) xs ys f p

theorem word_length (r : RowIndex) (i : Wire) (xs : ℕ → List (Fin 2)) (w : ℕ)
    (hw : ∀ j,(xs j).length=w) : (word r i xs).length=w :=
  RawLinearCombination.result_length _ _ _ hw

theorem signed_word (r : RowIndex) (i : Wire) (b p : ℕ) (xs : ℕ → List (Fin 2))
    (hw : ∀ j,(xs j).length=b+1) (ha : ∀ j,|signedRows b xs j|≤((2^p:ℕ):ℤ))
    (hguard : p+guardBits≤b) :
    signedValue b (word r i xs)=numeratorAction r (signedRows b xs) i := by
  by_cases hi : i=(gate r).target
  · subst i
    simpa only [word,expressionAt,ite_true,resultWord] using uniform_result_signed r b p xs hw ha hguard
  · have hv : RadixLinearCombination.Valid (q:=2) (.term (wireIndex i).val 2) := by
      norm_num [RadixLinearCombination.Valid,Swap.Modular.ratMod]
    have hr := RawLinearCombination.result_value (.term (wireIndex i) 2) hv xs (b+1) hw
    have hs : (RadixDigits.value (word r i xs):ZMod (2^(b+1)))=
        (numeratorAction r (signedRows b xs) i:ZMod (2^(b+1))) := by
      simpa [word,expressionAt,ite_eq_right hi,RadixLinearCombinationRefresh.Expr.erase,
        RadixLinearCombination.valueMod,numeratorAction,integerAction,ite_eq_right hi,Int.cast_mul,
        Int.cast_ofNat,signedRows,signed_cast,Swap.Modular.ratMod] using hr
    have hg := uniform_numerator_guard r (signedRows b xs) p ha i
    have hpow : ((2^(p+guardBits):ℕ):ℤ)≤((2^b:ℕ):ℤ) := by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) hguard
    have hbound := abs_lt.mp (hg.trans_le hpow)
    exact signed_unique b _ (word_length r i xs (b+1) hw) _ (by constructor <;> linarith) hs

theorem complex_word (r : RowIndex) (i : Wire) (b p n : ℕ) (xs ys : ℕ → List (Fin 2))
    (hx : ∀ j,(xs j).length=b+1) (hy : ∀ j,(ys j).length=b+1)
    (ha : ∀ j,|signedRows b xs j|≤((2^p:ℕ):ℤ))
    (hb : ∀ j,|signedRows b ys j|≤((2^p:ℕ):ℤ)) (hguard : p+guardBits≤b) :
    complexValue (signedValue b (word r i xs)) (signedValue b (word r i ys)) (n+1)=
      (Networks.RationalScalarGrid.castGate (gate r)).run
        (fun j => complexValue (signedRows b xs j) (signedRows b ys j) n) i := by
  rw [signed_word r i b p xs hx ha hguard,signed_word r i b p ys hy hb hguard]
  exact (row_semantics r _ _ n i).symm

/-- The physical compiler emits the actual real field followed by the actual
imaginary field, retaining every original control and blanking both workspaces. -/
theorem runs (r : RowIndex) (i : Wire) (xs ys : ℕ → List (Fin 2)) (w : ℕ)
    (hx : ∀ j,(xs j).length=w) (hy : ∀ j,(ys j).length=w) (f : ℤ → Fin 6) (p : ℤ) :
    HoareTime (program r i) (fun v => v=input r i xs ys f p)
      (fun v => v=output r i xs ys f p)
      (2*RawLinearCombination.cost (expressionAt r i) w+4*w+15) :=
  RawLinearCombinationComplexEmit.runs _ _ _ _ hx hy _ _

/-- The guard refers to the genuine native stored record width. -/
theorem native_complex_word (r : RowIndex) (i : Wire) (s : CompactGadgetReservationShape.Shape)
    (p n : ℕ) (xs ys : ℕ → List (Fin 2))
    (hx : ∀ j,(xs j).length=CompactNativeRoleHeaders.recordWidth s p)
    (hy : ∀ j,(ys j).length=CompactNativeRoleHeaders.recordWidth s p)
    (ha : ∀ j,|signedRows (ButterflyGuard.halfWidth p s.bits) xs j|≤((2^p:ℕ):ℤ))
    (hb : ∀ j,|signedRows (ButterflyGuard.halfWidth p s.bits) ys j|≤((2^p:ℕ):ℤ))
    (hg : guardBits≤2*s.bits+3) :
    complexValue (signedValue (ButterflyGuard.halfWidth p s.bits) (word r i xs))
      (signedValue (ButterflyGuard.halfWidth p s.bits) (word r i ys)) (n+1)=
      (Networks.RationalScalarGrid.castGate (gate r)).run
        (fun j => complexValue (signedRows (ButterflyGuard.halfWidth p s.bits) xs j)
          (signedRows (ButterflyGuard.halfWidth p s.bits) ys j) n) i := by
  apply complex_word r i _ p n xs ys
  · simpa only [CompactNativeRoleHeaders.recordWidth,ButterflyGuard.width] using hx
  · simpa only [CompactNativeRoleHeaders.recordWidth,ButterflyGuard.width] using hy
  · exact ha
  · exact hb
  · unfold ButterflyGuard.halfWidth
    omega

end
end IntegerMultBounds.Machine.CompactComplexScalarWireEmit
