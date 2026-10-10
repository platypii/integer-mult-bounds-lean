import IntegerMultBounds.Machine.CompactComplexScalarWireEmit
import IntegerMultBounds.Machine.RawLinearCombinationComplexFamily

/-! A complete actual complex25 sparse row block executes all named wire
expressions on real and imaginary components. Original controls are retained,
one shared arithmetic bank is blank afterward, and every output record has
the common advanced denominator, including physically doubled spectators. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarRowBlock
noncomputable section
open CompactComplexScalarIntegerRows
open CompactComplexScalarWireEmit (expressionAt word)
open RadixLinearCombinationRefresh (Size)
open ButterflySigned
open Networks.GaussianPrecision
attribute [local irreducible] Networks.ComplexRank25.program gates gate wireIndex

abbrev wireCount := Fintype.card Wire
def expressions (r : RowIndex) (i : Fin wireCount) := expressionAt r (wireIndex.symm i)
def scratch (r : RowIndex) := 2+Size (expression r)

private theorem plus_two (k : ℕ) : k≤2+k ∧ 2≤2+k := by omega

theorem scratch_fits (r : RowIndex) (i : Fin wireCount) : Size (expressions r i)≤scratch r := by
  dsimp only [expressions]
  by_cases hi : wireIndex.symm i=(gate r).target
  · simp only [expressionAt,ite_eq_left hi,scratch]
    exact (plus_two _).1
  · simp only [expressionAt,ite_eq_right hi,Size,RadixLinearCombinationRefresh.Expr.erase,
      RadixLinearCombination.TapeCount,RadixLinearCombination.AuxTapes]
    exact (plus_two _).2

theorem wires_pos : 0<wireCount := by
  have i := wireIndex (Sum.inl (Networks.ComplexRank25.triples 0,
    Networks.ComplexRank25.triples 0,Networks.ComplexRank25.triples 0))
  exact Nat.zero_lt_of_lt i.isLt

private theorem scale_allowance (T w : ℕ) :
    12*w+42≤(T+1)*(12*w+42) := by nlinarith

theorem expression_cost (r : RowIndex) (i : Fin wireCount) (w : ℕ) :
    RawLinearCombination.cost (expressions r i) w≤(termTotal+1)*(12*w+42) := by
  dsimp only [expressions]
  by_cases hi : wireIndex.symm i=(gate r).target
  · simp only [expressionAt,ite_eq_left hi]
    exact uniform_time_bound r w
  · simp only [expressionAt,ite_eq_right hi]
    have h := RawLinearCombination.cost_le
      (RadixLinearCombinationRefresh.Expr.term (wireIndex (wireIndex.symm i)) 2) w
    simp only [RadixLinearCombinationRefresh.leaves,one_mul] at h
    exact h.trans (scale_allowance termTotal w)

private opaque budgetWireCount : {k : ℕ // k=wireCount} := ⟨wireCount,rfl⟩

@[irreducible] def timeConstant := 2*budgetWireCount.val*(42*(termTotal+1)+8)+1

private theorem affine_budget (c T w : ℕ) :
    2*(c*((T+1)*(12*w+42)+2*w+8))+1≤(2*c*(42*(T+1)+8)+1)*(w+1) := by
  have he : (2*c*(42*(T+1)+8)+1)*(w+1)=
      (2*(c*((T+1)*(12*w+42)+2*w+8))+1)+(60*c*(T+1)+12*c+1)*w := by ring
  rw [he]
  exact Nat.le_add_right _ _

theorem time_bound (r : RowIndex) (w : ℕ) :
    2*RawLinearCombinationFieldFamily.cost (expressions r) (List.finRange wireCount) w+1≤
      timeConstant*(w+1) := by
  have h := RawLinearCombinationFieldFamily.cost_le (expressions r) (List.finRange wireCount)
    w ((termTotal+1)*(12*w+42)) (fun i _ => expression_cost r i w)
  rw [List.length_finRange] at h
  conv at h => rhs; rw [←budgetWireCount.property]
  have hm := Nat.add_le_add_right (Nat.mul_le_mul_left 2 h) 1
  delta timeConstant
  exact hm.trans (affine_budget budgetWireCount.val termTotal w)

def program (r : RowIndex) :=
  RawLinearCombinationComplexFamily.program (q:=2) wires_pos (expressions r) (scratch_fits r)

def bank (r : RowIndex) (xs ys : ℕ → List (Fin 2)) (fs : Fin wireCount → ℤ → Fin 6)
    (ps : Fin wireCount → ℤ) :=
  RawLinearCombinationComplexFamily.bank (S:=scratch r) xs ys fs ps

def records (r : RowIndex) (xs ys : ℕ → List (Fin 2)) (i : Fin wireCount) :=
  DelimitedRadixRecord.complex (word r (wireIndex.symm i) xs) (word r (wireIndex.symm i) ys)

def output (r : RowIndex) (xs ys : ℕ → List (Fin 2)) (fs : Fin wireCount → ℤ → Fin 6)
    (ps : Fin wireCount → ℤ) :=
  RawLinearCombinationComplexFamily.output (S:=scratch r) (expressions r) xs ys fs ps

/-- One fixed row machine processes the exact finite original wire order and
all actual integer coefficients. Its result is a literal Gaussian role bank. -/
theorem runs (r : RowIndex) (xs ys : ℕ → List (Fin 2)) (w : ℕ)
    (hx : ∀ j,(xs j).length=w) (hy : ∀ j,(ys j).length=w)
    (fs : Fin wireCount → ℤ → Fin 6) (ps : Fin wireCount → ℤ) :
    HoareTime (program r) (fun v => v=bank r xs ys fs ps)
      (fun v => v=output r xs ys fs ps)
      (2*RawLinearCombinationFieldFamily.cost (expressions r) (List.finRange wireCount) w+1) :=
  RawLinearCombinationComplexFamily.runs _ _ _ _ _ _ hx hy _ _

theorem output_records (r : RowIndex) (xs ys : ℕ → List (Fin 2))
    (fs : Fin wireCount → ℤ → Fin 6) (ps : Fin wireCount → ℤ) :
    output r xs ys fs ps=
      bank r xs ys (fun i => putWord (fs i) (ps i) (records r xs ys i))
        (fun i => ps i+(word r (wireIndex.symm i) xs).length+(word r (wireIndex.symm i) ys).length+2) := rfl

/-- Common stored width is unchanged, while common dyadic precision increases
by exactly one. Both real and imaginary output numerators are actual words. -/
theorem output_semantics (r : RowIndex) (b p n : ℕ) (xs ys : ℕ → List (Fin 2))
    (hx : ∀ j,(xs j).length=b+1) (hy : ∀ j,(ys j).length=b+1)
    (ha : ∀ j,|signedRows b xs j|≤((2^p:ℕ):ℤ))
    (hb : ∀ j,|signedRows b ys j|≤((2^p:ℕ):ℤ)) (hguard : p+guardBits≤b)
    (i : Fin wireCount) :
    complexValue (signedValue b (word r (wireIndex.symm i) xs))
      (signedValue b (word r (wireIndex.symm i) ys)) (n+1)=
      (Networks.RationalScalarGrid.castGate (gate r)).run
        (fun j => complexValue (signedRows b xs j) (signedRows b ys j) n) (wireIndex.symm i) ∧
      (records r xs ys i).length=2*((b+1)+1) := by
  constructor
  · exact CompactComplexScalarWireEmit.complex_word r _ b p n xs ys hx hy ha hb hguard
  · exact DelimitedRadixRecord.complex_length _ _ _
      (CompactComplexScalarWireEmit.word_length r _ xs _ hx)
      (CompactComplexScalarWireEmit.word_length r _ ys _ hy)

end
end IntegerMultBounds.Machine.CompactComplexScalarRowBlock
