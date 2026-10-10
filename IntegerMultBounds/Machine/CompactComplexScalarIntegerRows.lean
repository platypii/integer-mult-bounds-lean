import IntegerMultBounds.Machine.CompactFramedScalarGrid
import IntegerMultBounds.Machine.CompactComplexScalarGrid
import IntegerMultBounds.Machine.RawLinearCombination
import Mathlib.Data.Rat.Floor

/-! Concrete integer numerator rows of the actual grouped complex25 scalar
modules. Their original sparse term order and wire names are retained. One
common factor2 clears every coefficient denominator; real and imaginary
numerators therefore use the same fixed binary expression compiler. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarIntegerRows
noncomputable section
attribute [local irreducible] Networks.ComplexRank25.program
open Networks
open GaussianPrecision
open ButterflySigned
abbrev Wire := ComplexFramedExecution.Wire
abbrev GroupIndex := Fin ComplexRank25.program.length

def gates (g : GroupIndex) := GroupedCircuit.compile (CompactFramedScalarGrid.vertex g).group
abbrev RowIndex := (g : GroupIndex) × Fin (gates g).length

def gate (r : RowIndex) : Circuit.Gate Wire ℚ := (gates r.1)[r.2.val]

def numerator (c : ℚ) : ℤ := ⌊2*c⌋

/-- The numerator is explicitly computed from the rational coefficient, not
selected from an existential grid witness. -/
theorem numerator_spec {c : ℚ} (hc : BoundedGrid 1 52 (c:ℂ)) :
    (numerator c : ℚ)=2*c ∧ |numerator c|≤52 := by
  obtain ⟨a,b,he,ha,_⟩ := hc
  have hr := congrArg Complex.re he
  norm_num at hr
  have hq : 2*c=(a:ℚ) := by exact_mod_cast (by linarith : (2:ℝ)*(c:ℝ)=(a:ℝ))
  have hn : numerator c=a := by simp only [numerator,hq,Int.floor_intCast]
  exact ⟨by rw [hn]; exact hq.symm,by simpa [hn] using ha⟩

theorem coefficients (r : RowIndex) (t : Wire × ℚ) (ht : t ∈ (gate r).terms) :
    BoundedGrid 1 52 (t.2:ℂ) := by
  have hc := GroupedCoefficients.compile CompactFramedScalarGrid.coeffGood
    (CompactFramedScalarGrid.vertex r.1).group
    (CompactFramedScalarGrid.group_coefficients _ (by
      apply List.mem_map.mpr
      exact ⟨CompactFramedScalarGrid.vertex r.1,
        by exact List.getElem_mem r.1.isLt,rfl⟩))
  exact hc (gate r) (List.getElem_mem r.2.isLt) t ht

def integerTerms {ι : Type*} (g : Circuit.Gate ι ℚ) : List (ι × ℤ) :=
  g.terms.map (fun t => (t.1,numerator t.2))

def terms (r : RowIndex) : List (Wire × ℤ) := integerTerms (gate r)

theorem term_length (r : RowIndex) : (terms r).length=(gate r).terms.length := by
  simp only [terms,integerTerms,List.length_map]
theorem term_wires (r : RowIndex) : (terms r).map Prod.fst=(gate r).terms.map Prod.fst := by
  simp only [terms,integerTerms,List.map_map,Function.comp_def]

theorem term_bound (r : RowIndex) (t : Wire × ℤ) (ht : t ∈ terms r) : |t.2|≤52 := by
  obtain ⟨t0,ht0,rfl⟩ := List.mem_map.mp ht
  exact (numerator_spec (coefficients r t0 ht0)).2

/-- Exactly the finite wire ordering used by ComplexRank25.wires. -/
def wireIndex : Wire ≃ Fin (Fintype.card Wire) := Fintype.equivFin Wire

theorem wire_order : List.ofFn wireIndex.symm=ComplexRank25.wires := rfl

def expressionAux (target : Wire) : List (Wire × ℤ) → RadixLinearCombinationRefresh.Expr (Fintype.card Wire)
  | [] => .term (wireIndex target) 2
  | t::ts => .add (.term (wireIndex t.1) (t.2:ℚ)) (expressionAux target ts)
def expression (r : RowIndex) := expressionAux (gate r).target (terms r)

private theorem valid_aux (target : Wire) (ts : List (Wire × ℤ)) :
    RadixLinearCombination.Valid (q:=2) (expressionAux target ts).erase := by
  induction ts with
  | nil => norm_num [expressionAux,RadixLinearCombinationRefresh.Expr.erase,RadixLinearCombination.Valid]
  | cons t ts ih =>
    simp only [expressionAux,RadixLinearCombinationRefresh.Expr.erase,RadixLinearCombination.Valid]
    exact ⟨by simp,ih⟩

theorem valid (r : RowIndex) : RadixLinearCombination.Valid (q:=2) (expression r).erase :=
  valid_aux _ _

private theorem leaves_aux (target : Wire) (ts : List (Wire × ℤ)) :
    RadixLinearCombinationRefresh.leaves (expressionAux target ts)=ts.length+1 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [expressionAux,RadixLinearCombinationRefresh.leaves,List.length_cons,ih]; omega

theorem expression_leaves (r : RowIndex) :
    RadixLinearCombinationRefresh.leaves (expression r)=(gate r).terms.length+1 := by
  rw [expression,leaves_aux,term_length]

/-- Every actual numerator row is a fixed physical binary arithmetic program,
retaining all input words and erasing every private source copy afterward. -/
theorem runs (r : RowIndex) (xs : ℕ → List (Fin 2)) (b : ℕ) (hw : ∀ i,(xs i).length=b) :
    HoareTime (RawLinearCombination.program (q:=2) (expression r))
      (fun v => v=RawLinearCombination.input (expression r) xs)
      (fun v => v=RawLinearCombination.output (expression r) xs)
      (RawLinearCombination.cost (expression r) b) := RawLinearCombination.runs _ _ _ hw

theorem time_bound (r : RowIndex) (b : ℕ) :
    RawLinearCombination.cost (expression r) b≤((gate r).terms.length+1)*(12*b+42) := by
  simpa only [expression_leaves] using RawLinearCombination.cost_le (expression r) b


attribute [local irreducible] gates gate wireIndex

/-- Both Gaussian components use the identical actual integer row. Every
untouched wire is explicitly rescaled when the common exponent advances. -/
def integerAction {ι : Type*} [DecidableEq ι] (g : Circuit.Gate ι ℚ) (a : ι → ℤ) (i : ι) : ℤ :=
  if i=g.target then 2*a i+((integerTerms g).map (fun t => t.2*a t.1)).sum else 2*a i

def numeratorAction (r : RowIndex) (a : Wire → ℤ) (i : Wire) := integerAction (gate r) a i

private theorem sum_semantics {ι : Type*} (g : Circuit.Gate ι ℚ) (a b : ι → ℤ) (n : ℕ)
    (hc : ∀ t ∈ g.terms,BoundedGrid 1 52 (t.2:ℂ)) :
    ((g.terms.map (fun t => (t.2:ℂ)*complexValue (a t.1) (b t.1) n)).sum)*(2:ℂ)^(n+1)=
      ((((integerTerms g).map (fun t => t.2*a t.1)).sum:ℤ):ℂ)+
        ((((integerTerms g).map (fun t => t.2*b t.1)).sum:ℤ):ℂ)*Complex.I := by
  have h (ts : List (ι × ℚ)) (hc : ∀ t ∈ ts,BoundedGrid 1 52 (t.2:ℂ)) :
      ((ts.map (fun t => (t.2:ℂ)*complexValue (a t.1) (b t.1) n)).sum)*(2:ℂ)^(n+1)=
        (((ts.map (fun t => numerator t.2*a t.1)).sum:ℤ):ℂ)+
          (((ts.map (fun t => numerator t.2*b t.1)).sum:ℤ):ℂ)*Complex.I := by
    induction ts with
    | nil => simp
    | cons t ts ih =>
      have hn : (numerator t.2:ℂ)=2*(t.2:ℂ) := by exact_mod_cast (numerator_spec (hc t (by simp))).1
      have ht := ih (fun t ht => hc t (by simp [ht]))
      simp only [List.map_cons,List.sum_cons,add_mul,ht,Int.cast_add,Int.cast_mul]
      have hp : (2:ℂ)^n≠0 := pow_ne_zero _ (by norm_num)
      simp only [complexValue,pow_succ]
      rw [hn]
      field_simp
      ring
  simpa only [integerTerms,List.map_map,Function.comp_def] using h g.terms hc

private theorem value_scale (a b : ℤ) (n : ℕ) :
    complexValue a b n*(2:ℂ)^(n+1)=2*((a:ℂ)+(b:ℂ)*Complex.I) := by
  have hp : (2:ℂ)^n≠0 := pow_ne_zero _ (by norm_num)
  rw [complexValue,pow_succ,←mul_assoc,div_mul_cancel₀ _ hp]
  ring

private theorem value_double (a b : ℤ) (n : ℕ) :
    complexValue a b n=complexValue (2*a) (2*b) (n+1) := by
  unfold complexValue
  apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2:ℂ)≠0))).2
  rw [←complexValue,value_scale]
  push_cast
  ring

/-- Exact dyadic semantics of each physical numerator expression: no rational
coefficient conversion, row ordering, or Gaussian-grid callback is assumed. -/
private theorem generic_row_semantics {ι : Type*} [DecidableEq ι] (g : Circuit.Gate ι ℚ)
    (hc : ∀ t ∈ g.terms,BoundedGrid 1 52 (t.2:ℂ)) (a b : ι → ℤ) (n : ℕ) (i : ι) :
    (RationalScalarGrid.castGate g).run (fun j => complexValue (a j) (b j) n) i=
      complexValue (integerAction g a i) (integerAction g b i) (n+1) := by
  have hp' : (2:ℂ)^(n+1)≠0 := pow_ne_zero _ (by norm_num)
  by_cases hi : i=g.target
  · subst i
    unfold Circuit.Gate.run RationalScalarGrid.castGate
    rw [Function.update_self]
    simp only [List.map_map,Function.comp_def]
    apply (eq_div_iff hp').2
    have hs := sum_semantics g a b n hc
    simp only [integerAction,ite_true,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
    rw [add_mul,hs,value_scale]
    simp only [mul_add,add_mul,mul_assoc]
    exact add_add_add_comm _ _ _ _
  · simp only [Circuit.Gate.run,RationalScalarGrid.castGate,Function.update_of_ne hi,
      integerAction,hi,ite_false]
    exact value_double (a i) (b i) n

theorem row_semantics (r : RowIndex) (a b : Wire → ℤ) (n : ℕ) (i : Wire) :
    (RationalScalarGrid.castGate (gate r)).run (fun j => complexValue (a j) (b j) n) i=
      complexValue (numeratorAction r a i) (numeratorAction r b i) (n+1) :=
  generic_row_semantics (gate r) (coefficients r) a b n i

private theorem sum_abs_bound (ts : List (Wire × ℤ)) (a : Wire → ℤ) (M : ℕ)
    (ha : ∀ i,|a i|≤(M:ℤ)) (ht : ∀ t ∈ ts,|t.2|≤52) :
    |(ts.map (fun t => t.2*a t.1)).sum|≤((ts.length*52*M:ℕ):ℤ) := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have hsum := abs_add_le (t.2*a t.1) ((ts.map (fun t => t.2*a t.1)).sum)
    have hm := mul_le_mul (ht t (by simp)) (ha t.1) (abs_nonneg _) (by norm_num : (0:ℤ)≤52)
    have htail := ih (fun t ht0 => ht t (by simp [ht0]))
    push_cast at htail
    simp only [List.map_cons,List.sum_cons,abs_mul] at hsum ⊢
    push_cast
    simp only [List.length_cons]
    push_cast
    nlinarith

/-- A concrete finite numerator growth factor for this actual row. -/
def rowGrowth (r : RowIndex) := 2+(gate r).terms.length*52

theorem numerator_bound (r : RowIndex) (a : Wire → ℤ) (M : ℕ)
    (ha : ∀ i,|a i|≤(M:ℤ)) (i : Wire) :
    |numeratorAction r a i|≤((rowGrowth r*M:ℕ):ℤ) := by
  have ht := sum_abs_bound (terms r) a M ha (term_bound r)
  rw [term_length] at ht
  push_cast at ht
  dsimp only [terms] at ht
  have htwo : |2*a i|≤2*(M:ℤ) := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (ha i) (by norm_num : (0:ℤ)≤2)
  unfold numeratorAction integerAction
  split_ifs
  · have hs := abs_add_le (2*a i) ((terms r).map (fun t => t.2*a t.1)).sum
    dsimp only [terms] at hs
    unfold rowGrowth
    push_cast
    nlinarith
  · unfold rowGrowth
    push_cast
    nlinarith

/-- This actual scalar row advances the denominator exactly once and fits a
fixed extra signed-word guard, independent of input size and inherited depth. -/
def guardIncrement (r : RowIndex) := Nat.clog 2 (rowGrowth r+1)

theorem numerator_guard (r : RowIndex) (a : Wire → ℤ) (p : ℕ)
    (ha : ∀ i,|a i|≤((2^p:ℕ):ℤ)) (i : Wire) :
    |numeratorAction r a i|<((2^(p+guardIncrement r):ℕ):ℤ) := by
  have hm := numerator_bound r a (2^p) ha i
  have hg : rowGrowth r+1≤2^(guardIncrement r) := Nat.le_pow_clog (by decide) _
  have hg' : rowGrowth r<2^(guardIncrement r) := by omega
  have hh := Nat.mul_lt_mul_of_pos_right hg' (by positivity : 0<2^p)
  rw [Nat.mul_comm,←pow_add] at hh
  exact hm.trans_lt (by exact_mod_cast (by simpa only [Nat.mul_comm,Nat.add_comm] using hh))


/-- Literal centered numerators of the physical binary control words. -/
def signedRows (b : ℕ) (xs : ℕ → List (Fin 2)) (i : Wire) :=
  signedValue b (xs (wireIndex i).val)

def resultWord (r : RowIndex) (xs : ℕ → List (Fin 2)) :=
  RadixLinearCombination.result (expression r).erase xs

private theorem ratMod_integer (m : ℕ) (a : ℤ) :
    Swap.Modular.ratMod m (a:ℚ)=(a:ZMod m) := by
  simp [Swap.Modular.ratMod]

private theorem expression_value_aux (target : Wire) (ts : List (Wire × ℤ))
    (b : ℕ) (xs : ℕ → List (Fin 2)) :
    RadixLinearCombination.valueMod (b+1) (expressionAux target ts).erase xs=
      ((2*signedRows b xs target+(ts.map (fun t => t.2*signedRows b xs t.1)).sum:ℤ):ZMod (2^(b+1))) := by
  induction ts with
  | nil =>
    simp only [expressionAux,RadixLinearCombinationRefresh.Expr.erase,RadixLinearCombination.valueMod,
      List.map_nil,List.sum_nil,add_zero,Int.cast_mul,Int.cast_ofNat]
    have htwo : Swap.Modular.ratMod (2^(b+1)) 2=(2:ZMod (2^(b+1))) :=
      by simpa using ratMod_integer (2^(b+1)) 2
    rw [htwo]
    exact congrArg (fun z : ZMod (2^(b+1)) => 2*z) (signed_cast b _).symm
  | cons t ts ih =>
    simp only [expressionAux,RadixLinearCombinationRefresh.Expr.erase,RadixLinearCombination.valueMod,
      List.map_cons,List.sum_cons,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
    rw [ratMod_integer,ih]
    push_cast
    unfold signedRows
    simp_rw [signed_cast]
    exact add_left_comm _ _ _

theorem result_residue (r : RowIndex) (b : ℕ) (xs : ℕ → List (Fin 2))
    (hw : ∀ i,(xs i).length=b+1) :
    (RadixDigits.value (resultWord r xs):ZMod (2^(b+1)))=
      (numeratorAction r (signedRows b xs) (gate r).target:ZMod (2^(b+1))) := by
  rw [resultWord,RawLinearCombination.result_value (expression r) (valid r) xs (b+1) hw]
  simpa only [expression,numeratorAction,integerAction,terms,ite_true] using expression_value_aux (gate r).target (terms r) b xs

/-- Word guard converts the actual radix machine's residue into the literal
integer numerator. The only guard hypothesis concerns input word magnitudes. -/
theorem result_signed (r : RowIndex) (b p : ℕ) (xs : ℕ → List (Fin 2))
    (hw : ∀ i,(xs i).length=b+1)
    (ha : ∀ i,|signedRows b xs i|≤((2^p:ℕ):ℤ)) (hb : p+guardIncrement r≤b) :
    signedValue b (resultWord r xs)=numeratorAction r (signedRows b xs) (gate r).target := by
  have hg := numerator_guard r (signedRows b xs) p ha (gate r).target
  have hpow : ((2^(p+guardIncrement r):ℕ):ℤ)≤((2^b:ℕ):ℤ) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) hb
  have hs := (abs_lt.mp (hg.trans_le hpow))
  apply signed_unique b _ (RawLinearCombination.result_length (expression r) xs (b+1) hw) _
    (by constructor <;> linarith) (result_residue r b xs hw)

/-- Both actual physical result words implement exactly the original rational
Gaussian row at denominator exponent n+1, with inherited numerator guards. -/
theorem result_complex (r : RowIndex) (b p n : ℕ) (xs ys : ℕ → List (Fin 2))
    (hx : ∀ i,(xs i).length=b+1) (hy : ∀ i,(ys i).length=b+1)
    (ha : ∀ i,|signedRows b xs i|≤((2^p:ℕ):ℤ))
    (hb : ∀ i,|signedRows b ys i|≤((2^p:ℕ):ℤ)) (hguard : p+guardIncrement r≤b) :
    complexValue (signedValue b (resultWord r xs)) (signedValue b (resultWord r ys)) (n+1)=
      (RationalScalarGrid.castGate (gate r)).run
        (fun i => complexValue (signedRows b xs i) (signedRows b ys i) n) (gate r).target := by
  rw [result_signed r b p xs hx ha hguard,result_signed r b p ys hy hb hguard]
  exact (row_semantics r _ _ n (gate r).target).symm


/-- Each row index is an actual listed sparse scalar row of the full network. -/
theorem gate_mem (r : RowIndex) : gate r ∈ ComplexFramedExecution.rows := by
  have hrow : gate r ∈ GroupedCircuit.compile (CompactFramedScalarGrid.vertex r.1).group := by
    simpa only [gate,gates] using (List.getElem_mem r.2.isLt)
  unfold ComplexFramedExecution.rows GroupedCircuit.compileGroups
  apply List.mem_flatMap.mpr
  refine ⟨(CompactFramedScalarGrid.vertex r.1).group,?_,hrow⟩
  apply List.mem_map.mpr
  exact ⟨CompactFramedScalarGrid.vertex r.1,List.getElem_mem r.1.isLt,rfl⟩

/-- Literal finite data determine one allowance for all scalar modules. These
constants are independent of integer length, recursion exponent, and row count. -/
private opaque termTotalData :
    {k : ℕ // k=(ComplexFramedExecution.rows.map (fun g => g.terms.length)).sum} :=
  ⟨(ComplexFramedExecution.rows.map (fun g => g.terms.length)).sum,rfl⟩

@[irreducible] def termTotal := termTotalData.val

theorem termTotal_literal :
    termTotal=(ComplexFramedExecution.rows.map (fun g => g.terms.length)).sum := by
  delta termTotal
  exact termTotalData.property
@[irreducible] def growthConstant := 2+termTotal*52
@[irreducible] def guardBits := Nat.clog 2 (growthConstant+1)
@[irreducible] def precisionIncrement := ComplexFramedExecution.rows.length

theorem row_terms_le (r : RowIndex) : (gate r).terms.length≤termTotal := by
  rw [termTotal_literal]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨gate r,gate_mem r,rfl⟩)

private theorem growth_mono (a b : ℕ) (h : a≤b) : 2+a*52≤2+b*52 :=
  Nat.add_le_add_left (Nat.mul_le_mul_right 52 h) 2

theorem row_growth_le (r : RowIndex) : rowGrowth r≤growthConstant := by
  delta rowGrowth growthConstant
  exact growth_mono (gate r).terms.length termTotal (row_terms_le r)

theorem uniform_time_bound (r : RowIndex) (b : ℕ) :
    RawLinearCombination.cost (expression r) b≤(termTotal+1)*(12*b+42) :=
  (time_bound r b).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (row_terms_le r) 1))

private theorem binary_clog_bound (k : ℕ) : k≤2^(Nat.clog 2 k) :=
  Nat.le_pow_clog (by decide) k

theorem uniform_numerator_guard (r : RowIndex) (a : Wire → ℤ) (p : ℕ)
    (ha : ∀ i,|a i|≤((2^p:ℕ):ℤ)) (i : Wire) :
    |numeratorAction r a i|<((2^(p+guardBits):ℕ):ℤ) := by
  have hm := numerator_bound r a (2^p) ha i
  have hg : growthConstant+1≤2^guardBits := by
    delta guardBits
    exact binary_clog_bound (growthConstant+1)
  have hg' : rowGrowth r<2^guardBits := lt_of_le_of_lt (row_growth_le r)
    (lt_of_lt_of_le (Nat.lt_succ_self growthConstant) hg)
  have hh := Nat.mul_lt_mul_of_pos_right hg' (by positivity : 0<2^p)
  have hn : rowGrowth r*2^p<2^(p+guardBits) := by
    simpa only [pow_add,Nat.mul_comm] using hh
  exact hm.trans_lt (Int.ofNat_lt.mpr hn)

/-- One fixed guard allowance suffices for every actual sparse scalar row. -/
theorem uniform_result_signed (r : RowIndex) (b p : ℕ) (xs : ℕ → List (Fin 2))
    (hw : ∀ i,(xs i).length=b+1)
    (ha : ∀ i,|signedRows b xs i|≤((2^p:ℕ):ℤ)) (hb : p+guardBits≤b) :
    signedValue b (resultWord r xs)=numeratorAction r (signedRows b xs) (gate r).target := by
  have hg := uniform_numerator_guard r (signedRows b xs) p ha (gate r).target
  have hpow : ((2^(p+guardBits):ℕ):ℤ)≤((2^b:ℕ):ℤ) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) hb
  have hs := abs_lt.mp (hg.trans_le hpow)
  apply signed_unique b _ (RawLinearCombination.result_length (expression r) xs (b+1) hw) _
    (by constructor <;> linarith) (result_residue r b xs hw)

/-- The same fixed guard certifies exact real and imaginary physical outputs. -/
theorem uniform_result_complex (r : RowIndex) (b p n : ℕ) (xs ys : ℕ → List (Fin 2))
    (hx : ∀ i,(xs i).length=b+1) (hy : ∀ i,(ys i).length=b+1)
    (ha : ∀ i,|signedRows b xs i|≤((2^p:ℕ):ℤ))
    (hb : ∀ i,|signedRows b ys i|≤((2^p:ℕ):ℤ)) (hguard : p+guardBits≤b) :
    complexValue (signedValue b (resultWord r xs)) (signedValue b (resultWord r ys)) (n+1)=
      (RationalScalarGrid.castGate (gate r)).run
        (fun i => complexValue (signedRows b xs i) (signedRows b ys i) n) (gate r).target := by
  rw [uniform_result_signed r b p xs hx ha hguard,
    uniform_result_signed r b p ys hy hb hguard]
  exact (row_semantics r _ _ n (gate r).target).symm

end
end IntegerMultBounds.Machine.CompactComplexScalarIntegerRows
