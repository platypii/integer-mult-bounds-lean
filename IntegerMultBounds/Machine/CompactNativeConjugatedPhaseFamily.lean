import IntegerMultBounds.Machine.CompactNativeConjugatedPhaseZero

/-! One native basis program supplies every physical complex25 phase edge,
including zero-dimensional edges. A finite word budget absorbs both basis
passes, actual phase metadata and all joins into one stage-scale constant. -/
namespace IntegerMultBounds.Machine.CompactNativeConjugatedPhaseFamily
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ButterflyStreamData (Coefficient)
open ActivePrefixStageNativePolynomial (rows symbols)
open ActivePrefixStageHeadersData (Order)
open Networks.Shared50ModularControl (prime)
open CompactAllAxisPhaseDispatch (count edge)
open Networks.ComplexPhaseRowSchedule (dimension)
open CompactNativeConjugatedPhase
variable {s : Shape}

private theorem term_le_total {N : ℕ} (f : Fin N → ℕ) (pc : Fin N) :
    f pc≤∑ i : Fin N,f i :=
  Finset.single_le_sum (s:=Finset.univ) (f:=f)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ pc)

private opaque wordBudgetData :
    {n : ℕ // n=∑ pc : Fin count, (Networks.ComplexPhaseRowSchedule.word (edge pc)).length} :=
  ⟨∑ pc : Fin count, (Networks.ComplexPhaseRowSchedule.word (edge pc)).length,rfl⟩
def wordBudget : ℕ := wordBudgetData.val

theorem wordBudget_literal :
    wordBudget=∑ pc : Fin count, (Networks.ComplexPhaseRowSchedule.word (edge pc)).length :=
  wordBudgetData.property

theorem word_le (pc : Fin count) :
    (Networks.ComplexPhaseRowSchedule.word (edge pc)).length≤wordBudget := by
  rw [wordBudget_literal]
  exact term_le_total (fun pc : Fin count => (Networks.ComplexPhaseRowSchedule.word (edge pc)).length) pc

private opaque phaseConstantData :
    {n : ℕ // n=804304+(2*FixedBasePowerDescriptor.constant 2+15000)+(2*count+3)} :=
  ⟨804304+(2*FixedBasePowerDescriptor.constant 2+15000)+(2*count+3),rfl⟩
def phaseConstant : ℕ := phaseConstantData.val

theorem phaseConstant_literal :
    phaseConstant=804304+(2*FixedBasePowerDescriptor.constant 2+15000)+(2*count+3) :=
  phaseConstantData.property

theorem volume_le_scale (d : Inputs s) :
    (d.rows*s.recordWidth : ℕ)≤ActivePrefixStageInverseBudget.scale d := by
  unfold ActivePrefixStageInverseBudget.scale
  apply le_mul_of_one_le_right (Nat.cast_nonneg _)
  exact Real.one_le_rpow (by exact_mod_cast le_max_left 1 ((d.stage.f-1)*s.guard))
    Shared50RecursiveBudgetBound.exponent_range.1.le

def cost (D : ℕ) (d : Inputs s) (hslots : d.stage.slots=25^3)
    (order : Order) (pc : Fin count) (ell w : ℕ)
    (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed
      (ActivePrefixStagePairData.changePair d op) D) :=
  if 0<dimension (edge pc) then CompactNativeConjugatedPhase.cost D d hslots order pc ell w hp
  else CompactNativeConjugatedPhaseZero.cost D d hslots order pc ell w hp

def output (d : Inputs s) (hslots : d.stage.slots=25^3) (pc : Fin count) (ell w : ℕ)
    (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
    (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w) :=
  if 0<dimension (edge pc) then
    bank d ell (rows d (result d hslots pc ell xs) (result_width d hslots pc ell w xs hw))
  else bank d ell (rows d xs hw)

private theorem constant_le (k b : ℕ) :
    804273+2*k≤804304+(2*b+15000)+(2*k+3) := by omega

private theorem positive_constant (W C B : ℝ) (hW : 0≤W) (hC : 0≤C) (hB : 0≤B) :
    0<2*W*C+B+2 := by positivity

private theorem absorb (T B L W C V A S : ℝ)
    (hT : T≤2*L*C*S+B+2) (hL : L*C*S≤W*C*S)
    (hB : B≤A*V) (hV : A*V≤A*S) (hS : 1≤S) :
    T≤(2*W*C+A+2)*S := by
  have hL' := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ)≤2)
  have hS' := mul_le_mul_of_nonneg_left hS (by norm_num : (0 : ℝ)≤2)
  have hS'' : 2≤2*S := by simpa only [mul_one] using hS'
  calc
    T≤2*L*C*S+B+2 := hT
    _=2*(L*C*S)+B+2 := by ring
    _≤2*(W*C*S)+A*S+2*S := add_le_add (add_le_add hL' (hB.trans hV)) hS''
    _=(2*W*C+A+2)*S := by ring

private theorem choice_uniform {t q a : ℕ} (M : Program t q a)
    (p : Prop) [Decidable p] (v w w' : Tapes t a) (B B' : ℕ)
    (H H' L W C V A S : ℝ)
    (hL : L*C*S≤W*C*S) (hV : A*V≤A*S) (hS : 1≤S)
    (hpos : p → HoareTime M (fun z => z=v) (fun z => z=w) B ∧
      (B : ℝ)≤2*L*C*S+H+2 ∧ H≤A*V)
    (hzero : ¬p → HoareTime M (fun z => z=v) (fun z => z=w') B' ∧
      (B' : ℝ)≤2*L*C*S+H'+2 ∧ H'≤A*V) :
    HoareTime M (fun z => z=v) (fun z => z=if p then w else w') (if p then B else B') ∧
    ((if p then B else B' : ℕ) : ℝ)≤(2*W*C+A+2)*S := by
  by_cases hp : p
  · obtain ⟨hr,hb,hh⟩ := hpos hp
    simpa only [ite_eq_left hp] using And.intro hr (absorb _ _ _ _ _ _ _ _ hb hL hh hV hS)
  · obtain ⟨hr,hb,hh⟩ := hzero hp
    simpa only [ite_eq_right hp] using And.intro hr (absorb _ _ _ _ _ _ _ _ hb hL hh hV hS)

/-- A single stage witness covers the entire finite family; there is no
edge-dependent existential stage or supplied execution or cost callback. -/
theorem exists_program (D : ℕ) :
    ∃ q, ∃ P : Program ActivePrefixStageNative.tapes q prime, ∃ C : ℝ, 0<C ∧
    ∀ (s : Shape) (d : Inputs s) (hslots : d.stage.slots=25^3) (order : Order)
      (_ho : ActivePrefixStageHeadersSchedule.Ordered order d.stage)
      (pc : Fin count) (ell w : ℕ)
      (_hcode : s.payload=symbols (2^ell) w*3+0)
      (_hR : 2^ell≤s.payload) (_hwV : 2^ell*w≤s.payload)
      (hp : ∀ op,1<d.stage.f → ActivePrefixStageRuntimeData.Packed
        (ActivePrefixStagePairData.changePair d op) D)
      (xs : Fin (ActivePrefixStageTripleWords.count d) → Fin (2^ell) → Coefficient)
      (hw : ∀ i j,(xs i j).1.length=w ∧ (xs i j).2.length=w),
      HoareTime (program P order pc) (fun z => z=bank d ell (rows d xs hw))
        (fun z => z=output d hslots pc ell w xs hw) (cost D d hslots order pc ell w hp) ∧
      (cost D d hslots order pc ell w hp : ℝ)≤C*ActivePrefixStageInverseBudget.scale d := by
  obtain ⟨q,P,C,hC,hP⟩ := CompactComplexPhaseFixedWord.exists_fixed_program D
  let A : ℝ := 2*(wordBudget : ℝ)*C+(phaseConstant : ℝ)+2
  have hW : (0 : ℝ)≤wordBudget := Nat.cast_nonneg _
  have hPhase : (0 : ℝ)≤phaseConstant := Nat.cast_nonneg _
  have hA : 0<A := positive_constant _ _ _ hW hC.le hPhase
  refine ⟨q,P,A,hA,?_⟩
  intro s d hslots order ho pc ell w hcode hR hwV hp xs hw
  have hword : ((Networks.ComplexPhaseRowSchedule.word (edge pc)).length : ℝ)≤wordBudget := by
    exact Nat.cast_le.mpr (word_le pc)
  have hscale : 0≤ActivePrefixStageInverseBudget.scale d :=
    (ActivePrefixStageInverseBudget.one_le_scale d).trans' (by norm_num)
  have hwordpay := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hword hC.le) hscale
  have hv := volume_le_scale d
  have hphasepay := mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg phaseConstant : (0 : ℝ)≤phaseConstant)
  have hunit := ActivePrefixStageInverseBudget.one_le_scale d
  apply choice_uniform (program P order pc) (0<dimension (edge pc))
    (bank d ell (rows d xs hw))
    (bank d ell (rows d (result d hslots pc ell xs) (result_width d hslots pc ell w xs hw)))
    (bank d ell (rows d xs hw))
    (CompactNativeConjugatedPhase.cost D d hslots order pc ell w hp)
    (CompactNativeConjugatedPhaseZero.cost D d hslots order pc ell w hp)
    (AllAxisNativePolynomialCaller.cost order d pc ell w)
    (AllAxisNativePolynomialCaller.zeroCost order d ell)
    (Networks.ComplexPhaseRowSchedule.word (edge pc)).length wordBudget C
    (d.rows*s.recordWidth : ℕ) phaseConstant (ActivePrefixStageInverseBudget.scale d)
    hwordpay hphasepay hunit
  · intro hm
    obtain ⟨hrun,hbound⟩ := CompactNativeConjugatedPhase.runs_of_basis D P C hP
      s d hslots order ho pc hm ell w hcode hp xs hw
    have hphase := AllAxisNativePolynomialCaller.cost_linear order d hslots ho pc hm ell w hR hwV
    have hc : AllAxisNativePolynomialCaller.cost order d pc ell w≤phaseConstant*(d.rows*s.recordWidth) := by
      rw [phaseConstant_literal]
      exact hphase
    have hh : (AllAxisNativePolynomialCaller.cost order d pc ell w : ℝ)≤
        ((phaseConstant*(d.rows*s.recordWidth) : ℕ) : ℝ) := Nat.cast_le.mpr hc
    rw [Nat.cast_mul] at hh
    exact ⟨hrun,hbound,hh⟩
  · intro hm
    obtain ⟨hrun,hbound⟩ := CompactNativeConjugatedPhaseZero.runs_of_basis D P C hP
      s d hslots order ho pc (Nat.eq_zero_of_not_pos hm) ell w hcode hp xs hw
    have hphase := AllAxisNativePolynomialCaller.zero_cost_bound order d ho ell hR
    have hc : 804273+2*count≤phaseConstant := by
      rw [phaseConstant_literal]
      exact constant_le _ _
    have hh : (AllAxisNativePolynomialCaller.zeroCost order d ell : ℝ)≤
        ((phaseConstant*(d.rows*s.recordWidth) : ℕ) : ℝ) :=
      Nat.cast_le.mpr (hphase.trans (Nat.mul_le_mul_right _ hc))
    rw [Nat.cast_mul] at hh
    exact ⟨hrun,hbound,hh⟩

end
end IntegerMultBounds.Machine.CompactNativeConjugatedPhaseFamily
