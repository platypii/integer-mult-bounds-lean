import IntegerMultBounds.Networks.ComplexEndpoints

/-! Explicit endpoint correction programs and per-column scalar kernels for
the actual complex network. The source and sink sign corrections become
literal single-wire instructions placed around the lowered factor program,
with exact instruction counts (28 per data wire, independent of the rank
budget), and every all-column vector factor expands into its per-column
two-term Gaussian-dyadic translation kernels `aI + bX_v`. -/

namespace IntegerMultBounds.Networks.ComplexCorrections

open BinaryWalsh BinaryPhase BinaryColumns ComplexFramedExecution ComplexEndpoints
  ComplexPhaseBudget ComplexRank25

section Lists

theorem prod_flatMap {M α : Type*} [Monoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map (fun a => (f a).prod)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.prod_append, ih, List.map_cons, List.prod_cons]

theorem prod_map_filter {M α : Type*} [Monoid M] (l : List α) (p : α → Bool) (f : α → M) :
    ((l.filter p).map f).prod = (l.map (fun a => if p a = true then f a else 1)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.map_cons, List.prod_cons, ih, List.map_cons,
        List.prod_cons]
      simp [ha]
    · rw [List.filter_cons_of_neg ha, ih, List.map_cons, List.prod_cons]
      simp [ha]

theorem length_filter_eq_sum {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p).length = (l.map (fun a => if p a = true then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.length_cons, ih, List.map_cons, List.sum_cons]
      simp [ha, Nat.add_comm]
    · rw [List.filter_cons_of_neg ha, ih, List.map_cons, List.sum_cons]
      simp [ha]

theorem sum_map_const {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ) (h : ∀ a ∈ l, f a = c) :
    (l.map f).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, h a (List.mem_cons_self ..),
      ih (fun b hb => h b (List.mem_cons_of_mem a hb)), List.length_cons]
    ring

end Lists

section Signs
variable {h : ℕ}

/-- The coordinates carrying the binary vector. -/
def support (u : BinaryWalsh.Address h) : List (Fin h) :=
  (List.finRange h).filter (fun j => u j = 1)

theorem zmod_two_val (x : ZMod 2) : x.val = if x = 1 then 1 else 0 := by
  fin_cases x <;> rfl

/-- The support list has exactly the Hamming weight many entries. -/
theorem support_length (u : BinaryWalsh.Address h) : (support u).length = weight u := by
  rw [support, length_filter_eq_sum, weight, Fin.sum_univ_def]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  rw [zmod_two_val]
  simp

theorem sign_sum {ι : Type*} (s : Finset ι) (a : ι → ZMod 2) :
    sign (∑ i ∈ s, a i) = ∏ i ∈ s, sign (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, sign_add, ih]

theorem chi_eq_support_prod (u x : BinaryWalsh.Address h) :
    chi u x = ((support u).map (fun j => sign (x j))).prod := by
  rw [support, prod_map_filter, ← Fin.prod_univ_def]
  simp only [chi, Labels.binary, Labels.form_apply, zero_mul, sub_zero, sign_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hy : u j = 0 ∨ u j = 1 := by
    generalize u j = y
    fin_cases y
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hy with hy | hy <;> rw [hy] <;> simp

theorem chi_single (j : Fin h) (x : BinaryWalsh.Address h) :
    chi (Pi.single j 1) x = sign (x j) := by
  simp [chi, Labels.binary, Labels.form_apply, Pi.single_apply]

theorem characterMultiply_list_apply {α : Type*} (vs : List α) (e : α → BinaryWalsh.Address h)
    (f : BinaryWalsh.Arrays h) (x : BinaryWalsh.Address h) :
    ((vs.map (fun a => characterMultiply (e a))).prod f) x =
      (vs.map (fun a => chi (e a) x)).prod * f x := by
  induction vs generalizing f with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    change chi (e v) x * ((vs.map (fun a => characterMultiply (e a))).prod f) x = _
    rw [ih, mul_assoc]

/-- The sign character of a binary vector is the product of one coordinate
sign flip per support bit. -/
theorem characterMultiply_eq_prod (u : BinaryWalsh.Address h) :
    characterMultiply u =
      ((support u).map (fun j => characterMultiply (Pi.single j 1))).prod := by
  apply LinearMap.ext
  intro f
  funext x
  change chi u x * f x = _
  rw [characterMultiply_list_apply, chi_eq_support_prod]
  simp only [chi_single]

theorem tensorColumns_list_prod (k : ℕ)
    (Ts : List (BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h)) :
    tensorColumns k Ts.prod = (Ts.map (tensorColumns k)).prod := by
  induction Ts with
  | nil => simp
  | cons T Ts ih => rw [List.prod_cons, tensorColumns_mul, ih, List.map_cons, List.prod_cons]

/-- One all-column sign flip on one binary coordinate (the manuscript's `Z`
on that coordinate of every column). -/
noncomputable def signFactor (k : ℕ) (j : Fin h) : Operator h k :=
  tensorColumns k (characterMultiply (Pi.single j 1))

/-- The endpoint correction is the product of one all-column sign flip per
support coordinate. -/
theorem signColumns_eq_prod (k : ℕ) (u : BinaryWalsh.Address h) :
    signColumns k u = ((support u).map (signFactor k)).prod := by
  rw [signColumns, characterMultiply_eq_prod, tensorColumns_list_prod, List.map_map]
  rfl

/-- Each all-column sign flip is the product of its per-column sign flips. -/
theorem signFactor_columns (k : ℕ) (j : Fin h) :
    signFactor k j =
      (List.ofFn (fun c : Fin k => liftColumn c (characterMultiply (Pi.single j 1)))).prod := rfl

end Signs

section Kernels
variable {h : ℕ}

/-- The forward kernel `C = aI + bX_v` with `a = (1+i)/2`, `b = (1-i)/2`. -/
theorem kernel_one (v : BinaryWalsh.Address h) :
    kernel 1 v = ((1 + Complex.I) / 2) • LinearMap.id + ((1 - Complex.I) / 2) • translation v := by
  rw [kernel, phase_one]

/-- The inverse kernel `C⁻¹ = bI + aX_v` interchanges the two coefficients. -/
theorem kernel_neg_one (v : BinaryWalsh.Address h) :
    kernel (-1) v = ((1 - Complex.I) / 2) • LinearMap.id + ((1 + Complex.I) / 2) • translation v := by
  rw [kernel, phase_neg_one, sub_neg_eq_add, ← sub_eq_add_neg]

/-- One vector factor is the tensor over all columns of its one-column kernel. -/
theorem vectorFactor_eq_tensor (k : ℕ) (g : ZMod 4 × BinaryWalsh.Address h) :
    vectorFactor k g = tensorColumns k (kernel g.1 g.2) := by
  have he := tensorColumns_kernel_prod (k := k) [g]
  simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using he.symm

/-- Opposite-sign factors on the same direction are mutually inverse. -/
theorem vectorFactor_inverse (k : ℕ) (q : ZMod 4) (v : BinaryWalsh.Address h) :
    vectorFactor k (-q, v) * vectorFactor k (q, v) = 1 := by
  rw [vectorFactor_eq_tensor, vectorFactor_eq_tensor, ← tensorColumns_mul]
  have hk : kernel (-q) v * kernel q v = 1 := LinearMap.ext (kernel_inverse q v)
  rw [hk, tensorColumns_one]

/-- The per-column expansion of a forward vector factor: one explicit
Gaussian-dyadic two-term translation kernel in each column. -/
theorem vectorFactor_one_columns (k : ℕ) (v : BinaryWalsh.Address h) :
    vectorFactor k (1, v) =
      (List.ofFn (fun j : Fin k => ((1 + Complex.I) / 2) • LinearMap.id +
        ((1 - Complex.I) / 2) • columnTranslation j v)).prod := by
  simp only [vectorFactor, columnKernel, phase_one]

/-- The per-column expansion of an inverse vector factor. -/
theorem vectorFactor_neg_one_columns (k : ℕ) (v : BinaryWalsh.Address h) :
    vectorFactor k (-1, v) =
      (List.ofFn (fun j : Fin k => ((1 - Complex.I) / 2) • LinearMap.id +
        ((1 + Complex.I) / 2) • columnTranslation j v)).prod := by
  simp only [vectorFactor, columnKernel, phase_neg_one, sub_neg_eq_add, ← sub_eq_add_neg]

end Kernels

section Programs

abbrev Arr (k : ℕ) := BinaryColumns.Arrays (25 ^ 3) k
abbrev Op (k : ℕ) := Arr k →ₗ[ℚ] Arr k
abbrev Program (k : ℕ) := List (FramedFactorExecution.Instruction Wire ℚ (Arr k))

theorem restrict_prod {k : ℕ} (fs : List (BinaryColumns.Operator (25 ^ 3) k)) :
    (fs.map (fun f => f.restrictScalars ℚ)).prod = fs.prod.restrictScalars ℚ := by
  induction fs with
  | nil => rfl
  | cons f fs ih => rw [List.map_cons, List.prod_cons, List.prod_cons, ih]; rfl

theorem restrict_prod_ofFn {k n : ℕ} (T : Fin n → BinaryColumns.Operator (25 ^ 3) k) :
    (List.ofFn (fun j => (T j).restrictScalars ℚ)).prod = (List.ofFn T).prod.restrictScalars ℚ := by
  rw [← restrict_prod, List.map_ofFn]
  rfl

/-- Place factor lists on the wires named by a list of addresses, in order. -/
def onWires {ι α R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    (ws : List α) (wire : α → ι) (F : α → List (E →ₗ[R] E)) :
    List (FramedFactorExecution.Instruction ι R E) :=
  ws.flatMap (fun a => FramedFactorExecution.onWire (wire a) (F a))

section Run
variable {ι α R E : Type*} [DecidableEq ι] [CommRing R] [AddCommGroup E] [Module R E]

theorem run_onWires_notMem (ws : List α) (wire : α → ι) (F : α → List (E →ₗ[R] E))
    (x : ι → E) (i : ι) (hi : i ∉ ws.map wire) :
    FramedFactorExecution.run (onWires ws wire F) x i = x i := by
  induction ws generalizing x with
  | nil => rfl
  | cons a ws ih =>
    rw [List.map_cons, List.mem_cons, not_or] at hi
    rw [onWires, List.flatMap_cons, FramedFactorExecution.run_append]
    rw [← onWires, ih _ hi.2, FramedFactorExecution.run_onWire_other _ _ hi.1]

theorem run_onWires_mem (ws : List α) (wire : α → ι) (hw : (ws.map wire).Nodup)
    (F : α → List (E →ₗ[R] E)) (x : ι → E) (a : α) (ha : a ∈ ws) :
    FramedFactorExecution.run (onWires ws wire F) x (wire a) = (F a).prod (x (wire a)) := by
  induction ws generalizing x with
  | nil => exact absurd ha List.not_mem_nil
  | cons b ws ih =>
    rw [List.map_cons, List.nodup_cons] at hw
    rw [onWires, List.flatMap_cons, FramedFactorExecution.run_append, ← onWires]
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [run_onWires_notMem _ _ _ _ _ hw.1, FramedFactorExecution.run_onWire,
        Function.update_self]
    · have hne : wire a ≠ wire b := fun he => hw.1 (he ▸ List.mem_map_of_mem ha)
      rw [ih hw.2 _ ha, FramedFactorExecution.run_onWire, Function.update_of_ne hne]

omit [DecidableEq ι] in
theorem linearCount_onWires (ws : List α) (wire : α → ι) (F : α → List (E →ₗ[R] E)) :
    FramedFactorExecution.linearCount (onWires ws wire F) =
      (ws.map (fun a => (F a).length)).sum := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    rw [onWires, List.flatMap_cons, FramedFactorExecution.linearCount_append,
      FramedFactorExecution.linearCount_onWire, ← onWires, ih, List.map_cons, List.sum_cons]

end Run

/-- All physical X/Y bank addresses, enumerated once. -/
noncomputable def addresses : List (Wires.Address 25) :=
  List.ofFn (fun n : Fin (Fintype.card (Wires.Address 25)) =>
    (Fintype.equivFin (Wires.Address 25)).symm n)

theorem addresses_length : addresses.length = 12167000000 := by
  rw [addresses, List.length_ofFn, Wires.address_card, show Nat.choose 25 3 = 2300 by decide]
  norm_num

theorem mem_addresses (b : Wires.Address 25) : b ∈ addresses := by
  rw [addresses, List.mem_ofFn]
  exact ⟨Fintype.equivFin _ b, Equiv.symm_apply_apply _ _⟩

theorem addresses_nodup : addresses.Nodup := by
  rw [addresses]
  exact List.nodup_ofFn.mpr (Fintype.equivFin _).symm.injective

theorem addresses_nodup_x : (addresses.map (fun b => (Sum.inl b : Wire))).Nodup :=
  addresses_nodup.map Sum.inl_injective

theorem addresses_nodup_y : (addresses.map (fun b => (Sum.inr (Sum.inl b) : Wire))).Nodup :=
  addresses_nodup.map (fun _ _ he => Sum.inl_injective (Sum.inr_injective he))

variable (k : ℕ) (S : Wires.Address 25 → List (Op k))

/-- Source corrections: the sign factors `S b` on every X input. -/
noncomputable def sourceProgram : Program k :=
  onWires addresses (fun b => (Sum.inl b : Wire)) S

/-- Sink corrections: the sign factors and the single scalar `i^(27k)` on every
Y output, then one negation on every X output. -/
noncomputable def sinkProgram : Program k :=
  onWires addresses (fun b => (Sum.inr (Sum.inl b) : Wire))
    (fun b => (Complex.I ^ (27 * k) •
      (LinearMap.id : BinaryColumns.Operator (25 ^ 3) k)).restrictScalars ℚ :: S b) ++
  onWires addresses (fun b => (Sum.inl b : Wire)) (fun _ => [-LinearMap.id])

/-- The complete corrected program: source corrections, the lowered rank
factors with all scalar gates, then sink corrections. -/
noncomputable def corrected (directions : Directions) : Program k :=
  sourceProgram k S ++ lowered k directions ++ sinkProgram k S

variable {k S}
variable (hS : ∀ b, (S b).prod = (signColumns k (terminalVector b)).restrictScalars ℚ)
include hS

theorem sourceProgram_run (stored : Wire → Arr k) :
    FramedFactorExecution.run (sourceProgram k S) stored = correctInput k stored := by
  funext i
  rcases i with b | i
  · rw [sourceProgram, run_onWires_mem _ _ addresses_nodup_x _ _ _ (mem_addresses b), hS]
    rfl
  · rw [sourceProgram, run_onWires_notMem]
    · rfl
    · simp

theorem sinkProgram_run (y : Wire → Arr k) :
    FramedFactorExecution.run (sinkProgram k S) y = fun i => correctOutput k y (route i) := by
  funext i
  rw [sinkProgram, FramedFactorExecution.run_append]
  rcases i with b | b | s
  · rw [run_onWires_mem _ _ addresses_nodup_x _ _ _ (mem_addresses b),
      run_onWires_notMem _ _ _ _ _ (by simp)]
    rfl
  · rw [run_onWires_notMem _ _ _ _ _ (by simp),
      run_onWires_mem _ _ addresses_nodup_y _ _ _ (mem_addresses b), List.prod_cons,
      Module.End.mul_apply, hS]
    rfl
  · rw [run_onWires_notMem _ _ _ _ _ (by simp), run_onWires_notMem _ _ _ _ _ (by simp)]
    rfl

/-- The corrected program sends every input array, including dirty scratch,
to its full forward tensor transform, delivered on the exchanged bank. -/
theorem corrected_run (directions : Directions) (hd : Realizes directions)
    (stored : Wire → Arr k) :
    FramedFactorExecution.run (corrected k S directions) stored =
      fun i => fullFrame k (stored (route i)) := by
  rw [corrected, FramedFactorExecution.run_append, FramedFactorExecution.run_append,
    sourceProgram_run hS, sinkProgram_run hS, corrected_lowered_run k directions hd stored]

omit hS in
theorem sourceProgram_count (c : ℕ) (hc : ∀ b, (S b).length = c) :
    FramedFactorExecution.linearCount (sourceProgram k S) = 12167000000 * c := by
  rw [sourceProgram, linearCount_onWires, sum_map_const _ _ c (fun b _ => hc b), addresses_length]

omit hS in
theorem sinkProgram_count (c : ℕ) (hc : ∀ b, (S b).length = c) :
    FramedFactorExecution.linearCount (sinkProgram k S) = 12167000000 * (c + 2) := by
  rw [sinkProgram, FramedFactorExecution.linearCount_append, linearCount_onWires,
    linearCount_onWires, sum_map_const _ _ (c + 1) (fun b _ => by rw [List.length_cons, hc]),
    sum_map_const _ (fun _ => [-LinearMap.id].length) 1 (fun _ _ => rfl), addresses_length]
  ring

omit hS in
/-- Exact instruction count: the rank factors plus `2c + 2` corrections per
address, i.e. `c + 1` per data wire. -/
theorem corrected_count (directions : Directions) (hd : Realizes directions) (c : ℕ)
    (hc : ∀ b, (S b).length = c) :
    FramedFactorExecution.linearCount (corrected k S directions) =
      (directions.map List.length).sum + 12167000000 * (2 * c + 2) := by
  rw [corrected, FramedFactorExecution.linearCount_append,
    FramedFactorExecution.linearCount_append, sourceProgram_count c hc, sinkProgram_count c hc,
    lowered_count k directions hd]
  ring

end Programs

section AllColumn

/-- The all-column sign factors of one terminal: one per support coordinate. -/
noncomputable def signList (k : ℕ) (u : BinaryWalsh.Address (25 ^ 3)) : List (Op k) :=
  (support u).map (fun j => (signFactor k j).restrictScalars ℚ)

theorem signList_prod (k : ℕ) (u : BinaryWalsh.Address (25 ^ 3)) :
    (signList k u).prod = (signColumns k u).restrictScalars ℚ := by
  rw [signList, signColumns_eq_prod, ← restrict_prod, List.map_map]
  rfl

theorem signList_length (k : ℕ) (b : Wires.Address 25) :
    (signList k (terminalVector b)).length = 27 := by
  rw [signList, List.length_map, support_length, terminalVector_weight]

/-- The corrected program with all-column sign factors: 27 per X input, 28 per
Y output, one per X output. -/
noncomputable def correctedAll (k : ℕ) (directions : Directions) : Program k :=
  corrected k (fun b => signList k (terminalVector b)) directions

/-- One direction family gives, for every column count, the exact instruction
count (rank total plus 56 corrections per address, i.e. 28 per data wire),
the strict branching budget on the factor part, and the full corrected
forward transform on every wire. -/
theorem exists_correctedAll_budget :
    ∃ directions : Directions, Realizes directions ∧ ∀ k,
      FramedFactorExecution.linearCount (correctedAll k directions) = rankSum + 56 * 12167000000 ∧
      rankSum ≤ 916333630984500000 ∧
      (rankSum : ℝ) / 58645352620000 < (15625 : ℝ) ^ Parameters.sigma ∧
      ∀ stored : Wire → Arr k,
        FramedFactorExecution.run (correctedAll k directions) stored =
          fun i => fullFrame k (stored (route i)) := by
  obtain ⟨directions, hd, he⟩ := exists_uniform_execution
  refine ⟨directions, hd, fun k => ⟨?_, rank_budget, branching_bound, fun stored => ?_⟩⟩
  · rw [correctedAll, corrected_count directions hd 27 (signList_length k), ← (he k).1,
      lowered_count k directions hd]
  · exact corrected_run (fun b => signList_prod k (terminalVector b)) directions hd stored

end AllColumn

section PerColumn

/-- Every all-column vector factor replaced by its `k` per-column kernels. -/
noncomputable def columnMaps (k : ℕ) (directions : Directions) : List (List (Op k)) :=
  directions.map (fun gs => gs.flatMap (fun g =>
    List.ofFn (fun j : Fin k => (columnKernel j g.1 g.2).restrictScalars ℚ)))

theorem columnMaps_prod (k : ℕ) (gs : List (ZMod 4 × BinaryWalsh.Address (25 ^ 3))) :
    (gs.flatMap (fun g =>
      List.ofFn (fun j : Fin k => (columnKernel j g.1 g.2).restrictScalars ℚ))).prod =
      (gs.map (fun g => (vectorFactor k g).restrictScalars ℚ)).prod := by
  rw [prod_flatMap]
  refine congrArg List.prod (List.map_congr_left fun g _ => ?_)
  rw [restrict_prod_ofFn]
  rfl

theorem column_certificate (k : ℕ) (directions : Directions) (hd : Realizes directions) :
    List.Forall₂ (fun op fs => fs.prod = op)
      (FramedFactorExecution.edgeOperators (network k)) (columnMaps k directions) := by
  have h := factor_certificate k directions hd
  rw [factorMaps, List.forall₂_map_right_iff] at h
  rw [columnMaps, List.forall₂_map_right_iff]
  refine h.imp fun op gs hg => ?_
  rw [columnMaps_prod]
  exact hg

/-- The lowered program with every factor expanded into per-column kernels. -/
noncomputable def loweredColumns (k : ℕ) (directions : Directions) : Program k :=
  FramedFactorExecution.lower (network k) (columnMaps k directions)

theorem loweredColumns_run (k : ℕ) (directions : Directions) (hd : Realizes directions)
    (stored : Wire → Arr k) :
    FramedFactorExecution.run (loweredColumns k directions) stored =
      FramedFactorExecution.run (lowered k directions) stored := by
  rw [loweredColumns, FramedFactorExecution.run_lower _ _ (column_certificate k directions hd),
    lowered, FramedFactorExecution.run_lower _ _ (factor_certificate k directions hd)]

/-- Per-column kernel count: `k` scalar kernels per rank factor. -/
theorem loweredColumns_count (k : ℕ) (directions : Directions) (hd : Realizes directions) :
    FramedFactorExecution.linearCount (loweredColumns k directions) =
      k * (directions.map List.length).sum := by
  rw [loweredColumns, FramedFactorExecution.linearCount_lower _ _ (column_certificate k directions hd),
    columnMaps, List.map_map]
  have hl : ∀ gs : List (ZMod 4 × BinaryWalsh.Address (25 ^ 3)),
      (List.length ∘ fun gs : List (ZMod 4 × BinaryWalsh.Address (25 ^ 3)) => gs.flatMap (fun g =>
        List.ofFn (fun j : Fin k => (columnKernel j g.1 g.2).restrictScalars ℚ))) gs =
        gs.length * k := by
    intro gs
    simp only [Function.comp_apply, List.length_flatMap, List.length_ofFn]
    rw [sum_map_const _ _ k (fun _ _ => rfl)]
  rw [List.map_congr_left (fun gs _ => hl gs), List.sum_map_mul_right, mul_comm]

/-- The per-column sign flips of one terminal: `27 k` single-column kernels. -/
noncomputable def columnSignList (k : ℕ) (u : BinaryWalsh.Address (25 ^ 3)) : List (Op k) :=
  (support u).flatMap (fun j => List.ofFn (fun c : Fin k =>
    (liftColumn c (characterMultiply (Pi.single j 1))).restrictScalars ℚ))

theorem columnSignList_prod (k : ℕ) (u : BinaryWalsh.Address (25 ^ 3)) :
    (columnSignList k u).prod = (signColumns k u).restrictScalars ℚ := by
  rw [columnSignList, prod_flatMap, signColumns_eq_prod, ← restrict_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
  rw [restrict_prod_ofFn]
  rfl

theorem columnSignList_length (k : ℕ) (b : Wires.Address 25) :
    (columnSignList k (terminalVector b)).length = 27 * k := by
  rw [columnSignList, List.length_flatMap]
  simp only [List.length_ofFn]
  rw [sum_map_const _ _ k (fun _ _ => rfl), support_length, terminalVector_weight]

/-- The fully column-expanded corrected program: every instruction is one
single-column two-term kernel, one single-column sign flip, one scalar, one
negation, or one original scalar gate. -/
noncomputable def correctedColumns (k : ℕ) (directions : Directions) : Program k :=
  sourceProgram k (fun b => columnSignList k (terminalVector b)) ++ loweredColumns k directions ++
    sinkProgram k (fun b => columnSignList k (terminalVector b))

theorem correctedColumns_run (k : ℕ) (directions : Directions) (hd : Realizes directions)
    (stored : Wire → Arr k) :
    FramedFactorExecution.run (correctedColumns k directions) stored =
      fun i => fullFrame k (stored (route i)) := by
  rw [correctedColumns, FramedFactorExecution.run_append, FramedFactorExecution.run_append,
    sourceProgram_run (fun b => columnSignList_prod k (terminalVector b)),
    sinkProgram_run (fun b => columnSignList_prod k (terminalVector b)),
    loweredColumns_run k directions hd, corrected_lowered_run k directions hd stored]

/-- Single-column instruction count: `k` kernels per rank factor plus
`54 k + 2` corrections per address. -/
theorem correctedColumns_count (k : ℕ) (directions : Directions) (hd : Realizes directions) :
    FramedFactorExecution.linearCount (correctedColumns k directions) =
      k * (directions.map List.length).sum + 12167000000 * (54 * k + 2) := by
  rw [correctedColumns, FramedFactorExecution.linearCount_append,
    FramedFactorExecution.linearCount_append,
    sourceProgram_count (27 * k) (columnSignList_length k),
    sinkProgram_count (27 * k) (columnSignList_length k), loweredColumns_count k directions hd]
  ring

/-- One direction family gives the column-expanded program for every column
count: exact single-column kernel count `k · rankSum + (54 k + 2)` per
address, the branching budget on the rank total, and the corrected forward
transform. -/
theorem exists_correctedColumns_budget :
    ∃ directions : Directions, Realizes directions ∧ ∀ k,
      FramedFactorExecution.linearCount (correctedColumns k directions) =
        k * rankSum + 12167000000 * (54 * k + 2) ∧
      rankSum ≤ 916333630984500000 ∧
      (rankSum : ℝ) / 58645352620000 < (15625 : ℝ) ^ Parameters.sigma ∧
      ∀ stored : Wire → Arr k,
        FramedFactorExecution.run (correctedColumns k directions) stored =
          fun i => fullFrame k (stored (route i)) := by
  obtain ⟨directions, hd, he⟩ := exists_uniform_execution
  refine ⟨directions, hd, fun k => ⟨?_, rank_budget, branching_bound,
    correctedColumns_run k directions hd⟩⟩
  rw [correctedColumns_count k directions hd, ← (he k).1, lowered_count k directions hd]

end PerColumn

end IntegerMultBounds.Networks.ComplexCorrections
