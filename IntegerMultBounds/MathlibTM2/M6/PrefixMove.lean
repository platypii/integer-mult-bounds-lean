module

public import IntegerMultBounds.Networks.AffineFieldProgram
public import IntegerMultBounds.MathlibTM2.M6.PrefixLabel
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.PortFrame
public import IntegerMultBounds.MathlibTM2.Cover.Weighted
public import IntegerMultBounds.MathlibTM2.Routing.BlockExchangeIndex

/-! A nested PR589 MOVE exchanges a single interval in triangular coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Shared50ModularControl
open M8.Exchange (exchange transform)

open IntegerMultBounds.Swap.Shear (Op State run interchanges)

/-- Swap matching coordinates in the two address halves. -/
def coordinateSwaps {ι R : Type*} (ks : List ι) : List (Op ι R) :=
  ks.map fun k => .interchange k k

theorem coordinateSwaps_run {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (ks : List ι) (distinct : ks.Nodup) (s : State ι R) :
    run (coordinateSwaps ks) s = exchange (M8.Exchange.indicator ks) s := by
  have eval (l : List ι) (t : State ι R) :
      exchange (M8.Exchange.indicator l) t =
        (fun k => if k ∈ l then t.2 k else t.1 k,
         fun k => if k ∈ l then t.1 k else t.2 k) := by
    apply Prod.ext <;> funext k <;>
      simp only [exchange, sub_mulVec, one_mulVec, Pi.add_apply, Pi.sub_apply,
        M8.Exchange.mulVec_indicator] <;> split_ifs <;> simp
  rw [eval]
  induction ks generalizing s with
  | nil => simp [coordinateSwaps]
  | cons k ks ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    change run (coordinateSwaps ks) ((Op.interchange k k).run s) = _
    rw [ih tail]
    apply Prod.ext <;> funext j <;> by_cases eq : j = k
    all_goals simp_all [Op.run, Function.update]

/-- The instruction word for the middle of a MOVE on eight address coordinates. -/
def intervalSwaps {R : Type*} (d e : ℕ) : List (Op (Fin 8) R) :=
  coordinateSwaps ((List.finRange 8).filter fun k => d ≤ k.val ∧ k.val < e)

theorem intervalSwaps_run {R : Type*} [CommRing R] (d e : ℕ) (s : State (Fin 8) R) :
    run (intervalSwaps d e) s =
      exchange (diagonal fun k => if d ≤ k.val ∧ k.val < e then 1 else 0) s := by
  rw [intervalSwaps, coordinateSwaps_run _ ((List.nodup_finRange 8).filter _)]
  simp [M8.Exchange.indicator]

theorem intervalSwaps_interchanges {R : Type*} (d e : ℕ) (hd : d ≤ 8) (he : e ≤ 8) :
    interchanges (intervalSwaps (R := R) d e) = e - d := by
  have count : ∀ a b : Fin 9, ((List.finRange 8).filter fun k =>
      a.val ≤ k.val ∧ k.val < b.val).length = b.val - a.val := by decide +kernel
  simpa [intervalSwaps, coordinateSwaps, interchanges, Op.isInterchange, List.filter_map]
    using count ⟨d, by omega⟩ ⟨e, by omega⟩

/-- With two consecutive eight-atom address halves, one block exchange performs
all the interval swaps. Each atom occupies `w` consecutive positions, and `r`
tracks a position within the atom on either half. -/
theorem intervalSwaps_blockExchange (d e w : ℕ) (de : d ≤ e) (he : e ≤ 8)
    (k : Fin 8) (r : ℕ) (hr : r < w) :
    let width := (e - d) * w
    let pos := k.val * w + r
    let move := Routing.blockExchange (d * w) ((8 + d) * w) width
    move pos = (if d ≤ k.val ∧ k.val < e then 8 * w + pos else pos) ∧
    move (8 * w + pos) = (if d ≤ k.val ∧ k.val < e then pos else 8 * w + pos) := by
  intro width pos move
  have endLeft : d * w + width = e * w := by
    dsimp [width]
    rw [← Nat.add_mul, Nat.add_sub_of_le de]
  have low (a : ℕ) (h : a ≤ k.val) : a * w ≤ pos :=
    (Nat.mul_le_mul_right w h).trans (Nat.le_add_right _ _)
  have high (a : ℕ) (h : k.val < a) : pos < a * w := by
    calc pos < k.val * w + w := Nat.add_lt_add_left hr _
         _ = (k.val + 1) * w := (Nat.succ_mul _ _).symm
         _ ≤ a * w := Nat.mul_le_mul_right w h
  have top := high 8 k.isLt
  have last := Nat.mul_le_mul_right w he
  simp only [move, Routing.blockExchange, endLeft, Nat.add_mul]
  by_cases h : d ≤ k.val ∧ k.val < e
  · have := low d h.1
    have := high e h.2
    split_ifs <;> omega
  · have outside : pos < d * w ∨ e * w ≤ pos := by
      by_cases hk : k.val < d
      · exact Or.inl (high _ hk)
      · exact Or.inr (low _ (by omega))
    split_ifs <;> omega

/-- Bit action of the rectangular record permutation used by the host exchange
on the two address halves. The child width is the dimension gain times the atom width. -/
theorem prefixMoveRank_bits (d e w R : ℕ) (de : d ≤ e) (he : e ≤ 8)
    (k : Fin 8) (r : ℕ) (hr : r < w) (i : Fin (R * 2 ^ (16 * w))) :
    let width := (e - d) * w
    let pos := k.val * w + r
    ∃ (sep : d * w + width ≤ (8 + d) * w) (bound : (8 + d) * w + width ≤ 16 * w),
      let j := Routing.blockExchangeRank (16 * w) (d * w) ((8 + d) * w) width R sep bound i
      (j.val.testBit pos = i.val.testBit (if d ≤ k.val ∧ k.val < e then 8 * w + pos else pos)) ∧
      (j.val.testBit (8 * w + pos) = i.val.testBit (if d ≤ k.val ∧ k.val < e then pos else 8 * w + pos)) := by
  intro width pos
  have ends : d * w + width = e * w := by
    dsimp [width]
    rw [← Nat.add_mul, Nat.add_sub_of_le de]
  have last := Nat.mul_le_mul_right w he
  have sep : d * w + width ≤ (8 + d) * w := by rw [Nat.add_mul]; omega
  have bound : (8 + d) * w + width ≤ 16 * w := by rw [Nat.add_mul]; omega
  refine ⟨sep, bound, ?_⟩
  intro j
  have top : pos < 8 * w := by
    calc pos < k.val * w + w := Nat.add_lt_add_left hr _
         _ = (k.val + 1) * w := (Nat.succ_mul _ _).symm
         _ ≤ 8 * w := Nat.mul_le_mul_right w k.isLt
  have bits (q : ℕ) (hq : q < 16 * w) := Routing.blockExchangeRank_bit _ _ _ _ R sep bound i ⟨q, hq⟩
  obtain ⟨left, right⟩ := intervalSwaps_blockExchange d e w de he k r hr
  exact ⟨(bits pos (by omega)).trans (congrArg i.val.testBit left),
    (bits (8 * w + pos) (by omega)).trans (congrArg i.val.testBit right)⟩

/-- Conjugate the interval swaps by a change of basis on each address half. -/
noncomputable def prefixMoveProgram {R : Type*} [CommRing R] (d e : ℕ)
    (C : Matrix (Fin 8) (Fin 8) R) : List (Op (Fin 8) R) :=
  [.transformH C⁻¹, .transformD C⁻¹] ++ intervalSwaps d e ++ [.transformH C, .transformD C]

theorem prefixMoveProgram_interchanges {R : Type*} [CommRing R] (d e : ℕ)
    (hd : d ≤ 8) (he : e ≤ 8) (C : Matrix (Fin 8) (Fin 8) R) :
    interchanges (prefixMoveProgram d e C) = e - d := by
  simpa [prefixMoveProgram, interchanges, Op.isInterchange] using
    intervalSwaps_interchanges (R := R) d e hd he

open IntegerMultBounds.Networks

/-- Each eight-coordinate triangular pass costs eight scalar scalings and
twenty-eight controlled shifts, independent of the tape radix. -/
theorem prefixAdapter_length {R : Type*} (C : Matrix (Fin 8) (Fin 8) R) :
    (OrderedAffine.program C).length = 36 := by
  have row (i : Fin 8) : (OrderedAffine.row C i).length = i.val + 1 := by
    simp only [OrderedAffine.row, List.length_cons, List.length_map, OrderedAffine.earlier,
      Finset.length_toList]
    rw [show Finset.univ.filter (· < i) = Finset.Iio i by ext; simp]
    rw [Fin.card_Iio]
  simp only [OrderedAffine.program, List.length_flatMap, row, IntegerMultBounds.Swap.Shear.descending, Fin.sort_univ]
  decide +kernel

/-- Expand both basis changes into legal scalar operations. This introduces no
additional interchanges and implements the same MOVE on arbitrary field states. -/
theorem compile_prefixMove {R : Type*} [CommRing R] (d e : ℕ) (hd : d ≤ 8) (he : e ≤ 8)
    (C : Matrix (Fin 8) (Fin 8) R) (lower : C.IsLowerTriangular) (unit : IsUnit C) :
    let p := prefixMoveProgram d e C
    let q := AffineFieldProgram.compile p
    (∀ op ∈ q, AffineFieldProgram.Legal op) ∧
      AffineFieldProgram.interchanges q = e - d ∧
      ∀ s, AffineFieldProgram.run q s = run p s := by
  intro p q
  have invUnit := Matrix.isUnit_nonsing_inv_iff.mpr unit
  let := C.invertibleOfIsUnitDet ((Matrix.isUnit_iff_isUnit_det _).mp unit)
  have invLower := blockTriangular_inv_of_blockTriangular lower
  have valid : ∀ op ∈ p, AffineFieldProgram.Valid op := by
    intro op mem
    simp only [p, prefixMoveProgram, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rcases mem with ((rfl | rfl) | swap) | (rfl | rfl)
    · exact ⟨fun _ _ h => invLower h, invUnit⟩
    · exact ⟨fun _ _ h => invLower h, invUnit⟩
    · obtain ⟨k, _, rfl⟩ := List.mem_map.mp swap
      trivial
    · exact ⟨fun _ _ h => lower h, unit⟩
    · exact ⟨fun _ _ h => lower h, unit⟩
  exact ⟨AffineFieldProgram.compile_legal _ valid,
    (AffineFieldProgram.compile_interchanges p).trans (prefixMoveProgram_interchanges _ _ hd he C),
    AffineFieldProgram.compile_run _ (fun op h => (valid op h).triangular)⟩

/-- The explicit triangular eigenbasis of the MOVE projector. -/
def moveBasis {R : Type*} [CommRing R] (U : Matrix (Fin 8) (Fin 8) R) :=
  let E := diagonal fun k => U k k
  U * E + (1 - U) * (1 - E)

open M8.Height in
theorem moveBasis_height (A B : Matrix (Fin 8) (Fin 8) ℚ)
    (ha : Bounded A (2^100)) (hb : Bounded B (2^100)) :
    Bounded (moveBasis (B-A)) (2^6465) := by
  let U := B-A
  let E := diagonal fun k => U k k
  have hu : Bounded U (2^201) := bounded_sub hb ha
  have he : Bounded E (2^201) := by
    intro i j
    by_cases h : i = j
    · subst j
      simpa [E] using hu i i
    · simp [E, diagonal_apply_ne _ h]
  have result := bounded_add (bounded_mul hu he)
    (bounded_mul (bounded_sub bounded_one hu) (bounded_sub bounded_one he))
  simp only [Fintype.card_fin, Nat.reduceAdd, Nat.reduceMul] at result
  exact result

open M8.Height in
/-- A cofactor is a signed sum of at most eight factorial products. -/
theorem adjugate_height (C : Matrix (Fin 8) (Fin 8) ℚ) {e : ℕ}
    (bounded : Bounded C (2^e)) : Bounded C.adjugate (2^((e*8+1)*Nat.factorial 8)) := by
  intro i j
  rw [adjugate_apply, det_apply]
  let A := C.updateRow j (Pi.single i 1)
  have entry (k l) : ht (A k l) ≤ 2^e := by
    simp only [A, updateRow_apply, Pi.single_apply]
    split_ifs <;> first | exact bounded _ _ | simpa using (Nat.one_le_two_pow (n := e))
  have product (σ : Equiv.Perm (Fin 8)) (s : Finset (Fin 8)) :
      ht (∏ k ∈ s, A (σ k) k) ≤ (2^e)^s.card := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert k s fresh ih =>
      rw [Finset.prod_insert fresh, Finset.card_insert_of_notMem fresh, pow_succ']
      exact (ht_mul _ _).trans (Nat.mul_le_mul (entry _ _) ih)
  apply (ht_sum _ _ ((2^e)^8) ?_).trans
  · rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin, ← pow_mul, ← pow_succ', ← pow_mul]
  · intro σ _
    have h := product σ Finset.univ
    simp only [Finset.card_univ, Fintype.card_fin] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with pos | neg
    · simpa only [pos, one_smul] using h
    · simpa only [neg, Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul, ht_neg] using h

open IntegerMultBounds.Swap.Modular
open IntegerMultBounds.Networks.ModularFrameSchedule in
theorem moveBasis_reduce (m : ℕ) (U : Matrix (Fin 8) (Fin 8) ℚ) (hu : Admissible m U) :
    Admissible m (moveBasis U) ∧ reduce m (moveBasis U) = moveBasis (reduce m U) := by
  let E := diagonal fun k => U k k
  have he : Admissible m E := by
    intro i j
    by_cases h : i = j
    · subst j
      simpa [E] using hu i i
    · simp [E, diagonal_apply_ne _ h]
  have diag : reduce m E = diagonal (fun k => reduce m U k k) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [E, reduce]
    · simp [E, reduce, diagonal_apply_ne _ h, ratMod_zero]
  have h1 := admissible_one (ι := Fin 8) m
  have hU := admissible_sub m h1 hu
  have hE := admissible_sub m h1 he
  exact ⟨admissible_add m (admissible_mul m hu he) (admissible_mul m hU hE), by
    change reduce m (U * E + (1-U) * (1-E)) = _
    rw [reduce_add m (admissible_mul m hu he) (admissible_mul m hU hE), reduce_mul m hu he,
      reduce_mul m hU hE, reduce_sub m h1 hu, reduce_sub m h1 he, reduce_one, diag]
    rfl⟩

/-- Compile the forward basis and its adjugate once, before choosing a tape width. -/
noncomputable def rationalMoveWord (d e : ℕ) (C : Matrix (Fin 8) (Fin 8) ℚ) :=
  AffineFieldProgram.compile ([Op.transformH C.adjugate, .transformD C.adjugate] ++
    intervalSwaps d e ++ [.transformH C, .transformD C])

theorem rationalMoveWord_reduce (m d e : ℕ) (C : Matrix (Fin 8) (Fin 8) ℚ)
    (adm : Admissible m C) (det : (reduce m C).det = 1) :
    (rationalMoveWord d e C).map (AffineFieldProgram.mapOp (ratMod m)) =
      AffineFieldProgram.compile (prefixMoveProgram d e (reduce m C)) := by
  let L := lift m C adm
  have val : L.adjugate.map (denCoprime m).subtype = C.adjugate := by
    apply ((denCoprime m).subtype.map_adjugate L).trans
    exact congrArg Matrix.adjugate (lift_map_val m C adm)
  have adj : reduce m C.adjugate = (reduce m C).adjugate := by
    rw [← val, reduce_lift m C adm]
    exact (toZMod m).map_adjugate L
  have inv : (reduce m C)⁻¹ = (reduce m C).adjugate := by
    rw [Matrix.nonsing_inv_apply _ (det ▸ isUnit_one)]
    simp [det]
  unfold rationalMoveWord
  rw [← AffineFieldProgram.compile_map]
  congr 1
  simp only [prefixMoveProgram, List.map_append, List.map_cons, List.map_nil,
    AffineFieldProgram.mapShear, intervalSwaps, coordinateSwaps, List.map_map]
  change _ ++ _ ++ [Op.transformH (reduce m C), .transformD (reduce m C)] = _
  rw [inv, ← adj]
  rfl

/-- One family of tape-ring frames serves every nested pair. In coordinates given by
a unitriangular adapter, its MOVE exchanges precisely the newly gained prefix positions. -/
theorem nested_label_moves (w : ℕ) :
    let R := ZMod (prime ^ w)
    let dim := fun i : Fin 636 => Geometry.Dimensions.value i.val
    ∀ P : Fin 636 → Matrix (Fin 8) (Fin 8) R,
      (∀ l i j, i < j → P l i j = 0) →
      (∀ l i, P l i i = if i.val < dim l then 1 else 0) →
      (∀ i j : Fin 636, (∀ k ∈ Frames.labels i.val, k ∈ Frames.labels j.val) →
        P j * P i = P i ∧ P i * P j = P i) →
      ∀ i j : Fin 636, (∀ k ∈ Frames.labels i.val, k ∈ Frames.labels j.val) →
        let U := P j - P i
        let C := moveBasis U
        C.IsLowerTriangular ∧ C⁻¹.IsLowerTriangular ∧
          (∀ k, C k k = 1) ∧ C * C⁻¹ = 1 ∧ ∀ s,
          run (prefixMoveProgram (dim i) (dim j) C) s = exchange (P i) (exchange (P j) s) := by
  intro R dim P lower diag nested i j incl
  let E : Matrix (Fin 8) (Fin 8) R := diagonal fun k => if dim i ≤ k.val ∧ k.val < dim j then 1 else 0
  have sub : Geometry.label i.val ≤ Geometry.label j.val := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, rfl⟩
    exact Geometry.root_mem _ _ (incl k hk)
  have le := Submodule.finrank_mono sub
  rw [Geometry.Dimensions.dimension _ i.isLt, Geometry.Dimensions.dimension _ j.isLt] at le
  change dim i ≤ dim j at le
  let U := P j - P i
  have entry (k : Fin 8) : U k k = if dim i ≤ k.val ∧ k.val < dim j then 1 else 0 := by
    simp only [U, Matrix.sub_apply, diag]
    split_ifs <;> first | omega | simp
  obtain ⟨ji, ij⟩ := nested i j incl
  have idem (l) := (nested l l (fun _ h => h)).1
  have tri : U.IsLowerTriangular := fun {a b} h => by
    have lt : a < b := h
    simp [U, Matrix.sub_apply, lower j a b lt, lower i a b lt]
  obtain ⟨C, hC, ones, unit, basis, canonical⟩ := Nine.triangular_projector_basis U tri
    (M8.Exchange.sub_idempotent _ _ (idem i) (idem j) ij ji)
    (fun k => by rw [entry]; split <;> simp)
  have eq : diagonal (fun k => U k k) = E := congrArg diagonal (funext entry)
  rw [eq] at basis
  let := C.invertibleOfIsUnitDet unit
  change C = U * diagonal (fun k => U k k) + (1-U) * (1-diagonal (fun k => U k k)) at canonical
  dsimp only [moveBasis]
  rw [← canonical]
  refine ⟨hC, blockTriangular_inv_of_blockTriangular hC, ones, C.mul_nonsing_inv unit, ?_⟩
  intro s
  simp only [prefixMoveProgram, IntegerMultBounds.Swap.Shear.run_append, intervalSwaps_run]
  change transform C C (exchange E (transform C⁻¹ C⁻¹ s)) = _
  rw [Cover.Weighted.exchange_conj _ _ _ (C.mul_nonsing_inv unit), basis, Matrix.mul_assoc,
    C.mul_nonsing_inv unit, Matrix.mul_one, M8.Exchange.exchange_comp _ _ ij]

end IntegerMultBounds.MathlibTM2.M6
