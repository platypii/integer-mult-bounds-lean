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
        ∃ C : Matrix (Fin 8) (Fin 8) R, C.IsLowerTriangular ∧ C⁻¹.IsLowerTriangular ∧
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
  obtain ⟨C, hC, ones, unit, basis⟩ := Nine.triangular_projector_basis U tri
    (M8.Exchange.sub_idempotent _ _ (idem i) (idem j) ij ji)
    (fun k => by rw [entry]; split <;> simp)
  have eq : diagonal (fun k => U k k) = E := congrArg diagonal (funext entry)
  rw [eq] at basis
  let := C.invertibleOfIsUnitDet unit
  refine ⟨C, hC, blockTriangular_inv_of_blockTriangular hC, ones, C.mul_nonsing_inv unit, ?_⟩
  intro s
  simp only [prefixMoveProgram, IntegerMultBounds.Swap.Shear.run_append, intervalSwaps_run]
  change transform C C (exchange E (transform C⁻¹ C⁻¹ s)) = _
  rw [Cover.Weighted.exchange_conj _ _ _ (C.mul_nonsing_inv unit), basis, Matrix.mul_assoc,
    C.mul_nonsing_inv unit, Matrix.mul_one, M8.Exchange.exchange_comp _ _ ij]

end IntegerMultBounds.MathlibTM2.M6
