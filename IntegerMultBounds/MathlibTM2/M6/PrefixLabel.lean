module

public import IntegerMultBounds.MathlibTM2.M8.Height
public import IntegerMultBounds.MathlibTM2.M6.PrefixFrame
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.All

/-! The modular prefix projection fixes the entire translated PR589 label. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Shared50ModularControl

private def translate : Geometry.Address →ₗ[ℚ] Geometry.Address :=
  (Matrix.of fun (j k : Fin 8) => (k.val.choose j.val : ℚ) * 2 ^ (k.val - j.val)).mulVecLin

private theorem translate_root (line : Fin 111) :
    translate (Geometry.root line.val) = fun j => (translatedEntry line j.val : ℚ) := by
  have check : ∀ l : Fin 111, ∀ j : Fin 8,
      translate (Geometry.root l.val) j = (translatedEntry l j.val : ℚ) := by decide +kernel
  exact funext (check line)

/-- Every generator of a label is a rational combination of any full set of its
generators with nonsingular translated prefix. -/
theorem translated_label_span {label d : ℕ} (hd : d ≤ 8)
    (dimension : Module.finrank ℚ (Geometry.label label) = d) (lines : Fin d → Fin 111)
    (members : ∀ i, (lines i).val ∈ Frames.labels label) :
    let G : Matrix (Fin d) (Fin 8) ℤ := of fun i j => translatedEntry (lines i) j.val
    let A := G.submatrix id (Fin.castLE hd)
    A.det ≠ 0 → ∀ line : Fin 111, line.val ∈ Frames.labels label →
      ∃ a : Fin d → ℚ, a ᵥ* G.map (Int.castRingHom ℚ) = fun j => (translatedEntry line j.val : ℚ) := by
  intro G A nz line member
  let row := fun i => translate (Geometry.root (lines i).val)
  have ratDet : (A.map (Int.castRingHom ℚ)).det ≠ 0 := by
    change ((Int.castRingHom ℚ).mapMatrix A).det ≠ 0
    rw [← RingHom.map_det]
    change (A.det : ℚ) ≠ 0
    exact_mod_cast nz
  let restrict : Geometry.Address →ₗ[ℚ] (Fin d → ℚ) :=
    LinearMap.pi fun i => LinearMap.proj (R := ℚ) (i.castLE hd)
  have indep : LinearIndependent ℚ row := by
    apply LinearIndependent.of_comp restrict
    have eq : restrict ∘ row = (A.map (Int.castRingHom ℚ)).row := by
      funext i j
      exact congrFun (translate_root (lines i)) (j.castLE hd)
    rw [eq]
    exact linearIndependent_rows_of_det_ne_zero ratDet
  have sub : Submodule.span ℚ (Set.range row) ≤ (Geometry.label label).map translate := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨_, Geometry.root_mem _ _ (members i), rfl⟩
  have equal := Submodule.eq_of_le_of_finrank_le sub (by
    rw [finrank_span_eq_card indep, Fintype.card_fin, ← dimension]
    exact Submodule.finrank_map_le _ _)
  have mem : translate (Geometry.root line.val) ∈ Submodule.span ℚ (Set.range row) :=
    equal ▸ ⟨_, Geometry.root_mem _ _ member, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp mem
  refine ⟨a, ?_⟩
  funext j
  simpa [row, translate_root, Finset.sum_apply, vecMul, dotProduct, G] using congrFun ha j

private theorem reduce_fraction {m : ℕ} (n d : ℤ) (nz : d ≠ 0)
    (unit : IsUnit (d : ZMod m)) (z : ZMod m) (scaled : (d : ZMod m) * z = n) :
    let q := Rat.divInt n d
    q.den.Coprime m ∧ z = Swap.Modular.ratMod m q := by
  intro q
  obtain ⟨k,hk⟩ := Rat.den_dvd n d
  have factors : (d : ZMod m) = (q.den : ZMod m) * (k : ZMod m) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (Int.cast : ℤ → ZMod m) hk
  have cop := (ZMod.isUnit_iff_coprime q.den m).mp
    (isUnit_of_mul_isUnit_left (factors ▸ unit))
  refine ⟨cop, Swap.Modular.ratMod_unique m cop ?_⟩
  have eq : (q.num : ℤ) * d = n * q.den := by
    have h := Rat.mul_den_eq_num q
    change (Rat.divInt n d) * _ = _ at h
    rw [Rat.divInt_eq_div] at h
    have hd : (d : ℚ) ≠ 0 := by exact_mod_cast nz
    field_simp [hd] at h
    exact_mod_cast (by linarith only [h] : (q.num : ℚ) * d = n * q.den)
  apply unit.mul_left_cancel
  calc
    _ = ((d : ZMod m) * z) * q.den := (mul_assoc ..).symm
    _ = _ := by
      rw [scaled, mul_comm (d : ZMod m)]
      simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (Int.cast : ℤ → ZMod m) eq.symm

/-- Every translated generator listed for the label is reconstructed from its
dimension-many prefix coordinates over every tape radix. -/
theorem label_interpolation (label : ℕ) (live : label < 636) :
    let d := Geometry.Dimensions.value label
    ∃ (hd : d ≤ 8) (chart : Matrix (Fin d) (Fin 8) ℚ),
      (∀ i j, M8.Height.ht (chart i j) ≤ 2^100) ∧ ∀ w : ℕ, let R := ZMod (prime ^ w)
      ∃ B : Matrix (Fin d) (Fin 8) R,
        (∀ i j, (chart i j).den.Coprime (prime ^ w) ∧ B i j = Swap.Modular.ratMod (prime ^ w) (chart i j)) ∧
        B.submatrix id (Fin.castLE hd) = 1 ∧
        (∃ (lines : Fin d → Fin 111) (C : Matrix (Fin d) (Fin d) R),
          (∀ i, (lines i).val ∈ Frames.labels label) ∧
          B = C * of fun i j => (translatedEntry (lines i) j.val : R)) ∧
        ∀ line : Fin 111, line.val ∈ Frames.labels label →
          (fun i : Fin d => (translatedEntry line i.val : R)) ᵥ* B =
            fun j => (translatedEntry line j.val : R) := by
  intro d
  have bounded : ∀ i : Fin 636, Geometry.Dimensions.value i.val ≤ 8 := by decide +kernel
  let hd : d ≤ 8 := bounded ⟨label, live⟩
  obtain ⟨lines, members, units⟩ := prefix_witness label live
  let G : Matrix (Fin d) (Fin 8) ℤ := of fun i j => translatedEntry (lines i) j.val
  let A := G.submatrix id (Fin.castLE hd)
  have nz : A.det ≠ 0 := by
    let : Fact prime.Prime := ⟨prime_prime⟩
    have unit : IsUnit ((Int.castRingHom (ZMod prime)).mapMatrix A) := by
      have h : IsUnit ((Int.castRingHom (ZMod (prime ^ 1))).mapMatrix A) := units 1
      rwa [pow_one] at h
    have h := (isUnit_iff_isUnit_det _).mp unit
    rw [← RingHom.map_det] at h
    exact fun zero => h.ne_zero (by rw [zero, map_zero])
  refine ⟨hd, fun i j => Rat.divInt ((A.adjugate * G) i j) A.det, ?_, ?_⟩
  · intro i j
    apply (M8.Height.ht_divInt _ _ nz).trans
    apply max_le
    · change ((A.adjugate *ᵥ (fun k => G k j)) i).natAbs ≤ _
      rw [← cramer_eq_adjugate_mulVec, cramer_apply]
      apply prefix_det_bound hd
      intro k l
      rw [updateCol_apply]
      split
      · exact translatedEntry_bound _ _
      · exact translatedEntry_bound _ _
    · exact prefix_det_bound hd A fun _ _ => translatedEntry_bound _ _
  intro w R
  let M := G.map (Int.castRingHom R)
  let P := A.map (Int.castRingHom R)
  have detUnit : IsUnit P.det := (isUnit_iff_isUnit_det P).mp (units w)
  have reconstruct : P * (P⁻¹ * M) = M := by rw [← Matrix.mul_assoc, P.mul_nonsing_inv detUnit, Matrix.one_mul]
  let f := Int.castRingHom R
  have detEq : (A.det : R) = P.det := f.map_det A
  have scaled : (A.det : R) • (P⁻¹ * M) = (A.adjugate * G).map f := by
    calc
      _ = P.adjugate * (P * (P⁻¹ * M)) := by
        rw [← Matrix.mul_assoc P.adjugate P, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul, detEq]
      _ = _ := by
        rw [reconstruct]
        change (f.mapMatrix A).adjugate * G.map f = _
        rw [← f.map_adjugate A]
        exact (Matrix.map_mul (f := f)).symm
  refine ⟨P⁻¹ * M, (fun i j => reduce_fraction _ _ nz (detEq ▸ detUnit) _ (congrFun (congrFun scaled i) j)), P.nonsing_inv_mul detUnit, ⟨lines, P⁻¹, members, rfl⟩, ?_⟩
  intro line member
  apply prefix_fixed_of_rational_span hd G (fun i j => translatedEntry_bound (lines i) j)
    (fun j => translatedEntry line j.val) _ w _ nz reconstruct
  exact translated_label_span hd (Geometry.Dimensions.dimension label live) lines members nz line member

/-- For nested labels, projecting in either order returns the projection to the smaller
label. The larger projector fixes each generator of the smaller one, and the larger
prefix contains every coordinate read by the smaller projector. -/
theorem nested_prefix_interpolation {d e : ℕ} (de : d ≤ e) (he : e ≤ 8) (w : ℕ)
    (lines : Fin d → Fin 111) (C : Matrix (Fin d) (Fin d) (ZMod (prime ^ w)))
    (B : Matrix (Fin e) (Fin 8) (ZMod (prime ^ w))) (normalized : B.submatrix id (Fin.castLE he) = 1) :
    let R := ZMod (prime ^ w)
    let G : Matrix (Fin d) (Fin 8) R := of fun i j => (translatedEntry (lines i) j.val : R)
    let small := fun x : Fin 8 → R => (x ∘ Fin.castLE (de.trans he)) ᵥ* (C * G)
    let large := fun x : Fin 8 → R => (x ∘ Fin.castLE he) ᵥ* B
    (∀ i, large (G i) = G i) → ∀ x, large (small x) = small x ∧ small (large x) = small x := by
  intro R G small large fixes x
  have rows : G.submatrix id (Fin.castLE he) * B = G := by
    ext i j
    exact congrFun (fixes i) j
  let v := x ∘ Fin.castLE (de.trans he)
  have commute : small x = (v ᵥ* C) ᵥ* G := (vecMul_vecMul v C G).symm
  constructor
  · rw [commute]
    change ((v ᵥ* C) ᵥ* G.submatrix id (Fin.castLE he)) ᵥ* B = _
    rw [vecMul_vecMul, rows]
  · have prefixEq : large x ∘ Fin.castLE he = x ∘ Fin.castLE he := by
      change (x ∘ Fin.castLE he) ᵥ* B.submatrix id (Fin.castLE he) = _
      rw [normalized, vecMul_one]
    exact congrArg (fun y : Fin d → R => y ᵥ* (C * G))
      (congrArg (fun y : Fin e → R => y ∘ Fin.castLE de) prefixEq)

/-- Matrix of interpolation from the first `d` coordinates, acting on column vectors. -/
def prefixProjector {R : Type*} [CommRing R] {d : ℕ} (hd : d ≤ 8)
    (B : Matrix (Fin d) (Fin 8) R) : Matrix (Fin 8) (Fin 8) R :=
  Bᵀ * (1 : Matrix (Fin 8) (Fin 8) R).submatrix (Fin.castLE hd) id

theorem prefixProjector_mulVec {R : Type*} [CommRing R] {d : ℕ} (hd : d ≤ 8)
    (B : Matrix (Fin d) (Fin 8) R) (x : Fin 8 → R) :
    prefixProjector hd B *ᵥ x = (x ∘ Fin.castLE hd) ᵥ* B := by
  rw [prefixProjector, ← mulVec_mulVec, mulVec_transpose]
  congr 1
  exact congrArg (fun y : Fin 8 → R => y ∘ Fin.castLE hd) (one_mulVec x)

theorem prefixProjector_entry {R : Type*} [CommRing R] {d : ℕ} (hd : d ≤ 8)
    (B : Matrix (Fin d) (Fin 8) R) (i j : Fin 8) :
    prefixProjector hd B i j = if h : j.val < d then B ⟨j.val, h⟩ i else 0 := by
  classical
  simp only [prefixProjector, Matrix.mul_apply, transpose_apply, submatrix_apply]
  split
  next h =>
    let k : Fin d := ⟨j.val, h⟩
    rw [Finset.sum_eq_single k]
    · simp [k, Matrix.one_apply]
    · intro l _ ne
      have diff : l.castLE hd ≠ j := fun eq => ne (Fin.ext (congrArg (fun t : Fin 8 => t.val) eq))
      exact (congrArg (fun a : R => B l i * a) (Matrix.one_apply_ne (α := R) diff)).trans (mul_zero _)
    · simp
  next h =>
    apply Finset.sum_eq_zero
    intro l _
    have diff : l.castLE hd ≠ j := fun eq => h (congrArg Fin.val eq ▸ l.isLt)
    exact (congrArg (fun a : R => B l i * a) (Matrix.one_apply_ne (α := R) diff)).trans (mul_zero _)

theorem prefixProjector_shape {R : Type*} [CommRing R] {d : ℕ} (hd : d ≤ 8)
    (B : Matrix (Fin d) (Fin 8) R) (normalized : B.submatrix id (Fin.castLE hd) = 1) :
    (∀ i j, i < j → prefixProjector hd B i j = 0) ∧
    ∀ i, prefixProjector hd B i i = if i.val < d then 1 else 0 := by
  have entry (k l : Fin d) : B k (l.castLE hd) = (1 : Matrix (Fin d) (Fin d) R) k l :=
    congrFun (congrFun normalized k) l
  constructor
  · intro i j lt
    rw [prefixProjector_entry]
    split
    next h =>
      let l : Fin d := ⟨i.val, lt_trans lt h⟩
      exact (entry ⟨j.val, h⟩ l).trans (Matrix.one_apply_ne (fun eq => lt.ne (Fin.ext (congrArg Fin.val eq).symm)))
    next => rfl
  · intro i
    rw [prefixProjector_entry]
    split
    next h => simpa [h] using entry ⟨i.val, h⟩ ⟨i.val, h⟩
    next h => simp

/-- The translated generators of one physical label at the machine radix. -/
noncomputable def translatedLabel (w label : ℕ) : Submodule (ZMod (prime^w)) (Fin 8 → ZMod (prime^w)) :=
  Submodule.span _ (Set.range fun l : {l : Fin 111 // l.val ∈ Frames.labels label} =>
    fun j : Fin 8 => (translatedEntry l.val j.val : ZMod (prime^w)))

private theorem prefixProjector_range {w label d : ℕ} (hd : d ≤ 8)
    (B : Matrix (Fin d) (Fin 8) (ZMod (prime^w)))
    (factor : ∃ (lines : Fin d → Fin 111) (C : Matrix (Fin d) (Fin d) (ZMod (prime^w))),
      (∀ i, (lines i).val ∈ Frames.labels label) ∧
      B = C * of fun i j => (translatedEntry (lines i) j.val : ZMod (prime^w)))
    (fixes : ∀ l : Fin 111, l.val ∈ Frames.labels label →
      (fun i : Fin d => (translatedEntry l i.val : ZMod (prime^w))) ᵥ* B =
        fun j => (translatedEntry l j.val : ZMod (prime^w))) :
    LinearMap.range (prefixProjector hd B).mulVecLin = translatedLabel w label := by
  obtain ⟨lines,C,member,fact⟩ := factor
  let G : Matrix (Fin d) (Fin 8) (ZMod (prime^w)) := of fun i j => translatedEntry (lines i) j.val
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    change prefixProjector hd B *ᵥ x ∈ _
    rw [prefixProjector_mulVec, fact, ← vecMul_vecMul]
    have incl : LinearMap.range G.vecMulLinear ≤ translatedLabel w label := by
      rw [range_vecMulLinear]
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨⟨lines i,member i⟩,rfl⟩
    exact incl ⟨_,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨l,rfl⟩
    refine ⟨fun i => (translatedEntry l.val i.val : ZMod (prime^w)),?_⟩
    exact (prefixProjector_mulVec hd B (fun i => (translatedEntry l.val i.val : ZMod (prime^w)))).trans (fixes l.val l.property)

/-- One choice of modular frames for the entire word respects every inclusion of
generator lists, so the choice at a label is independent of the incoming MOVE. -/
theorem compatible_label_frames :
    ∃ chart : (i : Fin 636) → Matrix (Fin (Geometry.Dimensions.value i.val)) (Fin 8) ℚ,
    (∀ l i j, M8.Height.ht (chart l i j) ≤ 2^100) ∧ ∀ w : ℕ, let R := ZMod (prime ^ w)
    ∃ B : (i : Fin 636) → Matrix (Fin (Geometry.Dimensions.value i.val)) (Fin 8) R,
      ∃ bound : ∀ i : Fin 636, Geometry.Dimensions.value i.val ≤ 8,
      let project := fun (i : Fin 636) (x : Fin 8 → R) => (x ∘ Fin.castLE (bound i)) ᵥ* B i
      (∀ l i j, (chart l i j).den.Coprime (prime ^ w) ∧ B l i j = Swap.Modular.ratMod (prime ^ w) (chart l i j)) ∧
      (∀ i, (B i).submatrix id (Fin.castLE (bound i)) = 1) ∧
      (∀ i, LinearMap.range (prefixProjector (bound i) (B i)).mulVecLin = translatedLabel w i.val) ∧
      ∀ i j : Fin 636, (∀ k ∈ Frames.labels i.val, k ∈ Frames.labels j.val) →
        ∀ x, project j (project i x) = project i x ∧ project i (project j x) = project i x := by
  classical
  choose bound chart height frames using fun i : Fin 636 => label_interpolation i.val i.isLt
  refine ⟨chart, height, ?_⟩
  intro w R
  choose B reduced norm factor fixes using fun i : Fin 636 => frames i w
  refine ⟨B, bound, reduced, norm, fun i => prefixProjector_range _ _ (factor i) (fixes i), ?_⟩
  intro i j incl x
  have sub : Geometry.label i.val ≤ Geometry.label j.val := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, rfl⟩
    exact Geometry.root_mem _ _ (incl k hk)
  have de := Submodule.finrank_mono sub
  rw [Geometry.Dimensions.dimension _ i.isLt, Geometry.Dimensions.dimension _ j.isLt] at de
  obtain ⟨lines, C, members, eq⟩ := factor i
  have h := nested_prefix_interpolation de (bound j) w lines C (B j) (norm j)
    (fun k => fixes j (lines k) (incl _ (members k))) x
  simpa only [eq] using h

/-- All modular labels admit lower triangular projectors in the same coordinates.
Both products for a nested pair equal its smaller projector. -/
theorem compatible_label_projectors :
    ∃ Q : Fin 636 → Matrix (Fin 8) (Fin 8) ℚ, (∀ l i j, M8.Height.ht (Q l i j) ≤ 2^100) ∧ ∀ w : ℕ, let R := ZMod (prime ^ w)
    ∃ P : Fin 636 → Matrix (Fin 8) (Fin 8) R,
      (∀ l i j, (Q l i j).den.Coprime (prime ^ w) ∧ P l i j = Swap.Modular.ratMod (prime ^ w) (Q l i j)) ∧
      (∀ l i j, i < j → P l i j = 0) ∧
      (∀ l i, P l i i = if i.val < Geometry.Dimensions.value l.val then 1 else 0) ∧
      (∀ i, LinearMap.range (P i).mulVecLin = translatedLabel w i.val) ∧
      ∀ i j : Fin 636, (∀ k ∈ Frames.labels i.val, k ∈ Frames.labels j.val) →
        P j * P i = P i ∧ P i * P j = P i := by
  obtain ⟨chart, height, frames⟩ := compatible_label_frames
  let Q (l : Fin 636) (i j : Fin 8) : ℚ :=
    if h : j.val < Geometry.Dimensions.value l.val then chart l ⟨j.val,h⟩ i else 0
  refine ⟨Q, ?_, ?_⟩
  · intro l i j
    unfold Q
    split
    · exact height _ _ _
    · simp
  intro w R
  obtain ⟨B, bound, reduced, norm, images, nested⟩ := frames w
  refine ⟨fun i => prefixProjector (bound i) (B i), ?_,
    fun i => (prefixProjector_shape _ _ (norm i)).1,
    fun i => (prefixProjector_shape _ _ (norm i)).2, images, ?_⟩
  · intro l i j
    simp only [prefixProjector_entry, Q]
    split
    · exact reduced _ _ _
    · simp [Swap.Modular.ratMod_zero]
  intro i j incl
  constructor <;> apply Matrix.ext_iff_mulVec.mpr <;> intro x <;>
    simp only [← mulVec_mulVec, prefixProjector_mulVec]
  · exact (nested i j incl x).1
  · exact (nested i j incl x).2

end IntegerMultBounds.MathlibTM2.M6
