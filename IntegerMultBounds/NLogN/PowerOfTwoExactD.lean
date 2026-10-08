import IntegerMultBounds.NLogN.PowerOfTwoExact

/-! The exact chain of Theorem 3.1 of Harvey and van der Hoeven for any number
of coordinates. Lengths are written as successors `M i + 1`, so that `ZMod` and
`Fin` agree definitionally. Proved: the additive isomorphism splitting off the
last coordinate; the transport of the normalized `(d+1)`-dimensional complex
convolution along it; and the complete chain: the normalized complex transform
is a chirp multiplication, the untwist of the `d`-dimensional synthetic
pipeline (forward synthetic transforms of the twisted chirp and of the twisted
pre-multiplied input, `1/r`-scaled negacyclic products, inverse synthetic
transform, scaled by `∏_{i<d} (M i + 1)`), and another chirp multiplication.
Fixed-point errors are not treated here. -/

namespace IntegerMultBounds.NLogN

open Complex Real

section Split

variable {d : ℕ}

/-- The lengths of all `d + 1` coordinates. -/
abbrev lenAll (M : Fin (d + 1) → ℕ) : Fin (d + 1) → ℕ := fun i => M i + 1

/-- The lengths of the first `d` coordinates. -/
abbrev lenInit (M : Fin (d + 1) → ℕ) : Fin d → ℕ := fun i => M (Fin.castSucc i) + 1

/-- The length of the last coordinate, the synthetic ring dimension `r`. -/
abbrev lenLast (M : Fin (d + 1) → ℕ) : ℕ := M (Fin.last d) + 1

/-- Split off the last coordinate: the first `d` coordinates and the last one. -/
def splitLast (M : Fin (d + 1) → ℕ) :
    ((i : Fin (d + 1)) → ZMod (M i + 1)) ≃+
      (((i : Fin d) → Fin (lenInit M i)) × Fin (lenLast M)) where
  toFun f := (Fin.init f, f (Fin.last d))
  invFun p := Fin.snoc (α := fun i => ZMod (M i + 1)) p.1 p.2
  left_inv f := Fin.snoc_init_self f
  right_inv p := by
    refine Prod.ext ?_ ?_
    · exact Fin.init_snoc (α := fun i => ZMod (M i + 1)) p.2 p.1
    · exact Fin.snoc_last (α := fun i => ZMod (M i + 1)) p.2 p.1
  map_add' _ _ := rfl

theorem splitLast_apply (M : Fin (d + 1) → ℕ) (f : (i : Fin (d + 1)) → ZMod (M i + 1)) :
    splitLast M f = (Fin.init f, f (Fin.last d)) := rfl

theorem card_init (M : Fin (d + 1) → ℕ) :
    Fintype.card ((i : Fin d) → Fin (lenInit M i)) = ∏ i, lenInit M i := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]

theorem prod_lenAll (M : Fin (d + 1) → ℕ) :
    ∏ i, lenAll M i = (∏ i, lenInit M i) * lenLast M := by
  rw [Fin.prod_univ_castSucc]

/-- The normalized complex convolution on all `d + 1` coordinates is the normalized
convolution on the split index set. -/
theorem convNormD_split (M : Fin (d + 1) → ℕ)
    (u v : ((i : Fin (d + 1)) → ZMod (M i + 1)) → ℂ) (k : (i : Fin (d + 1)) → ZMod (M i + 1)) :
    convNormD (lenAll M) u v k =
      (1 / ((Fintype.card ((i : Fin d) → Fin (lenInit M i)) * lenLast M : ℕ) : ℂ)) *
        convG (u ∘ (splitLast M).symm) (v ∘ (splitLast M).symm) (splitLast M k) := by
  have h := congrFun (convG_comp_symm (splitLast M) u v) (splitLast M k)
  simp only [Function.comp_apply, AddEquiv.symm_apply_apply] at h
  simp only [convNormD]
  rw [← h, card_init, ← prod_lenAll]

end Split

section Chain

variable {d : ℕ}

/-- The exact chain of Theorem 3.1 for `d + 1` even power-of-two coordinates, the
first `d` dividing twice the last: chirp, split, twist, synthetic forward transforms,
scaled negacyclic products, inverse synthetic transform, untwist, chirp. -/
theorem dftNormD_chain (M : Fin (d + 1) → ℕ) (hpow : ∀ i, ∃ f, M i + 1 = 2 ^ f)
    (heven : ∀ i, 2 ∣ M i + 1) (hdiv : ∀ i : Fin d, M (Fin.castSucc i) + 1 ∣ 2 * (M (Fin.last d) + 1))
    (u : ((i : Fin (d + 1)) → ZMod (M i + 1)) → ℂ) :
    dftNormD (lenAll M) u = fun k => (starRingEnd ℂ) (chirpD (lenAll M) k) *
      ofSynth (fun j => ((∏ i, lenInit M i : ℕ) : ℂ) • synthDFTDInv (lenLast M) (lenInit M)
        (fun j => (1 / ((lenLast M : ℕ) : ℂ)) • negacyclicMul
          (synthDFTD (lenLast M) (lenInit M)
            (toSynth (chirpD (lenAll M) ∘ (splitLast M).symm)) j)
          (synthDFTD (lenLast M) (lenInit M)
            (toSynth ((fun j => (starRingEnd ℂ) (chirpD (lenAll M) j) * u j) ∘
              (splitLast M).symm)) j)) j)
        (splitLast M k) := by
  rw [bluesteinD_norm heven]
  funext k
  congr 1
  rw [convNormD_split]
  set a' := chirpD (lenAll M) ∘ (splitLast M).symm with ha'
  set b' := (fun j => (starRingEnd ℂ) (chirpD (lenAll M) j) * u j) ∘ (splitLast M).symm with hb'
  have hc := congrFun (convNorm_prod_eq (G := (i : Fin d) → Fin (lenInit M i)) a' b')
    (splitLast M k)
  refine hc.trans ?_
  congr 1
  have hpow' : ∀ i, ∃ f, lenInit M i = 2 ^ f := fun i => hpow (Fin.castSucc i)
  have h := synthConvNormD_eq (r := lenLast M) (N := lenInit M) hdiv hpow' (toSynth a') (toSynth b')
  have hr0 : ((lenLast M : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hT0 : ((∏ i, lenInit M i : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne _)
  funext j
  have hj := congrFun h j
  calc (1 / ((Fintype.card ((i : Fin d) → Fin (lenInit M i)) * lenLast M : ℕ) : ℂ)) •
        synthConvG (toSynth a') (toSynth b') j
      = (1 / ((lenLast M : ℕ) : ℂ)) • ((1 / ((∏ i, lenInit M i : ℕ) : ℂ)) •
          synthConvG (toSynth a') (toSynth b') j) := by
        rw [smul_smul, card_init]
        congr 1
        push_cast
        field_simp
    _ = (1 / ((lenLast M : ℕ) : ℂ)) • ((((∏ i, lenInit M i : ℕ) : ℂ) * (lenLast M : ℕ)) •
          synthDFTDInv (lenLast M) (lenInit M)
            (fun j => (1 / ((lenLast M : ℕ) : ℂ)) • negacyclicMul
              (synthDFTD (lenLast M) (lenInit M) (toSynth a') j)
              (synthDFTD (lenLast M) (lenInit M) (toSynth b') j)) j) := by
        rw [hj]
    _ = _ := by
        rw [smul_smul]
        congr 1
        field_simp

end Chain

end IntegerMultBounds.NLogN
