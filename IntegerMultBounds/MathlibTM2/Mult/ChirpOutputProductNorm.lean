module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputNormalizeExec

/-! # Norm of the executed E-product stream -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast

theorem norm_chirpOutputEProduct (q l : ℕ) (c : GaussianInt) (e : ℤ)
    (hc : ‖value (q + 1) c‖ ≤ 1) (he : |(e : ℝ) / 2 ^ q| ≤ 2) :
    ‖value q (chirpOutputEProduct q l c e)‖ ≤ 8 * (2 : ℝ) ^ l := by
  exact (norm_value_real_product q _ e _ _ (norm_chirpScaledCorrelation q l c hc)
    he (by norm_num)).trans_eq (by ring)

/-- A structural row lemma supplies normalization's input bound for every emitted product. -/
theorem chirpOutputERow_norm (q l : ℕ) (xs : List GaussianInt) (es : List ℤ)
    (hx : ∀ c ∈ xs, ‖value (q + 1) c‖ ≤ 1) (he : ∀ e ∈ es, |(e : ℝ) / 2 ^ q| ≤ 2) :
    ∀ z ∈ List.zipWith (chirpOutputEProduct q l) xs es, ‖value q z‖ ≤ 8 * (2 : ℝ) ^ l := by
  induction xs generalizing es with
  | nil => simp
  | cons x xs ih =>
    cases es with
    | nil => simp
    | cons e es =>
      intro z hz
      simp only [List.zipWith_cons_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact norm_chirpOutputEProduct q l x e (hx x (by simp)) (he e (by simp))
      · exact ih es (fun c hc => hx c (List.mem_cons_of_mem x hc))
          (fun a ha => he a (List.mem_cons_of_mem e ha)) z hz

/-- The complete first-stage output satisfies the next executed stage's precondition. -/
theorem chirpOutputEBlocks_norm (q l : ℕ) (blocks : List (List GaussianInt)) (es : List ℤ)
    (hx : ∀ c ∈ blocks.flatten, ‖value (q + 1) c‖ ≤ 1) (he : ∀ e ∈ es, |(e : ℝ) / 2 ^ q| ≤ 2) :
    ∀ z ∈ blocks.flatMap (fun xs => List.zipWith (chirpOutputEProduct q l) xs es),
      ‖value q z‖ ≤ 8 * (2 : ℝ) ^ l := by
  intro z hz
  obtain ⟨xs, hxs, hz⟩ := List.mem_flatMap.mp hz
  exact chirpOutputERow_norm q l xs es
    (fun c hc => hx c (List.mem_flatten.mpr ⟨xs, hxs, hc⟩)) he z hz

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
