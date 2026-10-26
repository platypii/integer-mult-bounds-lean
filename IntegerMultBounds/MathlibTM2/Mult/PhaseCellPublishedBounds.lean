module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedAccuracy

/-! Magnitudes of the actual published integer numerators. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

def interiorOutputExponent (p l target rhsExp : ℕ) : ℕ :=
  executionExponent p l target rhsExp+2*l+4

theorem weightedOutputNumerator_norm (q d : ℕ) (z : GaussianInt) (a : ℚ)
    (hz : ‖value q z‖ ≤ 4) (ha0 : 0 ≤ (a : ℝ)) (ha1 : (a : ℝ) ≤ 1) :
    ‖value q (weightedOutputNumerator q d z a)‖ ≤ (2 : ℝ)^(d+2) := by
  have h := normalized_product_norm q 0 (d+2) 0 ((2 : GaussianInt)^d*z) (rationalWord q a)
    (scaled_output_norm q d z hz) (by simpa using output_weight_norm q a ha0 ha1)
  simpa only [weightedOutputNumerator,Nat.add_zero,pow_zero,div_one] using h

theorem weightedOutputNumerators_norm (q d : ℕ) (xs : List GaussianInt) (ds : List ℚ)
    (hlen : xs.length = ds.length) (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 4)
    (hds : ∀ a ∈ ds, 0 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1) :
    ∀ z ∈ weightedOutputNumerators q d xs ds, ‖value q z‖ ≤ (2 : ℝ)^(d+2) := by
  induction xs generalizing ds with
  | nil => simp [weightedOutputNumerators]
  | cons x xs ih =>
    cases ds with
    | nil => simp at hlen
    | cons a ds =>
      intro z hz
      simp only [weightedOutputNumerators,outputWeightWords,List.map_cons,List.zipWith_cons_cons,List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact weightedOutputNumerator_norm q d x a (hxs x (by simp)) (hds a (by simp)).1 (hds a (by simp)).2
      · exact ih ds (by simpa using hlen) (fun x hx => hxs x (by simp [hx]))
          (fun a ha => hds a (by simp [ha])) z hz

theorem publishedWords_mem {K : Type*} (M L : ℕ) (xs : List K) (hlen : xs.length = M*L)
    (z : K) (hz : z ∈ publishedWords M L xs) : z ∈ xs := by
  obtain ⟨row,hrow,hz⟩ := List.mem_flatMap.mp hz
  rw [← (outputRows_spec M L xs hlen).1]
  exact List.mem_flatten.mpr ⟨row,hrow,List.mem_reverse.mp hz⟩

theorem publishedOutputWords_norm {s t p u l M L target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hL : 0 < L)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hpad : L+L ≤ 2^l+1) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < M, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp) :
    let q := executionPrecision p l target rhsExp
    let stage := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    ∀ z ∈ publishedWords M L (executedOutputWords s t p u q l M L stage cExp lo C),
      ‖value q z‖ ≤ (2 : ℝ)^interiorOutputExponent p l target rhsExp := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let inner := executedInteriorWords s t p u q l M L (executionStagePrecision p l target rhsExp) cExp lo C
  let table := executedOutputTable s t p u M L lo
  have hinner : ∀ z ∈ inner, ‖value q z‖ ≤ 4 :=
    executedInteriorWords_norm hp (NeZero.pos s) hst.le hu hL
      (by dsimp [q,executionPrecision,executionExponent,inputExponent,sourceExponent]; omega)
      hαu hθ hgap hbudget hpad lo C (by
        intro n hn k
        exact (hC n hn k).trans (pow_le_pow_right₀ (by norm_num) (by dsimp [cExp,sourceExponent]; omega)))
  have htable : ∀ a ∈ table, 0 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1 := by
    intro a ha
    change a ∈ List.ofFn (fun i : Fin (M*L) => weightData s t p u (lo (i.val/L)) (L-1-i.val%L)) at ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    have h := weightData_bounds hp (NeZero.pos s) hαu hθ hgap hbudget (lo (i.val/L)) (L-1-i.val%L)
    exact ⟨(lt_of_lt_of_le (by positivity) h.1).le,h.2⟩
  intro z hz
  have hz' := publishedWords_mem M L _ (executedOutputWords_length ..) z hz
  have h := weightedOutputNumerators_norm q (inputExponent p cExp+2*l+2) inner table
    (by simp [inner,table,executedOutputTable]) hinner htable z hz'
  simpa only [interiorOutputExponent,executionExponent,cExp,Nat.add_assoc] using h

theorem interiorOutput_width (p l target rhsExp : ℕ) :
    executionPrecision p l target rhsExp+interiorOutputExponent p l target rhsExp+2 ≤
      executionWidth p l target rhsExp := by
  simpa only [interiorOutputExponent,executionExponent,Nat.add_assoc] using execution_width_bound p l target rhsExp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
