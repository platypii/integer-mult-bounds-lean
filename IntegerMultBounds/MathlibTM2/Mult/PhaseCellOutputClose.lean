module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputScale
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightClose

/-! # Executed final output rescaling and similarity multiplication

Only the owned prefix is rescaled. The normalization header is saved while the
existing closed weight pass runs at shift zero, then restored symbol for symbol.
The weight source, borrowed suffix and all private workspace are preserved.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def closedOutputWeights (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq scaleOutputPrefix (.seq (moveR 116 114 id) (.seq (closedWeights hQ) (moveR 114 116 id)))

def closedOutputWeightsCost (q d w M L : ℕ) : ℕ :=
  scaleOutputPrefixCost M L w d + closedWeightsCost q 0 w M L + 4 * d + 4

/-- Restore the cell-output scale and multiply its actual computed words by the
encoded actual similarity weights. Only the persistent output prefix changes. -/
theorem closedOutputWeights_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q d w M L : ℕ} (hq : 1 ≤ q) (hw : q + d + 4 ≤ w)
    (xs : List GaussianInt) (ds : List ℚ) (hlen : xs.length = M * L) (hdslen : ds.length = xs.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 4)
    (hds : ∀ a ∈ ds, 0 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail borrowed : List (Fin (A + 4)))
    (hc : CClean mul S) (hfresh : ∀ r, S.R (cr r) = []) (h114 : S.R 114 = [])
    (hqR : (S.R 100).length = q) (hwR : (S.R 94).length = w)
    (hdR : (S.R 116).length = d) (hrest : (S.R 115).length = w - d)
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hsrc : S.R 93 = cstream A w xs ++ tail)
    (htable : S.R 96 = cstream A w (outputWeightWords q ds) ++ borrowed) :
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (weightedOutputNumerators q d xs ds) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ closedOutputWeightsCost q d w M L ∧
      Exec body (closedOutputWeights hQ) (mk v S) m (mk v' SF) ∧
      ∀ i (hi : i < xs.length),
        |(value q (decodeWord (((SF.R 93).drop (i * w)).take w))).re -
          (ds[i] : ℝ) * ((2 : ℝ) ^ d * (value q xs[i]).re)| ≤
          (2 + (2 : ℝ) ^ (d + 2)) / (2 : ℝ) ^ q := by
  dsimp only
  have h84 : S.R 84 = [] := hfresh .xs
  have hlow (k : Fin 117) (hk : k.val < 64) : S.R k = [] := (hc ⟨k.val, hk⟩).2
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := scaleOutputPrefix_exec (body := body) M L w d (by omega) (by omega)
    xs hlen v S tail hbatch hrows hwR hdR hrest hsrc (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hlow _ (by decide) | exact h84)
  let shifted := xs.map (fun x => (2 : GaussianInt) ^ d * x)
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 93 (cstream A w shifted ++ tail) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body 116 114 (by decide) id v₁ S₁
  let S₂ : Stacks 117 A := { S₁ with R := movedR S₁.R 116 114 id (S₁.R 116) }
  have hclean : CClean mul S₂ := by
    intro i
    have hi := i.isLt
    have hn (k : Fin 117) (hk : 64 ≤ k.val) : mul i ≠ k := by
      intro h
      have he := congrArg (fun k : Fin 117 => k.val) h
      simp only [mul] at he
      omega
    refine ⟨(hc i).1, ?_⟩
    simpa [S₂, S₁, movedR, hn 93 (by decide), hn 114 (by decide), hn 116 (by decide)] using (hc i).2
  have hfresh₂ : ∀ r, S₂.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have hn93 : cr r ≠ (93 : Fin 117) := by intro h; exact hr.2.2.1 (congrArg Fin.val h)
    have hnhigh (k : Fin 117) (hk : 96 ≤ k.val) : cr r ≠ k := by
      intro h
      have he := congrArg (fun k : Fin 117 => k.val) h
      omega
    simpa [S₂, S₁, movedR, hn93, hnhigh 114 (by decide), hnhigh 116 (by decide)] using hfresh r
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃, _⟩ := closedWeights_exec (body := body)
    (q := q) (b := 0) (w := w) (e := d + 2) (f := 0) (M := M) (L := L)
    hQ hA hq (by omega) (by omega) shifted (outputWeightWords q ds)
    (by simp [shifted, hlen]) (by simp [shifted, outputWeightWords, hdslen])
    (by intro x hx; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx; exact scaled_output_norm q d z (hxs z hz))
    (by simpa only [pow_zero] using outputWeightWords_norm q ds hds)
    v₂ S₂ tail borrowed hclean hfresh₂
    (by simpa [S₂, S₁, movedR] using hqR) (by simp [S₂, movedR])
    (by simpa [S₂, S₁, movedR] using hwR)
    (by simpa [S₂, S₁, movedR] using hbatch) (by simpa [S₂, S₁, movedR] using hrows)
    (by simp [S₂, S₁, movedR]) (by simpa [S₂, S₁, movedR] using htable)
  let result := cstream A w (weightedOutputNumerators q d xs ds) ++ tail
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 93 result }
  have he₃' : Exec body (closedWeights hQ) (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    simpa only [S₃, result, weightedOutputNumerators, shifted, Nat.add_zero] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body 114 116 (by decide) id v₃ S₃
  have hsave : (S₁.R 116).length = d := by simpa [S₁] using hdR
  have hrestore : (S₃.R 114).length = d := by simp [S₃, S₂, S₁, movedR, h114, hdR]
  refine ⟨v₄, m₁ + ((2 * d + 2) + (m₃ + (2 * d + 2))), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_, ?_⟩
  · unfold closedOutputWeightsCost
    omega
  · refine (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃' he₄))).cast (by rw [hsave, hrestore]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk114 : k = (114 : Fin 117)
    · subst k; simp [S₃, S₂, S₁, movedR, h114]
    · by_cases hk116 : k = (116 : Fin 117)
      · subst k; simp [S₃, S₂, S₁, movedR, h114]
      · by_cases hk93 : k = (93 : Fin 117)
        · subst k; simp [S₃, S₂, S₁, movedR, result]
        · simp [S₃, S₂, S₁, movedR, hk114, hk116, hk93]
  · intro i hi
    simpa only [Function.update_self] using
      weightedOutputNumerators_word_error (by omega) hw xs ds hdslen.symm hxs hds tail i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
