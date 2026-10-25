module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputHeader
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputClose

/-! # Final output pass with generated and released shift controls -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def outputFromHeaders (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq (outputHeaders 100 101 94 116 115 26 27)
    (.seq (closedOutputWeights hQ) (clearWords [115, 116]))

def outputFromHeadersCost (q b l w M L : ℕ) : ℕ :=
  22 * b + 8 * l + 6 * w + 6 * (b + 2 * l + 2) + 34 +
    closedOutputWeightsCost q (b + 2 * l + 2) w M L

/-- The final pass now requires only ordinary precision, row and width headers.
Generated controls are paid for and released; only the output prefix changes. -/
theorem outputFromHeaders_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q b l w M L : ℕ} (hq : 1 ≤ q) (hquarter : q = 4 * b) (hw : q + (b + 2 * l + 2) + 4 ≤ w)
    (xs : List GaussianInt) (ds : List ℚ) (hlen : xs.length = M * L) (hdslen : ds.length = xs.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 4) (hds : ∀ a ∈ ds, 0 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail borrowed : List (Fin (A + 4)))
    (hc : CClean mul S) (hfresh : ∀ r, S.R (cr r) = [])
    (hhigh : ∀ k ∈ [(114 : Fin 117), 115, 116], S.R k = [])
    (hqR : (S.R 100).length = q) (hlR : (S.R 101).length = l) (hwR : (S.R 94).length = w)
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hsrc : S.R 93 = cstream A w xs ++ tail)
    (htable : S.R 96 = cstream A w (outputWeightWords q ds) ++ borrowed) :
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (weightedOutputNumerators q (b + 2 * l + 2) xs ds) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ outputFromHeadersCost q b l w M L ∧
      Exec body (outputFromHeaders hQ) (mk v S) m (mk v' SF) ∧
      ∀ i (hi : i < xs.length),
        |(value q (decodeWord (((SF.R 93).drop (i * w)).take w))).re -
          (ds[i] : ℝ) * ((2 : ℝ) ^ (b + 2 * l + 2) * (value q xs[i]).re)| ≤
          (2 + (2 : ℝ) ^ (b + 2 * l + 2 + 2)) / (2 : ℝ) ^ q := by
  dsimp only
  let d := b + 2 * l + 2
  let shiftSymbols := tick :: tick :: (S.R 101).reverse ++ (S.R 101).reverse ++ List.replicate b tick
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update S.R 116 shiftSymbols)
    115 ((S.R 94).reverse.drop d)) }
  have h26 : S.R 26 = [] := (hc ⟨26, by decide⟩).2
  have h27 : S.R 27 = [] := (hc ⟨27, by decide⟩).2
  obtain ⟨v₁, hu₁, he₁⟩ := outputHeaders_exec (body := body)
    (precision := 100) (rows := 101) (width := 94) (shift := 116) (rest := 115) (saved := 26) (tmp := 27)
    (by decide) b v S (by omega) (by omega)
    (hhigh 116 (by simp)) (hhigh 115 (by simp)) h26 h27
  have he₁' : Exec body (outputHeaders 100 101 94 116 115 26 27) (mk v S)
      (22 * b + 8 * l + 4 * w + 6 * d + 29) (mk v₁ S₁) := by
    simpa only [hlR, hwR] using he₁
  have hdlen : (S₁.R 116).length = d := by simp [S₁, shiftSymbols, d, hlR]; omega
  have hrlen : (S₁.R 115).length = w - d := by simp [S₁, hwR]
  have hclean : CClean mul S₁ := by
    intro i
    have hi := i.isLt
    have hn (k : Fin 117) (hk : 64 ≤ k.val) : mul i ≠ k := by
      intro he
      have hv := congrArg (fun k : Fin 117 => k.val) he
      simp only [mul] at hv
      omega
    refine ⟨(hc i).1, ?_⟩
    simpa [S₁, hn 115 (by decide), hn 116 (by decide)] using (hc i).2
  have hfr : ∀ r, S₁.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have hn (k : Fin 117) (hk : 96 ≤ k.val) : cr r ≠ k := by
      intro he
      have hv := congrArg (fun k : Fin 117 => k.val) he
      omega
    simpa [S₁, hn 115 (by decide), hn 116 (by decide)] using hfresh r
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, _⟩ := closedOutputWeights_exec (body := body)
    (q := q) (d := d) (w := w) (M := M) (L := L) hQ hA hq hw xs ds hlen hdslen hxs hds
    v₁ S₁ tail borrowed hclean hfr
    (by simpa [S₁] using hhigh 114 (by simp))
    (by simpa [S₁] using hqR) (by simpa [S₁] using hwR) hdlen hrlen
    (by simpa [S₁] using hbatch) (by simpa [S₁] using hrows)
    (by simpa [S₁] using hsrc) (by simpa [S₁] using htable)
  let result := cstream A w (weightedOutputNumerators q d xs ds) ++ tail
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 93 result }
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) [115, 116] (by decide) v₂ S₂
  refine ⟨v₃, (22 * b + 8 * l + 4 * w + 6 * d + 29) + m₂ + (2 * w + 5),
    hu₃.trans (hu₂.trans hu₁), ?_, ?_, ?_⟩
  · unfold outputFromHeadersCost
    dsimp only [d] at *
    omega
  · refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast ?_ ?_
    · have hd : d ≤ w := by dsimp [d]; omega
      have hsum : (S₂.R 115).length + (S₂.R 116).length = w := by
        simpa only [S₂, Function.update_of_ne (by decide : (115 : Fin 117) ≠ 93),
          Function.update_of_ne (by decide : (116 : Fin 117) ≠ 93), hrlen, hdlen] using Nat.sub_add_cancel hd
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
      omega
    · congr 1
      ext1
      · rfl
      · rfl
      · rfl
      funext k
      by_cases h115 : k = (115 : Fin 117)
      · subst k; simp [hhigh 115 (by simp)]
      · by_cases h116 : k = (116 : Fin 117)
        · subst k; simp [hhigh 116 (by simp)]
        · simp [S₂, S₁, result, h115, h116, d, Function.update_apply]

  · intro i hi
    simpa only [Function.update_self] using
      weightedOutputNumerators_word_error (by omega) hw xs ds hdslen.symm hxs hds tail i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
