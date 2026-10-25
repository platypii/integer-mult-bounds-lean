module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputFromHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFetchOutputTable

/-! # Complete output stage borrowing its table from the retained setup page -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def preparedOutput (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq fetchOutputTable (.seq (outputFromHeaders hQ) (uclear 96))

def preparedOutputCost (q b l w M L : ℕ) : ℕ :=
  fetchOutputTableCost M L w + outputFromHeadersCost q b l w M L + 2 * (M * L * w) + 2

theorem preparedOutput_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q b l w M L : ℕ} (hq : 1 ≤ q) (hquarter : q = 4 * b) (hw : q + (b + 2 * l + 2) + 4 ≤ w)
    (xs : List GaussianInt) (ds : List ℚ) (hlen : xs.length = M * L) (hdslen : ds.length = xs.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 4) (hds : ∀ a ∈ ds, 0 ≤ (a : ℝ) ∧ (a : ℝ) ≤ 1)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail pre borrowed : List (Fin (A + 4)))
    (hc : CClean mul S) (hfresh : ∀ r, S.R (cr r) = [])
    (hhigh : ∀ k ∈ [(96 : Fin 117), 112, 114, 115, 116], S.R k = [])
    (hpre : pre.length = 2 * (M * L * w) + w)
    (hqR : (S.R 100).length = q) (hlR : (S.R 101).length = l) (hwR : (S.R 94).length = w)
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hsrc : S.R 93 = cstream A w xs ++ tail)
    (htable : S.R 110 = pre ++ (cstream A w (outputWeightWords q ds) ++ borrowed)) :
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (weightedOutputNumerators q (b + 2 * l + 2) xs ds) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ preparedOutputCost q b l w M L ∧
      Exec body (preparedOutput hQ) (mk v S) m (mk v' SF) ∧
      ∀ i (hi : i < xs.length),
        |(value q (decodeWord (((SF.R 93).drop (i * w)).take w))).re -
          (ds[i] : ℝ) * ((2 : ℝ) ^ (b + 2 * l + 2) * (value q xs[i]).re)| ≤
          (2 + (2 : ℝ) ^ (b + 2 * l + 2 + 2)) / (2 : ℝ) ^ q := by
  dsimp only
  have hlow (k : Fin 117) (hk : k.val < 64) : S.R k = [] := (hc ⟨k.val, hk⟩).2
  have htablelen : (cstream A w (outputWeightWords q ds)).length = M * L * w := by
    simp [outputWeightWords, hdslen, hlen]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := fetchOutputTable_exec (body := body)
    M L w pre (cstream A w (outputWeightWords q ds)) borrowed v S (by omega) hrows hwR hpre htablelen htable (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hlow _ (by decide) | exact hhigh _ (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 96 (cstream A w (outputWeightWords q ds)) }
  have hclean : CClean mul S₁ := by
    intro i
    have hi := i.isLt
    have hn : mul i ≠ (96 : Fin 117) := by
      intro he
      have hv := congrArg (fun k : Fin 117 => k.val) he
      simp only [mul] at hv
      omega
    exact ⟨(hc i).1, by simpa [S₁, hn] using (hc i).2⟩
  have hfr : ∀ r, S₁.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have hn : cr r ≠ (96 : Fin 117) := by
      intro he
      have hv := congrArg (fun k : Fin 117 => k.val) he
      omega
    simpa [S₁, hn] using hfresh r
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, herr⟩ := outputFromHeaders_exec (body := body)
    hQ hA hq hquarter hw xs ds hlen hdslen hxs hds v₁ S₁ tail [] hclean hfr
    (by
      intro k hk
      have hn : k ≠ (96 : Fin 117) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> decide
      simpa [S₁, hn] using hhigh k (by simp_all))
    (by simpa [S₁] using hqR) (by simpa [S₁] using hlR) (by simpa [S₁] using hwR)
    (by simpa [S₁] using hbatch) (by simpa [S₁] using hrows) (by simpa [S₁] using hsrc)
    (by simp [S₁])
  let result := cstream A w (weightedOutputNumerators q (b + 2 * l + 2) xs ds) ++ tail
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 93 result }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 96 v₂ S₂
  have h96 : (S₂.R 96).length = M * L * w := by simpa [S₂, S₁] using htablelen
  refine ⟨v₃, m₁ + (m₂ + (2 * (M * L * w) + 2)), hu₃.trans (hu₂.trans hu₁),
    by unfold preparedOutputCost; omega, ?_, ?_⟩
  · refine (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [h96]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = (96 : Fin 117)
    · subst k; simp [hhigh 96 (by simp)]
    · simp [S₂, S₁, result, Function.update_apply, hk]
  · intro i hi
    simpa only [Function.update_self] using herr i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
