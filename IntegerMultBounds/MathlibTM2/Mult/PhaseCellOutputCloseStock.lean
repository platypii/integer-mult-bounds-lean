module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputClose
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputNativeStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightCloseStock

/-! Executed output rescaling and weighting retain shared numerical scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def closedOutputWorkspace (C q d w M L : ℕ) : ℕ :=
  3*scaleOutputPrefixCost M L w d+applyWeightsWorkspace C q 0 M L w+4*d+4

theorem closedOutputWeights_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (htable : S.R 96 = cstream A w (outputWeightWords q ds) ++ borrowed)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C) (depth : ℕ) :
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (weightedOutputNumerators q d xs ds) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ closedOutputWeightsCost q d w M L ∧
      ExecWithin body (fun level z => mnSize z+level ≤ mnSize (mk v S)+depth+closedOutputWorkspace C q d w M L)
        depth (closedOutputWeights hQ) (mk v S) m (mk v' SF) ∧
      ∀ i (hi : i < xs.length),
        |(value q (decodeWord (((SF.R 93).drop (i * w)).take w))).re -
          (ds[i]'(by rw [hdslen]; exact hi) : ℝ) * ((2 : ℝ) ^ d * (value q (xs[i]'hi)).re)| ≤
          (2 + (2 : ℝ) ^ (d + 2)) / (2 : ℝ) ^ q := by
  dsimp only
  obtain ⟨vf,nf,huf,hnf,hef,herr⟩ := closedOutputWeights_exec (body := body) hQ hA hq hw
    xs ds hlen hdslen hxs hds v S tail borrowed hc hfresh h114 hqR hwR hdR hrest hbatch hrows hsrc htable
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
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃, _⟩ := closedWeights_exec_within (body := body)
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
    C hpush depth
  let result := cstream A w (weightedOutputNumerators q d xs ds) ++ tail
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 93 result }
  have he₃' : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₂ S₂)+depth+applyWeightsWorkspace C q 0 M L w) depth (closedWeights hQ) (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    simpa only [S₃, result, weightedOutputNumerators, shifted, Nat.add_zero] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body 114 116 (by decide) id v₃ S₃
  have hsave : (S₁.R 116).length = d := by simpa [S₁] using hdR
  have hrestore : (S₃.R 114).length = d := by simp [S₃, S₂, S₁, movedR, h114, hdR]
  have hmove (x y : Fin 117) : mnNativePushBound 1
      (moveR (P := P) (Q := Q) (A := A) (U := U) x y id) := by
    simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₁ := mn_native_exec_within he₁ 3 scaleOutputPrefix_native depth
    (mnSize (mk v S)+depth+3*scaleOutputPrefixCost M L w d)
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm₁) _)
  have ht₂ := mn_native_exec_within he₂ 1 (hmove 116 114) depth _ (Nat.le_refl _)
  have ht₄ := mn_native_exec_within he₄ 1 (hmove 114 116) depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add ht₂ (mn_seq_within_add he₃' ht₄))
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  refine ⟨vf,nf,huf,hnf,ht.mono ?_,herr⟩
  intro d' z hz
  simp only [Nat.one_mul] at hz
  rw [hsave,hrestore] at hz
  dsimp only [closedOutputWorkspace]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
