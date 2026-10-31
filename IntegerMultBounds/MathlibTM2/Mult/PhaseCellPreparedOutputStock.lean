module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOutput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputFromHeadersStock

/-! The borrowed output page is fetched, used and retired in the actual bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def preparedOutputWorkspace (C q b l w M L : ℕ) : ℕ :=
  3*fetchOutputTableCost M L w+outputFromHeadersWorkspace C q b l w M L

theorem preparedOutput_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (htable : S.R 110 = pre ++ (cstream A w (outputWeightWords q ds) ++ borrowed))
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C) (depth : ℕ) :
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (weightedOutputNumerators q (b + 2 * l + 2) xs ds) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ preparedOutputCost q b l w M L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+preparedOutputWorkspace C q b l w M L)
        depth (preparedOutput hQ) (mk v S) m (mk v' SF) ∧
      ∀ i (hi : i < xs.length),
        |(value q (decodeWord (((SF.R 93).drop (i * w)).take w))).re -
          (ds[i]'(by rw [hdslen]; exact hi) : ℝ) * ((2 : ℝ) ^ (b + 2 * l + 2) * (value q (xs[i]'hi)).re)| ≤
          (2 + (2 : ℝ) ^ (b + 2 * l + 2 + 2)) / (2 : ℝ) ^ q := by
  dsimp only
  obtain ⟨vf,nf,huf,hnf,hef,herrf⟩ := preparedOutput_exec (body := body) hQ hA hq hquarter hw
    xs ds hlen hdslen hxs hds v S tail pre borrowed hc hfresh hhigh hpre hqR hlR hwR hbatch hrows hsrc htable
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
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, herr⟩ := outputFromHeaders_exec_within (body := body)
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
    C hpush depth
  let result := cstream A w (weightedOutputNumerators q (b + 2 * l + 2) xs ds) ++ tail
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 93 result }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 96 v₂ S₂
  have ht₁ := mn_native_exec_within he₁ 3 fetchOutputTable_native depth
    (mnSize (mk v S)+depth+3*fetchOutputTableCost M L w)
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm₁) _)
  have ht₃ := mn_native_exec_within he₃ 0
    (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add he₂ ht₃)
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  refine ⟨vf,nf,huf,hnf,ht.mono ?_,herrf⟩
  intro d z hz
  simp only [Nat.zero_mul,Nat.add_zero] at hz
  exact hz

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
