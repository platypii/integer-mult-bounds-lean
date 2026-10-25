module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUpperCrop
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPadding

/-! # Compaction with a generated ring-row symbol count

The zero skip header is a fresh empty word. Padding against that empty header
constructs 2^l*w; after selection the counter is released. No prepared row-symbol
count is supplied to this caller.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.ToeplitzInverse

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Generate the record count, select the upper prefix and release the generated word. -/
def upperCropFromDimensions
    (lR batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp dst : Fin T) :
    Pr P T Q A U :=
  .seq (padding lR wordR skip recordSymbols buf tmp)
    (.seq (correlationBatch batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols
      src acc current savedSource saved buf tmp dst) (uclear recordSymbols))

/-- Complete counter generation and cleanup around the actual compaction loop. -/
theorem upperCropFromDimensions_exec
    {lR dst batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [lR, dst, batch, batchSaved, skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    {q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hl : (S.R lR).length = l) (hbatch : (S.R batch).length = M)
    (hsrc : S.R src = cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail)
    (hskip : S.R skip = []) (hm : (S.R mR).length = L) (hword : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [recordSymbols, batchSaved, acc, savedSource, savedSkip, recordSaved, current, saved, buf, tmp],
      S.R k = []) :
    let SF := { S with R := (Function.update S.R dst
      (cstream A w (upperRows q l M L X V) ++ S.R dst)) }
    ∃ v' n, v'.user = v.user ∧
      n ≤ M * (20 * L * w + 19 * L + 6 * 2 ^ l * w + 23) +
        4 * w + 6 * 2 ^ l * w + 9 * l + 22 ∧
      Exec body (upperCropFromDimensions lR batch batchSaved skip savedSkip mR recordSaved wordR
        recordSymbols src acc current savedSource saved buf tmp dst) (mk v S) n (mk v' SF) ∧
      ∀ j < M, ∀ i : Fin L,
        ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
            (((SF.R dst).drop ((j * L + i.val) * w)).take w)) -
          upper L (fun k => value q (block (X j) k)) (fun k => value q (block (V j) k)) i.val‖ ≤
            2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  dsimp only
  have hcrop := (List.nodup_cons.mp hreg).2
  have hreg' := hreg
  regs_ne hreg'
  have hc : S.R recordSymbols = [] := hclean recordSymbols (by simp)
  have hcd : recordSymbols ≠ dst := ‹dst ≠ recordSymbols›.symm
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := padding_exec (body := body)
    (show [lR, wordR, skip, recordSymbols, buf, tmp].Nodup by simp_all [ne_comm])
    v S hc (hclean buf (by simp)) (hclean tmp (by simp))
  let S₁ : Stacks T A := { S with R := Function.update S.R recordSymbols (List.replicate (2 ^ l * w) tick) }
  have he₁' : Exec body (padding lR wordR skip recordSymbols buf tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hl, hword, hskip, List.length_nil, Nat.sub_zero] using he₁
  have off (k : Fin T) (hk : k ≠ recordSymbols) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, hu₂, he₂, herr⟩ := upper_crop_exec (body := body) hcrop hA hw hpad X V
    hlenX hlenV hX hV v₁ S₁ tail
    (by rw [off _ ‹batch ≠ recordSymbols›]; exact hbatch)
    (by rw [off _ ‹recordSymbols ≠ src›.symm]; exact hsrc)
    (by rw [off _ ‹skip ≠ recordSymbols›]; exact hskip)
    (by rw [off _ ‹mR ≠ recordSymbols›]; exact hm)
    (by rw [off _ ‹wordR ≠ recordSymbols›]; exact hword)
    (by simp [S₁]) (by
      intro k hk
      have hne : k ≠ recordSymbols := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [off k hne]
      exact hclean k (List.mem_cons_of_mem recordSymbols hk))
  let S₂ : Stacks T A := { S₁ with R := (Function.update S₁.R dst
    (cstream A w (upperRows q l M L X V) ++ S₁.R dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec (body := body) recordSymbols v₂ S₂
  have hlen : (S₂.R recordSymbols).length = 2 ^ l * w := by simp [S₂, S₁, hcd]
  refine ⟨v₃, n₁ + (M * (20 * L * w + 19 * L + 6 * 2 ^ l * w + 23) + 8 +
      (2 * (2 ^ l * w) + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_, ?_⟩
  · rw [hl, hword, hskip] at hn₁
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hn₁
    nlinarith only [hn₁]
  · refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hlen]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = recordSymbols
    · subst k
      simp [S₂, S₁, hc, hcd]
    · by_cases hd : k = dst
      · subst k
        simp [S₂, S₁, hk]
      · simp [S₂, S₁, hk, hd]
  · simpa only [Function.update_self, off dst ‹dst ≠ recordSymbols›] using herr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
