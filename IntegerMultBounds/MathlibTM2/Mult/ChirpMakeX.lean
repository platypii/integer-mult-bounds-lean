module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpWeightedExec
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandReverse

/-! # Execute weighted and reversed chirp input operands

Multiply all gathered windows against the generated G table in one traversal, reverse
each row, and erase the temporary weighted stream. Only the final operand tape changes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

noncomputable def chirpMakeX (cr : CR → Fin T) (ι : Fin 64 → Fin T)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (batch batchSaved rowCount recordSaved wordR recordSymbols acc current savedSource saved buf tmp dst : Fin T) :
    Pr P T Q A U :=
  .seq (cmulStream cr (rmulOne ι hι hT hQ cr)) <|
  .seq (reverseRows batch batchSaved rowCount recordSaved wordR recordSymbols
    (cr .out) acc current savedSource saved buf tmp dst) (uclear (cr .out))

def chirpMakeXCost (M m w : ℕ) : ℕ :=
  M * (3 * m + 1) * (rmulCost w + 6 * w + 2) + 8 +
    (M * (26 * (3 * m + 1) * w + 19 * (3 * m + 1) + 17) + 8) +
    (2 * (M * (3 * m + 1) * w) + 2)

/-- All operand arithmetic and reversal execute with exact source/scratch restoration.
The remaining unary counts are explicit caller inputs, not execution oracles. -/
theorem chirpMakeX_exec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {dst batch batchSaved rowCount recordSaved wordR recordSymbols acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, rowCount, recordSaved, wordR, recordSymbols, cr .out,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    {s t α q w m M : ℕ} (hs : 0 < s) (ht : 0 < t) (hα : 0 < α) (hq : 13 ≤ q)
    (hw : q + 3 ≤ w) (hblocks : ∀ n < M, n * m < t)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (ρ : CR → List (Fin (A + 4))) (hr : Ready ρ w q)
    (hX : ρ .xs = cstream A w ((List.range M).flatMap fun n => chirpWindow s t m n u))
    (hY : ρ .ys = chirpBlockStream M (fun n => chirpEntryStream A w (3 * m + 1)
      (fun a => chirpNegativeNumerator false s t α q m (n * m) a)))
    (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = []) (hout : ρ .out = [])
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S) (hS : CHolds cr S ρ)
    (hbatch : (S.R batch).length = M) (hrow : (S.R rowCount).length = 3 * m + 1)
    (hword : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = (3 * m + 1) * w)
    (hclean : ∀ k ∈ [batchSaved, acc, savedSource, recordSaved, current, saved, buf, tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpMakeXCost M m w ∧
      Exec body (chirpMakeX cr ι hι hT hQ batch batchSaved rowCount recordSaved wordR
        recordSymbols acc current savedSource saved buf tmp dst) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w ((List.range M).flatMap fun n =>
            chirpOperandX s t q m n (chirpInputNumerators s t α q m) u) ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hblank : S.R (cr .out) = [] := (hS .out).trans hout
  let words := cstream A w ((List.range M).flatMap fun n =>
    chirpWeighted s t q m n (chirpInputNumerators s t α q m) u)
  let operands := cstream A w ((List.range M).flatMap fun n =>
    chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpWeighted_exec (body := body)
    hcr hdisj hι hT hQ hA hs ht hα hq hw hblocks u hu ρ hr hX hY hxsv hysv hacc v S hc hS
  set S₁ : Stacks T A := { S with R := Function.update S.R (cr .out) words }
  have he₁' : Exec body (cmulStream cr (rmulOne ι hι hT hQ cr)) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hblank, List.append_nil] using he₁
  have off (k : Fin T) (hk : k ≠ cr .out) : S₁.R k = S.R k := by simp [S₁, hk]
  obtain ⟨v₂, hu₂, he₂⟩ := chirpOperandX_exec (body := body) hreg s t q w m M
    (chirpInputNumerators s t α q m) u v₁ S₁ []
    (by rw [off _ ‹batch ≠ cr .out›]; exact hbatch)
    (by simp only [S₁, Function.update_self, List.append_nil]; rfl)
    (by rw [off _ ‹rowCount ≠ cr .out›]; exact hrow)
    (by rw [off _ ‹wordR ≠ cr .out›]; exact hword)
    (by rw [off _ ‹recordSymbols ≠ cr .out›]; exact hrecord)
    (by
      intro k hk
      have h := hclean k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [off _ (by first | assumption | (apply Ne.symm; assumption))] <;> exact h)
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (operands ++ S₁.R dst) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body (cr .out) v₂ S₂
  have hlen : words.length = M * (3 * m + 1) * w := by
    simp [words, length_cstream, chirpWeighted]
  refine ⟨v₃, n₁ + ((M * (26 * (3 * m + 1) * w + 19 * (3 * m + 1) + 17) + 8) +
    (2 * (S₂.R (cr .out)).length + 2)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · simp only [S₂, S₁, Function.update_of_ne ‹dst ≠ cr .out›.symm, Function.update_self, hlen]
    unfold chirpMakeXCost
    omega
  · refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₁' he₂ he₃
    funext k
    by_cases hd : k = dst
    · subst k
      simp [S₂, S₁, operands, ‹dst ≠ cr .out›]
    · by_cases ho : k = cr .out
      · subst k
        simp [S₂, S₁, hd, hblank]
      · simp [S₂, S₁, hd, ho]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
