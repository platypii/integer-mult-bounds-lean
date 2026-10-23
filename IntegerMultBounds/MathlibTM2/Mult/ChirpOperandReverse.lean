module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpReverseRows
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperands

/-! # Produce the reversed S1 input operands from the weighted row stream -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Every forward weighted row contains the full gathered window. -/
@[simp] theorem length_chirpWeighted (s t q m n : ℕ) (g : ℕ → ℕ → ℤ)
    (u : ZMod s → GaussianInt) : (chirpWeighted s t q m n g u).length = 3 * m + 1 := by
  simp [chirpWeighted]

/-- Reversal emits precisely the raw X operand stream expected by the shared S1 caller.
All supplied counters, weighted rows, scratch, spectator tails and user state are restored. -/
theorem chirpOperandX_exec
    {dst batch batchSaved rowCount recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, rowCount, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (s t q w m M : ℕ) (g : ℕ → ℕ → ℤ) (u : ZMod s → GaussianInt)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R batch).length = M)
    (hsrc : S.R src = cstream A w ((List.range M).flatMap fun n =>
      chirpWeighted s t q m n g u) ++ tail)
    (hrow : (S.R rowCount).length = 3 * m + 1)
    (hw : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = (3 * m + 1) * w)
    (hclean : ∀ k ∈ [batchSaved, acc, savedSource, recordSaved, current, saved, buf, tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reverseRows batch batchSaved rowCount recordSaved wordR
        recordSymbols src acc current savedSource saved buf tmp dst) (mk v S)
        (M * (26 * (3 * m + 1) * w + 19 * (3 * m + 1) + 17) + 8)
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w ((List.range M).flatMap fun n => chirpOperandX s t q m n g u) ++ S.R dst)) }) := by
  let blocks := (List.range M).map fun n => chirpWeighted s t q m n g u
  obtain ⟨v', hu, he⟩ := reverseRows_exec (body := body) hreg w (3 * m + 1) blocks
    (by
      intro xs hx
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
      exact length_chirpWeighted ..) v S tail (by simpa [blocks] using hbatch)
    (by simpa [blocks, List.flatMap_def] using hsrc) hrow hw hrecord hclean
  refine ⟨v', hu, ?_⟩
  simpa only [blocks, List.length_map, List.length_range, List.flatMap_map, chirpOperandX] using he

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
