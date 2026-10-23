module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpSetup

/-! # Generate reusable counters for a shared correlation batch

The skip count `3mw` and record-symbol count `2^l w` are computed from unary dimensions.
The third generated word, `3m`, is owned setup workspace and is included in cleanup.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Generate the skip and record-symbol counters once for all records. -/
def correlationBatchSetup (lR wR mR triples skip recordSymbols current buf tmp : Fin T) : Pr P T Q A U :=
  .seq (umulSym 3 tick mR triples tmp) <|
  .seq (unaryProduct triples wR skip buf tmp) (padding lR wR current recordSymbols buf tmp)

/-- Exact prepared bank, with all setup work tapes restored. -/
theorem correlationBatchSetup_exec
    {lR wR mR triples skip recordSymbols current buf tmp : Fin T}
    (hreg : [lR, wR, mR, triples, skip, recordSymbols, current, buf, tmp].Nodup)
    (l w m : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hl : (S.R lR).length = l) (hw : (S.R wR).length = w) (hm : (S.R mR).length = m)
    (htriples : S.R triples = []) (hskip : S.R skip = []) (hrecord : S.R recordSymbols = [])
    (hcurrent : S.R current = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 12 * m * w + 31 * m + 4 * w + 4 * (2 ^ l * w) + 9 * l + 20 ∧
      Exec body (correlationBatchSetup lR wR mR triples skip recordSymbols current buf tmp) (mk v S) n
        (mk v' { S with R := (Function.update (Function.update
          (Function.update S.R triples (List.replicate (3 * m) tick)) skip
            (List.replicate (3 * m * w) tick)) recordSymbols (List.replicate (2 ^ l * w) tick)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := umulSym_exec (body := body) 3 tick ‹mR ≠ triples› ‹mR ≠ tmp›
    ‹triples ≠ tmp› v S htmp
  rw [hm, htriples, List.append_nil] at he₁
  set S₁ : Stacks T A := { S with R := Function.update S.R triples (List.replicate (3 * m) tick) }
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := unaryProduct_exec (body := body)
    (show [triples, wR, skip, buf, tmp].Nodup by simp_all [ne_comm]) v₁ S₁
    (by simp [S₁, ‹triples ≠ buf›.symm, hbuf])
    (by simp [S₁, ‹triples ≠ tmp›.symm, htmp])
  have ht₁ : (S₁.R triples).length = 3 * m := by simp [S₁]
  have hw₁ : (S₁.R wR).length = w := by simpa [S₁, ‹wR ≠ triples›] using hw
  have hs₁ : S₁.R skip = [] := by simp [S₁, ‹triples ≠ skip›.symm, hskip]
  rw [ht₁, hw₁] at hn₂ he₂
  rw [hs₁, List.append_nil] at he₂
  set S₂ : Stacks T A := { S₁ with R := Function.update S₁.R skip (List.replicate (3 * m * w) tick) }
  have off (k : Fin T) (ht : k ≠ triples) (hs : k ≠ skip) : S₂.R k = S.R k := by
    simp [S₂, S₁, ht, hs]
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ := padding_exec (body := body)
    (show [lR, wR, current, recordSymbols, buf, tmp].Nodup by simp_all [ne_comm]) v₂ S₂
    (by rw [off _ ‹triples ≠ recordSymbols›.symm ‹skip ≠ recordSymbols›.symm]; exact hrecord)
    (by rw [off _ ‹triples ≠ buf›.symm ‹skip ≠ buf›.symm]; exact hbuf)
    (by rw [off _ ‹triples ≠ tmp›.symm ‹skip ≠ tmp›.symm]; exact htmp)
  have hl₂ : (S₂.R lR).length = l := by rw [off _ ‹lR ≠ triples› ‹lR ≠ skip›]; exact hl
  have hw₂ : (S₂.R wR).length = w := by rw [off _ ‹wR ≠ triples› ‹wR ≠ skip›]; exact hw
  have hc₂ : S₂.R current = [] := by
    rw [off _ ‹triples ≠ current›.symm ‹skip ≠ current›.symm]
    exact hcurrent
  rw [hl₂, hw₂, hc₂, List.length_nil] at hn₃ he₃
  simp only [Nat.sub_zero] at he₃
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · nlinarith [hn₂, hn₃]
  · rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
