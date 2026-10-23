module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherWindows

/-! # Executable shared gathering of the analytic chirp input windows -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

/-- The last block can be partial; every emitted block still starts before output `t`. -/
theorem chirpBlock_valid {t m n : ℕ} (ht : 0 < t) (hm : 0 < m)
    (hn : n < (t - 1) / m + 1) : n * m < t := by
  have hdiv : n ≤ (t - 1) / m := by omega
  have hmul := (Nat.le_div_iff_mul_le hm).mp hdiv
  omega

/-- Even the final advance after the last window sweeps at most `s+m` records. -/
theorem chirpCenter_end_le {s t m M : ℕ} (hst : s ≤ t) (ht : 0 < t)
    (hvalid : ∀ n < M, n * m < t) : chirpCenter s t m M ≤ s + m := by
  cases M with
  | zero => simp
  | succ n =>
    have hn := hvalid n (by omega)
    have hMm : (n + 1) * m ≤ t + m := by rw [Nat.add_mul, Nat.one_mul]; omega
    have hnum : s * ((n + 1) * m) ≤ t * (s + m) := by
      calc s * ((n + 1) * m) ≤ s * (t + m) := Nat.mul_le_mul_left s hMm
        _ = s * t + s * m := by ring
        _ ≤ s * t + t * m := Nat.add_le_add_left (Nat.mul_le_mul_right m hst) _
        _ = t * (s + m) := by ring
    exact (Nat.div_le_div_right hnum).trans_eq (by
      rw [Nat.mul_comm t (s + m), Nat.mul_div_cancel _ ht])

/-- A fixed sweep gathers all cyclic windows, preserving every other stack and user state.
The cyclic extension and unary control stream are explicit data inputs to this contract. -/
theorem chirpGather_exec {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}
    {dst control savedControl advance window src acc current savedSource buf tmp : Fin T}
    (hreg : [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp].Nodup)
    (s t m w M : ℕ) (hs : 0 < s) (hst : s ≤ t) (ht : 0 < t)
    (u : ZMod s → GaussianInt) (hvalid : ∀ n < M, n * m < t)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A (chirpAdvancesFrom s t m w 0 M))
    (hsrc : S.R src = cstream A w (chirpExtended s m u))
    (hw : (S.R window).length = (3 * m + 1) * w)
    (hclean : ∀ k ∈ [savedControl, advance, acc, current, savedSource, buf, tmp], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (gatherBatch dst control savedControl advance window src acc current savedSource buf tmp)
        (mk v S) (M * (14 * ((3 * m + 1) * w) + 25) + 12 * (chirpCenter s t m M * w) + 8)
        (mk v' { S with R := (Function.update S.R dst
          ((List.range M).flatMap (fun n => cstream A w (chirpWindow s t m n u)) ++ S.R dst)) }) := by
  have hlen : (chirpAdvancesFrom s t m w 0 M).length = M := by simp [chirpAdvancesFrom]
  have hfit := chirpGatherFits_from (A := A) (w := w) (j := 0) hs hst ht u
    (by simpa only [Nat.zero_add] using hvalid)
  simp only [chirpCenter_zero, Nat.zero_mul, List.drop_zero] at hfit
  simpa only [hlen, chirpAdvances_sum, chirpGatherRows] using
    gatherBatch_exec (body := body) hreg ((3 * m + 1) * w) (chirpAdvancesFrom s t m w 0 M)
      (cstream A w (chirpExtended s m u)) hfit v S hc hsrc hw hclean

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
