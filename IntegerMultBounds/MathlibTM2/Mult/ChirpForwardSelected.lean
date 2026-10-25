module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardApprox
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardWindow

/-! # Explicit forward parameters with no numerical error or window oracles

The tape representation is the exact output of the checked arithmetic stages.
The remaining machine obligation is assembling and initializing their full caller.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

/-- The selected window, growth, ring length and precision close the tape error theorem. -/
theorem chirpForwardSelected_error {s t A : ℕ} [NeZero s] [NeZero t]
    (hA : 4 ≤ A) (hst : s < t) (α p : ℕ) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    ∀ u : ZMod s → GaussianInt, (∀ j, ‖value q (u j)‖ ≤ 1) →
      2 ^ p * ‖chirpForwardDecoded A s t α p q l Γ m u -
        resampA s t (α : ℝ) (fun j => value q (u j))‖ ≤ 4 := by
  have hp : 1 ≤ p := by nlinarith
  have hm : 1 ≤ chirpForwardWindow p α := by
    unfold chirpForwardWindow
    nlinarith [Nat.zero_le (Nat.sqrt p)]
  dsimp only
  intro u hu
  apply chirpForwardDecoded_error hA hst α p (chirpForwardRingLog p α) (chirpForwardGrowth p)
    (chirpForwardWindow p α) hα (by exact_mod_cast hαp)
    (by exact_mod_cast (chirpForwardWindow_sq p α hp).1) hm (chirpForwardRingLog_good p α)
    ?_ (fun b hb => chirpForwardGrowth_good s t α p b (NeZero.pos s) hst (by omega) hp hb) u hu
  intro b hb
  have he := chirpForwardWindow_exponent s t α p b hst.le hp (NeZero.pos t) (by omega) hb
  have hq : 16 * p + 1 ≤ chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) -
      chirpForwardGrowth p := by
    unfold chirpForwardPrecision chirpForwardGrowth
    omega
  have hq' : 16 * (p : ℝ) + 1 ≤
      (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) - chirpForwardGrowth p : ℕ) := by
    exact_mod_cast hq
  linarith

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
