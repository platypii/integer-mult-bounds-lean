module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputBounds
public import IntegerMultBounds.MathlibTM2.Mult.SignedRoundExec

/-! # Execute the final signed precision reduction on a chirp stream

Reuse the signed word pass structurally over an arbitrary list. The program keeps
all counters and scratch, including the empty reversal tape, and changes only the
source stream. Width reduction and fixed-point precision reduction are distinct.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Execute signed truncation on an arbitrary stream, restoring every other register. -/
theorem chirpRound_exec (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src, dst, tmp, cW, cS, cE, cD, sp, sg, cy].Nodup)
    (w d k : ℕ) (hw : 1 ≤ w) (hdk : d + k ≤ w)
    (xs : List GaussianInt) (hxs : ∀ x ∈ xs, Fits w x)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w xs) (hdst : S.R dst = [])
    (hg : topShiftG tmp cW cS cE cD sp sg cy w d k S.R) :
    ∃ v', v'.user = v.user ∧
      Exec body (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy))
        (mk v S) (1 + (xs.length * (topShiftWordCost w d k + 1) + 1) +
          (2 * (xs.length * k) + 2))
        (mk v' { S with R := (Function.update S.R src
          (cstream A k (xs.map (tdivN d)))) }) := by
  apply signedRound_exec hA hreg w d k hw hdk xs _ v S hsrc hdst hg
  intro x hx
  have hf := hxs x hx
  exact ⟨⟨(abs_lt.mp hf.1).1.le,(abs_lt.mp hf.1).2⟩,
    ⟨(abs_lt.mp hf.2).1.le,(abs_lt.mp hf.2).2⟩⟩

/-- The final precision reduction preserves the output norm envelope. -/
theorem chirpRounded_norm {p q : ℕ} (hpq : p ≤ q) (l Γ : ℕ) (x : GaussianInt)
    (hx : ‖value q x‖ ≤ 8 * (2 : ℝ) ^ (l + Γ)) :
    ‖value p (tdivN (q - p) x)‖ ≤ 8 * (2 : ℝ) ^ (l + Γ) := by
  rw [value_round_precision hpq]
  exact (NLogN.norm_rhoC_le p _).trans hx

/-- Five guard bits also prevent signed aliasing after reducing precision. -/
theorem chirpRounded_fits {p q : ℕ} (hpq : p ≤ q) (l Γ k : ℕ)
    (hk : p + l + Γ + 5 ≤ k) (x : GaussianInt)
    (hx : ‖value q x‖ ≤ 8 * (2 : ℝ) ^ (l + Γ)) :
    Fits k (tdivN (q - p) x) :=
  fits_chirpOutput_bound p l Γ k _ (chirpRounded_norm hpq l Γ x hx) hk

/-- Execute the final p-grid rounding with a derived signed input fit.
The returned words have exactly the same five guard bits as the product stage. -/
theorem chirpOutputRound_exec (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src, dst, tmp, cW, cS, cE, cD, sp, sg, cy].Nodup)
    (p q l Γ w : ℕ) (hpq : p ≤ q) (hw : q + l + Γ + 5 ≤ w)
    (xs : List GaussianInt) (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 8 * (2 : ℝ) ^ (l + Γ))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w xs) (hdst : S.R dst = [])
    (hg : topShiftG tmp cW cS cE cD sp sg cy w (q - p) (p + l + Γ + 5) S.R) :
    ∃ v', v'.user = v.user ∧
      Exec body (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy))
        (mk v S) (1 + (xs.length * (topShiftWordCost w (q - p) (p + l + Γ + 5) + 1) + 1) +
          (2 * (xs.length * (p + l + Γ + 5)) + 2))
        (mk v' { S with R := (Function.update S.R src
          (cstream A (p + l + Γ + 5) (xs.map (tdivN (q - p))))) }) :=
  chirpRound_exec hA hreg w (q - p) (p + l + Γ + 5) (by omega) (by omega)
    xs (fun x hx => fits_chirpOutput_bound q l Γ w x (hxs x hx) hw) v S hsrc hdst hg

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
