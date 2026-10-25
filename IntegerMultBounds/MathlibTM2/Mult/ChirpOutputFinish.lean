module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputRound
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputCrop

/-! # Finish the chirp output stream

Execute precision reduction followed by cropping to the original output length.
All reusable counters and scratch are restored, and both passes are charged.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Final precision reduction and removal of the padded last block. -/
theorem chirpOutputFinish_exec (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src, dst, tmp, cW, cS, cE, cD, sp, sg, cy].Nodup)
    {count saved cropTmp : Fin T} (hcrop : [count, src, saved, cropTmp].Nodup)
    (p q l Γ w t : ℕ) (hpq : p ≤ q) (hw : q + l + Γ + 5 ≤ w)
    (xs : List GaussianInt) (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 8 * (2 : ℝ) ^ (l + Γ))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w xs) (hdst : S.R dst = [])
    (hg : topShiftG tmp cW cS cE cD sp sg cy w (q - p) (p + l + Γ + 5) S.R)
    (hcount : (S.R count).length = (min t xs.length) * (p + l + Γ + 5))
    (hsaved : S.R saved = []) (htmp : S.R cropTmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body
        (.seq (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy))
          (chirpCrop count src saved cropTmp))
        (mk v S)
        ((1 + (xs.length * (topShiftWordCost w (q - p) (p + l + Γ + 5) + 1) + 1) +
          (2 * (xs.length * (p + l + Γ + 5)) + 2)) +
          (6 * ((min t xs.length) * (p + l + Γ + 5)) +
            2 * ((xs.length - t) * (p + l + Γ + 5)) + 8))
        (mk v' { S with R := (Function.update S.R src
          (cstream A (p + l + Γ + 5) ((xs.take t).map (tdivN (q - p))))) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := chirpOutputRound_exec (body := body) hA hreg p q l Γ w hpq hw
    xs hxs v S hsrc hdst hg
  let S₁ : Stacks T A := { S with R := (Function.update S.R src
    (cstream A (p + l + Γ + 5) (xs.map (tdivN (q - p))))) }
  have hcrop' := hcrop
  regs_ne hcrop'
  obtain ⟨v₂, hu₂, he₂⟩ := chirpCrop_stream_exec (body := body) hcrop (p + l + Γ + 5) t
    (xs.map (tdivN (q - p))) v₁ S₁ (by simp [S₁])
    (by simpa [S₁, ‹count ≠ src›] using hcount)
    (by simpa [S₁, ‹src ≠ saved›.symm] using hsaved)
    (by simpa [S₁, ‹src ≠ cropTmp›.symm] using htmp)
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by simp) ?_⟩
  simp only [S₁, Function.update_idem, List.map_take]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
