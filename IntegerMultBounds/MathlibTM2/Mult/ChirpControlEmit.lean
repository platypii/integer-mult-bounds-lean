module

public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! # Emit an executable unary gathering-control packet

The binary count is retained. Unary ticks and a blank delimiter form the reversed
packet; the whole packet stream is reversed once after its generation loop.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def chirpControlEmit (a dst work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (toUnary a dst work saved tmp) (.act (.push (.rt dst) (fun _ => blank) .done))

/-- Binary conversion and delimiter emission preserve the word and every work register. -/
theorem chirpControlEmit_exec {a dst work saved tmp : Fin T}
    (hreg : [a, dst, work, saved, tmp].Nodup) (W d : ℕ) (hd : d < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (ha : S.R a = binSyms W d)
    (hw : S.R work = []) (hs : S.R saved = []) (ht : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6 * d + 11 * W + 7 ∧
      Exec body (chirpControlEmit a dst work saved tmp) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (blank :: (List.replicate d tick ++ S.R dst))) }) := by
  obtain ⟨v', n, hu, hn, he⟩ := toUnary_exec_linear body hreg hd v S ha hw hs ht
  let S₁ : Stacks T A := { S with R := Function.update S.R dst (List.replicate d tick ++ S.R dst) }
  have hp : (Action.push (.rt dst) (fun _ : HS T Q A U => blank) .done).run (mk v' S₁) =
      mk v' { S with R := Function.update S.R dst (blank :: (List.replicate d tick ++ S.R dst)) } := by
    simp [Action.run, update_rt, S₁]
  exact ⟨v', n + 1, hu, by omega, Exec.seq he
    (hp ▸ Exec.act (body := body) (.push (.rt dst) (fun _ => blank) .done) _)⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
