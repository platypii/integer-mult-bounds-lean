module

public import IntegerMultBounds.MathlibTM2.Routing.GroupedProfileFrame

/-! Generate grouped coordinates from a live profile and rewind its full archive.
Only the coordinate output and advanced index change; all other tapes are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def groupedProfileCompileProgram (rg : GroupedProfileReg → Fin T) : Pr P T Q A U :=
  .seq (.act (peekR (rg .src))) (.seq (.loop (·.flag) (groupedProfileLoopBody rg))
    (moveR (rg .archive) (rg .src) id))

theorem groupedProfileCompile_exec (body : P → Pr P T Q A U)
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (Li Lg Lk Ls index g k b N : ℕ) (entries : List (Bool × ℕ)) (hg : g < 2 ^ Lg) (hgpositive : 0 < g) (hk : k < 2 ^ Lk)
    (hwidth : Lg ≤ Li + Lk) (hN : N < 2 ^ (Li + Lk))
    (hready : GroupedProfileReady Li Ls g k b N index entries)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls entries) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg (.coordinate (.arithmetic .index))) = binSyms Li index)
    (hgroup : S.R (rg (.coordinate (.arithmetic .group))) = binSyms Lg g)
    (hstride : S.R (rg (.coordinate (.arithmetic .stride))) = binSyms Lk k) (hoffset : S.R (rg (.coordinate (.arithmetic .base))) = binSyms (Li + Lk) b)
    (hlast : S.R (rg (.coordinate .last)) = binSyms (Li + Lk) (N - 1)) (hone : S.R (rg (.coordinate .one)) = binSyms Ls 1)
    (hblank : ∀ r, r ∉ groupedProfileLive → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ entries.length * (groupedProfileCallCost Li Lg Lk Ls + 2) +
        2 * (affineProfileFrames (A := A) Ls entries).length + 4 ∧
      Exec body (groupedProfileCompileProgram rg) (mk v S)
        steps
        (mk v' { S with R := Function.update (Function.update S.R (rg (.coordinate .dst)) (groupedProfileOutput Li Lg Lk Ls index g k b N entries ++ S.R (rg (.coordinate .dst)))) (rg (.coordinate (.arithmetic .index))) (binSyms Li (index + entries.length)) }) := by
  let input := affineProfileFrames (A := A) Ls entries
  let v₁ := { v with flag := input.head?.isSome }
  have hp : (peekR (rg .src) : Act T Q A U).run (mk v S) = mk v₁ S := by
    simp only [peekR_run, hsrc]; rfl
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := groupedProfileLoop_exec body rg hrg Li Lg Lk Ls index g k b N entries hg hgpositive hk hwidth hN hready
    v₁ S hsrc hindex hgroup hstride hoffset hlast hone hblank rfl
  let S₂ : Stacks T A := { S with R := groupedProfileTraceBank S.R rg Li Lg Lk Ls index g k b N entries }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body (rg .archive) (rg .src) (hrg.ne (by decide)) id v₂ S₂
  have ha : S₂.R (rg .archive) = input.reverse := by
    dsimp only [S₂]
    rw [groupedProfileTrace_archive S.R rg hrg Li Lg Lk Ls index g k b N entries, harchive, List.append_nil]
  have hs : S₂.R (rg .src) = [] := groupedProfileTrace_src S.R rg hrg Li Lg Lk Ls index g k b N entries hsrc
  have hd := groupedProfileTrace_output S.R rg hrg Li Lg Lk Ls index g k b N entries
  have hc := groupedProfileTrace_index S.R rg Li Lg Lk Ls index g k b N entries hindex
  have hf : movedR S₂.R (rg .archive) (rg .src) id (S₂.R (rg .archive)) =
      Function.update (Function.update S.R (rg (.coordinate .dst)) (groupedProfileOutput Li Lg Lk Ls index g k b N entries ++ S.R (rg (.coordinate .dst))))
        (rg (.coordinate (.arithmetic .index))) (binSyms Li (index + entries.length)) := by
    rw [ha]
    funext j
    by_cases hj : j = rg .src
    · subst j; simp [movedR, hs, input, hsrc, hrg.eq_iff]
    · by_cases hjA : j = rg .archive
      · subst j; simp [movedR, harchive, hrg.eq_iff]
      · by_cases hjC : j = rg (.coordinate (.arithmetic .index))
        · subst j; simp [movedR, hj, hjA, S₂, hc]
        · by_cases hjD : j = rg (.coordinate .dst)
          · subst j; simp [movedR, hj, hjA, hjC, S₂, hd]
          · simp only [movedR, Function.update_of_ne hjA, Function.update_of_ne hj, Function.update_of_ne hjC, Function.update_of_ne hjD]
            exact groupedProfileTrace_keep S.R rg Li Lg Lk Ls index g k b N entries j hj hjA hjC hjD
  rw [hf, ha, List.length_reverse] at he₃
  refine ⟨v₃, 1 + (n₂ + (2 * input.length + 2)), hu₃.trans hu₂, by dsimp only [input]; omega, ?_⟩
  have he := Exec.seq (hp ▸ Exec.act (body := body) (peekR (rg .src)) (mk v S)) (Exec.seq he₂ he₃)
  dsimp only [input] at he
  convert he using 1; first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
