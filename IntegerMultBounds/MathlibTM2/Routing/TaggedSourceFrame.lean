module

public import IntegerMultBounds.MathlibTM2.Routing.SelectedSourceFrame
public import IntegerMultBounds.MathlibTM2.Routing.SourceTagDispatch

/-! Raw two-bit source tags select a region-base register for source-address
arithmetic. Tag bits are archived; coordinate operands and scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def taggedSourceFrameProgram (rg : Fin 4 → Fin 13 → Fin T) (src saved dst : Fin T) : Pr P T Q A U :=
  sourceTagDispatchProgram src saved (fun tag => selectedSourceFrameProgram (rg tag) dst)

theorem taggedSourceFrame_exec (body : P → Pr P T Q A U)
    (rg : Fin 4 → Fin 13 → Fin T) (lo hi : Bool)
    (hrg : Function.Injective (rg (sourceTagIndex lo hi)))
    (src saved dst : Fin T) (hss : src ≠ saved)
    (hsrc : ∀ j, src ≠ rg (sourceTagIndex lo hi) j)
    (hsaved : ∀ j, saved ≠ rg (sourceTagIndex lo hi) j)
    (hsep : ∀ j, dst ≠ rg (sourceTagIndex lo hi) j)
    (hdsrc : dst ≠ src) (hdsaved : dst ≠ saved)
    (Li Lk i k b r : ℕ) (hiFit : i < 2 ^ Li) (hk : k < 2 ^ Lk)
    (hfit : i * k + b + r < 2 ^ (Li + Lk))
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (htag : S.R src = bitSymbol lo :: bitSymbol hi :: rest)
    (hindex : S.R (rg (sourceTagIndex lo hi) 0) = binSyms Li i)
    (hstride : S.R (rg (sourceTagIndex lo hi) 1) = binSyms Lk k)
    (hbase : S.R (rg (sourceTagIndex lo hi) 2) = binSyms (Li + Lk) b)
    (hlocal : S.R (rg (sourceTagIndex lo hi) 3) = binSyms (Li + Lk) r)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 →
      S.R (rg (sourceTagIndex lo hi) j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ selectedSourceFrameCost Li Lk + 4 ∧
      Exec body (taggedSourceFrameProgram rg src saved dst) (mk v S) steps
        (mk v' { S with R := Function.update (sourceTagDispatchBank S.R src saved lo hi rest) dst (affineProfileFrames (Li + Lk) [(true, i * k + b + r)] ++ S.R dst) }) := by
  let B : Stacks T A := { S with R := sourceTagDispatchBank S.R src saved lo hi rest }
  let u := sourceTagDispatchState v hi
  have hkeep (j : Fin 13) : B.R (rg (sourceTagIndex lo hi) j) = S.R (rg (sourceTagIndex lo hi) j) := by
    simp [B, sourceTagDispatchBank, (hsrc j).symm, (hsaved j).symm]
  obtain ⟨v', m, hu, hm, hx⟩ := selectedSourceFrame_exec body (rg (sourceTagIndex lo hi)) hrg dst hsep
    Li Lk i k b r hiFit hk hfit u B
    ((hkeep 0).trans hindex) ((hkeep 1).trans hstride) ((hkeep 2).trans hbase) ((hkeep 3).trans hlocal)
    (fun j h0 h1 h2 h3 => (hkeep j).trans (hblank j h0 h1 h2 h3))
  have hd : B.R dst = S.R dst := by simp [B, sourceTagDispatchBank, hdsrc, hdsaved]
  rw [hd] at hx
  exact ⟨v', m + 4, hu, by omega,
    sourceTagDispatch_exec body src saved hss _ lo hi rest v S htag m v' _ hx⟩

end IntegerMultBounds.MathlibTM2.Routing
