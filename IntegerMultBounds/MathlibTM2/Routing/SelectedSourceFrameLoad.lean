module

public import IntegerMultBounds.MathlibTM2.Routing.TaggedSourceFrame
public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunLoad

/-! Load raw source coordinates and a region tag, then compute the address.
All consumed fields and tag bits remain in one rewind archive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def selectedSourceFrameLoadProgram (rg : Fin 4 → Fin 13 → Fin T)
    (src saved index localOffset tmp dst : Fin T) : Pr P T Q A U :=
  .seq (selectorRunLoadProgram src saved index localOffset tmp) (taggedSourceFrameProgram rg src saved dst)

theorem selectedSourceFrameLoad_exec (body : P → Pr P T Q A U)
    (rg : Fin 4 → Fin 13 → Fin T) (lo hi : Bool)
    (hrg : Function.Injective (rg (sourceTagIndex lo hi)))
    (src saved index localOffset tmp dst : Fin T)
    (hreg : [src, saved, index, localOffset, tmp].Nodup)
    (hsrc : ∀ j, src ≠ rg (sourceTagIndex lo hi) j)
    (hsaved : ∀ j, saved ≠ rg (sourceTagIndex lo hi) j)
    (hindexReg : ∀ tag, rg tag 0 = index) (hlocalReg : ∀ tag, rg tag 3 = localOffset)
    (hsep : ∀ j, dst ≠ rg (sourceTagIndex lo hi) j)
    (hdsrc : dst ≠ src) (hdsaved : dst ≠ saved)
    (Li Lk i k b r : ℕ) (hiFit : i < 2 ^ Li) (hk : k < 2 ^ Lk)
    (hfit : i * k + b + r < 2 ^ (Li + Lk))
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = binSyms Li i ++ separator :: (binSyms (Li + Lk) r ++ separator ::
      (bitSymbol lo :: bitSymbol hi :: rest)))
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = [])
    (hstride : S.R (rg (sourceTagIndex lo hi) 1) = binSyms Lk k)
    (hbase : S.R (rg (sourceTagIndex lo hi) 2) = binSyms (Li + Lk) b)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 →
      S.R (rg (sourceTagIndex lo hi) j) = []) :
    let B := selectorRunLoaded S.R src saved index localOffset (binSyms Li i) (binSyms (Li + Lk) r)
      (bitSymbol lo :: bitSymbol hi :: rest)
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (4 * Li + 4 * (Li + Lk) + 12) +
        (selectedSourceFrameCost Li Lk + 4) ∧
      Exec body (selectedSourceFrameLoadProgram rg src saved index localOffset tmp dst) (mk v S) steps
        (mk v' { S with R := Function.update (sourceTagDispatchBank B src saved lo hi rest) dst (affineProfileFrames (Li + Lk) [(true, i * k + b + r)] ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, hx₁⟩ := selectorRunLoad_exec body src saved index localOffset tmp hreg
    Li (Li + Lk) i r (bitSymbol lo :: bitSymbol hi :: rest) v S hraw hindex hlocal htmp
  let G : Stacks T A := { S with R := selectorRunLoaded S.R src saved index localOffset (binSyms Li i) (binSyms (Li + Lk) r) (bitSymbol lo :: bitSymbol hi :: rest) }
  have hkeep (j : Fin 13) (hj0 : j ≠ 0) (hj3 : j ≠ 3) :
      G.R (rg (sourceTagIndex lo hi) j) = S.R (rg (sourceTagIndex lo hi) j) := by
    dsimp only [G]
    apply selectorRunLoaded_keep
    · exact (hsrc j).symm
    · exact (hsaved j).symm
    · rw [← hindexReg (sourceTagIndex lo hi)]
      exact hrg.ne hj0
    · rw [← hlocalReg (sourceTagIndex lo hi)]
      exact hrg.ne hj3
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := taggedSourceFrame_exec body rg lo hi hrg
    src saved dst ‹src ≠ saved› hsrc hsaved hsep hdsrc hdsaved Li Lk i k b r hiFit hk hfit rest v₁ G
    (by simp [G, selectorRunLoaded, ‹src ≠ saved›, ‹src ≠ index›, ‹src ≠ localOffset›])
    (by rw [hindexReg]; simp [G, selectorRunLoaded, ‹index ≠ localOffset›])
    ((hkeep 1 (by decide) (by decide)).trans hstride)
    ((hkeep 2 (by decide) (by decide)).trans hbase)
    (by rw [hlocalReg]; simp [G, selectorRunLoaded])
    (fun j h0 h1 h2 h3 => (hkeep j h0 h3).trans (hblank j h0 h1 h2 h3))
  have hd : G.R dst = S.R dst := by
    dsimp only [G]
    apply selectorRunLoaded_keep
    · exact hdsrc
    · exact hdsaved
    · rw [← hindexReg (sourceTagIndex lo hi)]
      exact hsep 0
    · rw [← hlocalReg (sourceTagIndex lo hi)]
      exact hsep 3
  rw [hd] at hx₂
  exact ⟨v₂, (4 * Li + 4 * (Li + Lk) + 12) + m₂, hu₂.trans hu₁,
    Nat.add_le_add_left hm₂ _, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
