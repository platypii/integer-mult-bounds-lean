module

public import IntegerMultBounds.MathlibTM2.Routing.GatedTaggedSourceFrame
public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunLoad

/-! Load raw source coordinates and a region tag, then compute the address.
All consumed fields and tag bits remain in one rewind archive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def gatedSelectedSourceFrameLoadProgram (rg : Fin 4 → Fin 13 → Fin T)
    (zr : BinaryZeroReg → Fin T) (src saved index localOffset tmp dst : Fin T) : Pr P T Q A U :=
  .seq (selectorRunLoadProgram src saved index localOffset tmp) (gatedTaggedSourceFrameProgram rg zr src saved dst)

theorem gatedSelectedSourceFrameLoad_exec (body : P → Pr P T Q A U)
    (rg : Fin 4 → Fin 13 → Fin T) (lo hi : Bool)
    (hrg : Function.Injective (rg (sourceTagIndex lo hi)))
    (src saved index localOffset tmp dst : Fin T)
    (hreg : [src, saved, index, localOffset, tmp].Nodup)
    (hsrc : ∀ j, src ≠ rg (sourceTagIndex lo hi) j)
    (hsaved : ∀ j, saved ≠ rg (sourceTagIndex lo hi) j)
    (hindexReg : ∀ tag, rg tag 0 = index) (hlocalReg : ∀ tag, rg tag 3 = localOffset)
    (hsep : ∀ j, dst ≠ rg (sourceTagIndex lo hi) j)
    (hdsrc : dst ≠ src) (hdsaved : dst ≠ saved)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = dst)
    (hz5 : ∀ j, zr j ≠ rg (sourceTagIndex lo hi) 5)
    (hsrcZr : ∀ j, src ≠ zr j) (hsavedZr : ∀ j, saved ≠ zr j)
    (hzIndex : ∀ j, zr j ≠ index) (hzLocal : ∀ j, zr j ≠ localOffset)
    (enabled : Bool) (Lw Li Lk i k b r : ℕ) (hwidth : Li + Lk < 2 ^ Lw) (hiFit : i < 2 ^ Li) (hk : k < 2 ^ Lk)
    (hfit : i * k + b + r < 2 ^ (Li + Lk))
    (rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hraw : S.R src = binSyms Li i ++ separator :: (binSyms (Li + Lk) r ++ separator ::
      (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest)))
    (hindex : S.R index = []) (hlocal : S.R localOffset = []) (htmp : S.R tmp = [])
    (hstride : S.R (rg (sourceTagIndex lo hi) 1) = binSyms Lk k)
    (hbase : S.R (rg (sourceTagIndex lo hi) 2) = binSyms (Li + Lk) b)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 →
      S.R (rg (sourceTagIndex lo hi) j) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ j, S.R (zr (.scratch j)) = []) :
    let B := selectorRunLoaded S.R src saved index localOffset (binSyms Li i) (binSyms (Li + Lk) r)
      (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest)
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (4 * Li + 4 * (Li + Lk) + 12) +
        (gatedSelectedSourceFrameCost Lw Li Lk + 4) ∧
      Exec body (gatedSelectedSourceFrameLoadProgram rg zr src saved index localOffset tmp dst) (mk v S) steps
        (mk v' { S with R := activityProfileFrameBank (sourceTagDispatchBank B src saved lo hi (bitSymbol enabled :: rest)) src saved dst (Li + Lk) (i * k + b + r) enabled rest }) := by
  have hn := hreg
  regs_ne hn
  obtain ⟨v₁, hu₁, hx₁⟩ := selectorRunLoad_exec body src saved index localOffset tmp hreg
    Li (Li + Lk) i r (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest) v S hraw hindex hlocal htmp
  let G : Stacks T A := { S with R := selectorRunLoaded S.R src saved index localOffset (binSyms Li i) (binSyms (Li + Lk) r) (bitSymbol lo :: bitSymbol hi :: bitSymbol enabled :: rest) }
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
  have hzkeep (j : BinaryZeroReg) : G.R (zr j) = S.R (zr j) := by
    dsimp only [G]
    exact selectorRunLoaded_keep _ _ _ _ _ _ _ _ _ (hsrcZr j).symm (hsavedZr j).symm (hzIndex j) (hzLocal j)
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := gatedTaggedSourceFrame_exec body rg lo hi hrg
    src saved dst ‹src ≠ saved› hsrc hsaved hsep hdsrc hdsaved zr hzr hdst hz5 hsrcZr hsavedZr enabled Lw Li Lk i k b r hwidth hiFit hk hfit rest v₁ G
    (by simp [G, selectorRunLoaded, ‹src ≠ saved›, ‹src ≠ index›, ‹src ≠ localOffset›])
    (by rw [hindexReg]; simp [G, selectorRunLoaded, ‹index ≠ localOffset›])
    ((hkeep 1 (by decide) (by decide)).trans hstride)
    ((hkeep 2 (by decide) (by decide)).trans hbase)
    (by rw [hlocalReg]; simp [G, selectorRunLoaded])
    (fun j h0 h1 h2 h3 => (hkeep j h0 h3).trans (hblank j h0 h1 h2 h3))
    ((hzkeep .width).trans hwidthInput) ((hzkeep .unary).trans hunary)
    (fun j => (hzkeep (.scratch j)).trans (hzeroScratch j))
  exact ⟨v₂, (4 * Li + 4 * (Li + Lk) + 12) + m₂, hu₂.trans hu₁,
    Nat.add_le_add_left hm₂ _, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
