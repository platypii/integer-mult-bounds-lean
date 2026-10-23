module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileClosedGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RepairRotationCoordinates

/-! Generate the complete Z-descriptor coordinate input from its live source
profile at any reservoir offset, including empty source profiles. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A : ℕ} {P U : Type}

theorem repairZProfileGenerate_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (hG : 0 < p.G) (hK : 0 < p.K) (hwy : 0 < p.wy) (j : Fin 2)
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lk Ls : ℕ) (hk : p.K < 2 ^ Lk) (hN : p.wy < 2 ^ (Li + Lk))
    (hi : p.n ≤ 2 ^ Li) (hW : selectiveSourceWidth p X .Z + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls (affineSourceProfile (repairRotationSources p X hG hK active s .Z j))) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg .index) = binSyms Li 0)
    (hstride : S.R (rg .stride) = binSyms Lk p.K) (hoffset : S.R (rg .offset) = binSyms (Li + Lk) p.ρ)
    (hlast : S.R (rg .last) = binSyms (Li + Lk) (p.wy - 1)) (hone : S.R (rg .one) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .index → r ≠ .stride →
      r ≠ .offset → r ≠ .last → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ affineProfileClosedCost Li Lk Ls p.n ∧
      Exec body (affineProfileClosedProgram rg saved) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
            (repairRotationCoordinates p X hG hK active s .Z j)) ++ S.R (rg .dst)) }) := by
  have hρfit : p.ρ < 2 ^ (Li + Lk) := by
    have hw : p.ρ ≤ p.wy := by dsimp only [Par.wy]; omega
    omega
  have hpos : ∀ c : Fin p.n, c.val * p.K + p.ρ < p.wy := by
    intro c
    have hb := repairKeyCoordinates_bound p hK c.val c.isLt
    dsimp only [posS] at hb
    omega
  obtain ⟨v', steps, hu, ht, he⟩ := affineProfileClosed_exec body rg hrg saved hsep
    Li Lk Ls p.K p.ρ p.wy (repairRotationSources p X hG hK active s .Z j) hk hN hρfit hwy
    (by simpa only [repairRotationSlots] using hi) hpos hW v S hsrc harchive hindex hstride hoffset hlast hone hsaved hblank
  have hposition : (fun c : ℕ => c * p.K + p.ρ) = posS p := by
    funext c
    exact Nat.add_comm _ _
  rw [hposition] at he
  exact ⟨v', steps, hu, ht, he⟩

end IntegerMultBounds.MathlibTM2.Routing
