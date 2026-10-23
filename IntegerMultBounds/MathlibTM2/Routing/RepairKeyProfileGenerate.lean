module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileTerminal
public import IntegerMultBounds.MathlibTM2.Routing.RepairKeyCoordinates

/-! Generate the complete key-descriptor coordinate input from its live source
profile when selected slots start at a positive reservoir offset. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A : ℕ} {P U : Type}

theorem repairKeyProfileGenerate_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (hK : 0 < p.K) (hρ : 0 < p.ρ)
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lk Ls : ℕ) (hk : p.K < 2 ^ Lk) (hN : p.wy < 2 ^ (Li + Lk))
    (hi : p.n ≤ 2 ^ Li) (hW : p.wy + 2 * p.wc + X + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls (affineSourceProfile (selectiveKeySources p X active s))) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg .index) = binSyms Li 0)
    (hstride : S.R (rg .stride) = binSyms Lk p.K) (hoffset : S.R (rg .offset) = binSyms (Li + Lk) p.ρ)
    (hlast : S.R (rg .last) = binSyms (Li + Lk) (p.wy - 1)) (hone : S.R (rg .one) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .index → r ≠ .stride →
      r ≠ .offset → r ≠ .last → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (22 * (Li + Lk) + 12 * Ls + 37) +
        (p.n * (affineProfileCallCost Li Lk Ls + 2) + 2 * (p.n * (Ls + 3)) + 16 * Li + 20) ∧
      Exec body (affineProfileTerminalProgram rg saved) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
            (repairKeyCoordinates p X active s)) ++ S.R (rg .dst)) }) := by
  have hpositive : 0 < p.wy := by dsimp only [Par.wy]; omega
  have hpos : ∀ j : Fin p.n, 0 < (0 + j.val) * p.K + p.ρ ∧
      (0 + j.val) * p.K + p.ρ < p.wy := by
    intro j
    have hb := repairKeyCoordinates_bound p hK j.val j.isLt
    dsimp only [posS] at hb
    simp only [Nat.zero_add]
    constructor <;> omega
  obtain ⟨v', steps, hu, ht, he⟩ := affineProfileTerminal_exec body rg hrg saved hsep
    Li Lk Ls 0 p.K p.ρ p.wy (selectiveKeySources p X active s) hk hN hpositive
    (by simpa only [Nat.zero_add] using hi) hpos hW v S
    hsrc harchive hindex hstride hoffset hlast hone hsaved hblank
  have hposition : (fun j : ℕ => (0 + j) * p.K + p.ρ) = posS p := by
    funext j
    simp only [Nat.zero_add, posS]
    exact Nat.add_comm _ _
  rw [hposition] at he
  exact ⟨v', steps, hu, ht, he⟩

end IntegerMultBounds.MathlibTM2.Routing
