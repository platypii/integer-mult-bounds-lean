module

public import IntegerMultBounds.MathlibTM2.Routing.GroupedProfileTerminal
public import IntegerMultBounds.MathlibTM2.Routing.RepairRotationCoordinates

/-! Generate complete coordinates for both temporary-bit A descriptors from
live dimensions and source profiles, restoring every non-output tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A : ℕ} {P U : Type}

theorem repairAProfileGenerate_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K) (hGK : p.G < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X) (j : Fin 2)
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lg Lk Ls : ℕ) (hg : p.G < 2 ^ Lg) (hk : p.K < 2 ^ Lk)
    (hwidth : Lg ≤ Li + Lk) (hN : p.wy < 2 ^ (Li + Lk)) (hpositive : 0 < p.wy)
    (hi : p.n * p.G ≤ 2 ^ Li) (hW : selectiveSourceWidth p X .A + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls (affineSourceProfile (repairRotationSources p X hG hK active s .A j)))
    (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg (.coordinate (.arithmetic .index))) = binSyms Li 0)
    (hgroup : S.R (rg (.coordinate (.arithmetic .group))) = binSyms Lg p.G)
    (hstride : S.R (rg (.coordinate (.arithmetic .stride))) = binSyms Lk p.K)
    (hbase : S.R (rg (.coordinate (.arithmetic .base))) = binSyms (Li + Lk) (p.ρ + 1))
    (hlast : S.R (rg (.coordinate .last)) = binSyms (Li + Lk) (p.wy - 1))
    (hone : S.R (rg (.coordinate .one)) = binSyms Ls 1) (hsaved : S.R saved = [])
    (hblank : ∀ r, r ∉ groupedProfileLive → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (22 * (Li + Lk) + 12 * Ls + 37) +
        (p.n * p.G * (groupedProfileCallCost Li Lg Lk Ls + 2) +
          2 * (p.n * p.G * (Ls + 3)) + 16 * Li + 20) ∧
      Exec body (groupedProfileTerminalProgram rg saved) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg (.coordinate .dst)) (sparseCoordinateFrames (Li + Lk) Ls
          (sparseCoordinateValues (repairRotationCoordinates p X hG hK active s .A j)) ++ S.R (rg (.coordinate .dst))) }) := by
  have hposition : (fun c : ℕ => (0 + c) / p.G * p.K + ((0 + c) % p.G + (p.ρ + 1))) = posA p := by
    funext c
    simp only [Nat.zero_add, posA]
    omega
  have hpos : ∀ c : Fin (repairRotationSlots p .A),
      0 < (0 + c.val) / p.G * p.K + ((0 + c.val) % p.G + (p.ρ + 1)) ∧
      (0 + c.val) / p.G * p.K + ((0 + c.val) % p.G + (p.ρ + 1)) < p.wy := by
    intro c
    refine ⟨by omega, ?_⟩
    change (fun c : ℕ => (0 + c) / p.G * p.K + ((0 + c) % p.G + (p.ρ + 1))) c.val < p.wy
    rw [hposition]
    exact posA_lt hG hGK c.isLt
  obtain ⟨v', steps, hu, ht, he⟩ := groupedProfileTerminal_exec body rg hrg saved hsep
    Li Lg Lk Ls 0 p.G p.K (p.ρ + 1) p.wy (repairRotationSources p X hG hK active s .A j)
    hg hG hk hwidth hN hpositive (by simpa only [Nat.zero_add, repairRotationSlots] using hi)
    hpos hW v S hsrc harchive hindex hgroup hstride hbase hlast hone hsaved hblank
  rw [hposition] at he
  exact ⟨v', steps, hu, ht, he⟩

end IntegerMultBounds.MathlibTM2.Routing
