module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileComplete

/-! Executed generation of the complete coordinate inputs for the six Y, YZ
and X repair descriptors. No absolute-coordinate input is supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

variable {T Q A : ℕ} {P U : Type}

theorem repairAffineProfileGenerate_exec (body : P → Pr P T Q A U)
    (p : Par) (X : ℕ) (hG : 0 < p.G) (hK : 0 < p.K)
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (hn : 0 < p.n) (off : Off) (hoff : off = .Y ∨ off = .YZ ∨ off = .X) (j : Fin 2)
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lk Ls : ℕ) (hk : p.G < 2 ^ Lk) (hN : selectiveTargetWidth p off < 2 ^ (Li + Lk))
    (hi : p.n ≤ 2 ^ Li)
    (hW : selectiveSourceWidth p X off + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls (affineSourceProfile (repairRotationSources p X hG hK active s off j))) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg .index) = binSyms Li 0)
    (hstride : S.R (rg .stride) = binSyms Lk p.G) (hoffset : S.R (rg .offset) = binSyms (Li + Lk) 0)
    (hlast : S.R (rg .last) = binSyms (Li + Lk) (selectiveTargetWidth p off - 1)) (hone : S.R (rg .one) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .index → r ≠ .stride → r ≠ .offset → r ≠ .last → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ p.n * (affineProfileCallCost Li Lk Ls + 2) +
        2 * (p.n * (Ls + 3)) + 16 * Li + 20 ∧
      Exec body (affineProfileGenerateProgram rg saved) (mk v S)
        steps
        (mk v' { S with R := Function.update S.R (rg .dst) (sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
          (repairRotationCoordinates p X hG hK active s off j)) ++ S.R (rg .dst)) }) := by
  have hslots : repairRotationSlots p off = p.n := by
    rcases hoff with rfl | rfl | rfl <;> rfl
  have hpos : ∀ c : Fin (repairRotationSlots p off),
      (0 + c.val) * p.G + 0 < selectiveTargetWidth p off := by
    rcases hoff with rfl | rfl | rfl <;> intro c <;>
      simpa only [Nat.zero_add, Nat.add_zero, repairRotationSlots, selectiveTargetWidth, Par.wc] using Nat.mul_lt_mul_of_pos_right c.isLt hG
  have hr := affineSourceProfile_ready (N := selectiveTargetWidth p off) Li Ls 0 p.G 0
    (repairRotationSources p X hG hK active s off j) (by simpa only [Nat.zero_add, hslots] using hi) hpos hW
  obtain ⟨v', steps, hu, ht, he⟩ := affineProfileGenerate_exec body rg hrg saved hsep
    Li Lk Ls 0 p.G 0 (selectiveTargetWidth p off)
    (affineSourceProfile (repairRotationSources p X hG hK active s off j)) hk hN hr v S
    hsrc harchive hindex hstride hoffset hlast hone hsaved hblank
  rw [repairAffineProfile_output p X hG hK active s hn off hoff j] at he
  rw [affineProfileFrames_length] at ht
  have hl : (affineSourceProfile (repairRotationSources p X hG hK active s off j)).length = p.n := by
    simp only [affineSourceProfile, List.length_ofFn, hslots]
  rw [hl] at ht
  exact ⟨v', steps, hu, ht, he⟩

end IntegerMultBounds.MathlibTM2.Routing
