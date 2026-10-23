module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileCoordinates

/-! Generate the exact sparse-pattern coordinate input from a live source
profile and dimensions, restoring every tape except the coordinate output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W m : ℕ} {P U : Type}

theorem affineSourceProfileGenerate_exec (body : P → Pr P T Q A U)
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lk Ls index k o N : ℕ) (src : Fin m → Option (Fin W)) (hk : k < 2 ^ Lk) (hN : N < 2 ^ (Li + Lk))
    (hi : index + m ≤ 2 ^ Li) (hpos : ∀ j : Fin m, (index + j.val) * k + o < N)
    (hW : W + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls (affineSourceProfile src)) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg .index) = binSyms Li index)
    (hstride : S.R (rg .stride) = binSyms Lk k) (hoffset : S.R (rg .offset) = binSyms (Li + Lk) o)
    (hlast : S.R (rg .last) = binSyms (Li + Lk) (N - 1)) (hone : S.R (rg .one) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .index → r ≠ .stride → r ≠ .offset → r ≠ .last → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ m * (affineProfileCallCost Li Lk Ls + 2) +
        2 * (m * (Ls + 3)) + 16 * Li + 20 ∧
      Exec body (affineProfileGenerateProgram rg saved) (mk v S)
        steps
        (mk v' { S with R := Function.update S.R (rg .dst) (sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues
          (sparsePatternCoordinates (N := N) (fun j => (index + j) * k + o) src)) ++ S.R (rg .dst)) }) := by
  have hr := affineSourceProfile_ready (N := N) Li Ls index k o src hi hpos hW
  obtain ⟨v', steps, hu, ht, he⟩ := affineProfileGenerate_exec body rg hrg saved hsep
    Li Lk Ls index k o N (affineSourceProfile src) hk hN hr v S
    hsrc harchive hindex hstride hoffset hlast hone hsaved hblank
  rw [affineSourceProfile_output] at he
  rw [affineProfileFrames_length] at ht
  have hl : (affineSourceProfile src).length = m := by simp [affineSourceProfile]
  rw [hl] at ht
  exact ⟨v', steps, hu, ht, he⟩

end IntegerMultBounds.MathlibTM2.Routing
