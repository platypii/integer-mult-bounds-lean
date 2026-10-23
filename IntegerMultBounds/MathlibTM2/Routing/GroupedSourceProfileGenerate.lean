module

public import IntegerMultBounds.MathlibTM2.Routing.GroupedProfileCoordinates

/-! Generate the exact grouped sparse-pattern coordinate input from a live source
profile, restoring every tape except the coordinate output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W m : ℕ} {P U : Type}

theorem groupedSourceProfileGenerate_exec (body : P → Pr P T Q A U)
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lg Lk Ls index g k b N : ℕ) (src : Fin m → Option (Fin W)) (hg : g < 2 ^ Lg) (hgpositive : 0 < g) (hk : k < 2 ^ Lk)
    (hwidth : Lg ≤ Li + Lk) (hN : N < 2 ^ (Li + Lk))
    (hi : index + m ≤ 2 ^ Li)
    (hpos : ∀ j : Fin m, (index + j.val) / g * k + ((index + j.val) % g + b) < N)
    (hW : W + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls (affineSourceProfile src)) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg (.coordinate (.arithmetic .index))) = binSyms Li index)
    (hgroup : S.R (rg (.coordinate (.arithmetic .group))) = binSyms Lg g)
    (hstride : S.R (rg (.coordinate (.arithmetic .stride))) = binSyms Lk k) (hoffset : S.R (rg (.coordinate (.arithmetic .base))) = binSyms (Li + Lk) b)
    (hlast : S.R (rg (.coordinate .last)) = binSyms (Li + Lk) (N - 1)) (hone : S.R (rg (.coordinate .one)) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ∉ groupedProfileLive → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ m * (groupedProfileCallCost Li Lg Lk Ls + 2) +
        2 * (m * (Ls + 3)) + 16 * Li + 20 ∧
      Exec body (groupedProfileGenerateProgram rg saved) (mk v S)
        steps
        (mk v' { S with R := Function.update S.R (rg (.coordinate .dst)) (sparseCoordinateFrames (Li + Lk) Ls (sparseCoordinateValues (sparsePatternCoordinates (N := N) (fun j => (index + j) / g * k + ((index + j) % g + b)) src)) ++ S.R (rg (.coordinate .dst))) }) := by
  have hr := groupedSourceProfile_ready (N := N) Li Ls index g k b src hi hpos hW
  obtain ⟨v', steps, hu, ht, he⟩ := groupedProfileGenerate_exec body rg hrg saved hsep
    Li Lg Lk Ls index g k b N (affineSourceProfile src) hg hgpositive hk hwidth hN hr v S
    hsrc harchive hindex hgroup hstride hoffset hlast hone hsaved hblank
  rw [groupedSourceProfile_output] at he
  rw [affineProfileFrames_length] at ht
  have hl : (affineSourceProfile src).length = m := by simp [affineSourceProfile]
  rw [hl] at ht
  exact ⟨v', steps, hu, ht, he⟩

end IntegerMultBounds.MathlibTM2.Routing
