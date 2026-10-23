module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileCompile
public import IntegerMultBounds.MathlibTM2.Routing.SparseCursorRestore

/-! Generate absolute coordinate frames from a live activity/source profile,
restore the complete input and original index, and erase the saved index.
Only coordinate output changes; every phase is charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def affineProfileGenerateProgram (rg : AffineProfileReg → Fin T) (saved : Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg .index) saved (rg .tx) (rg .ty))
    (.seq (affineProfileCompileProgram rg) (sparseCursorRestoreProgram (rg .index) saved (rg .tx) (rg .ty)))

theorem affineProfileGenerate_exec (body : P → Pr P T Q A U)
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lk Ls index k o N : ℕ) (entries : List (Bool × ℕ)) (hk : k < 2 ^ Lk) (hN : N < 2 ^ (Li + Lk))
    (hready : AffineProfileReady Li Ls k o N index entries)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls entries) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg .index) = binSyms Li index)
    (hstride : S.R (rg .stride) = binSyms Lk k) (hoffset : S.R (rg .offset) = binSyms (Li + Lk) o)
    (hlast : S.R (rg .last) = binSyms (Li + Lk) (N - 1)) (hone : S.R (rg .one) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .index → r ≠ .stride → r ≠ .offset → r ≠ .last → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ entries.length * (affineProfileCallCost Li Lk Ls + 2) +
        2 * (affineProfileFrames (A := A) Ls entries).length + 16 * Li + 20 ∧
      Exec body (affineProfileGenerateProgram rg saved) (mk v S)
        steps
        (mk v' { S with R := Function.update S.R (rg .dst) (affineProfileOutput Li Lk Ls index k o N entries ++ S.R (rg .dst)) }) := by
  have ht := hblank .tx (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hw := hblank .ty (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hregs : [rg .index, saved, rg .tx, rg .ty].Nodup := by
    simp [List.nodup_cons, hrg.eq_iff, hsep, Ne.symm (hsep .index)]
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body hregs v S ht hw
  rw [hindex, hsaved, List.append_nil, length_binSyms] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R saved (binSyms Li index) }
  have hkeep (r : AffineProfileReg) : S₁.R (rg r) = S.R (rg r) := Function.update_of_ne (hsep r).symm _ _
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := affineProfileCompile_exec body rg hrg Li Lk Ls index k o N entries hk hN hready v₁ S₁
    ((hkeep .src).trans hsrc) ((hkeep .archive).trans harchive) ((hkeep .index).trans hindex)
    ((hkeep .stride).trans hstride) ((hkeep .offset).trans hoffset) ((hkeep .last).trans hlast) ((hkeep .one).trans hone)
    (by intro r hs ha hc hst ho hl h1 hd; rw [hkeep]; exact hblank r hs ha hc hst ho hl h1 hd)
  have hd : S₁.R (rg .dst) = S.R (rg .dst) := hkeep .dst
  rw [hd] at he₂
  let out := affineProfileOutput (A := A) Li Lk Ls index k o N entries ++ S.R (rg .dst)
  let S₂ : Stacks T A := { S₁ with R := Function.update (Function.update S₁.R (rg .dst) out) (rg .index) (binSyms Li (index + entries.length)) }
  obtain ⟨v₃, hu₃, he₃⟩ := sparseCursorRestore_exec body (rg .index) saved (rg .tx) (rg .ty) hregs
    Li (index + entries.length) index v₂ S₂
    (by simp [S₂]) (by simp [S₂, S₁, hsep])
    (by simp [S₂, S₁, (hsep .tx).symm, hrg.eq_iff, ht]) (by simp [S₂, S₁, (hsep .ty).symm, hrg.eq_iff, hw])
  have hf : Function.update (Function.update S₂.R (rg .index) (binSyms Li index)) saved [] =
      Function.update S.R (rg .dst) out := by
    funext j
    by_cases hs : j = saved
    · subst j; simp [hsep, hsaved]
    · by_cases hc : j = rg .index
      · subst j; simp [hs, hrg.eq_iff, hindex]
      · by_cases hd : j = rg .dst
        · subst j; simp [S₂, S₁, hs, hc]
        · simp [S₂, S₁, hs, hc, hd]
  rw [hf] at he₃
  refine ⟨v₃, (6 * Li + 6) + (n₂ + (10 * Li + 10)), hu₃.trans (hu₂.trans hu₁), by omega, ?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  convert he using 1; first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
