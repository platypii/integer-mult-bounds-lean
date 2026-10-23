module

public import IntegerMultBounds.MathlibTM2.Routing.GroupedProfileCompile
public import IntegerMultBounds.MathlibTM2.Routing.SparseCursorRestore

/-! Generate absolute coordinate frames from a live grouped activity/source profile,
restore the complete input and original index, and erase the saved index.
Only coordinate output changes; every phase is charged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def groupedProfileGenerateProgram (rg : GroupedProfileReg → Fin T) (saved : Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg (.coordinate (.arithmetic .index))) saved (rg (.coordinate (.arithmetic .tx))) (rg (.coordinate (.arithmetic .ty))))
    (.seq (groupedProfileCompileProgram rg) (sparseCursorRestoreProgram (rg (.coordinate (.arithmetic .index))) saved (rg (.coordinate (.arithmetic .tx))) (rg (.coordinate (.arithmetic .ty)))))

theorem groupedProfileGenerate_exec (body : P → Pr P T Q A U)
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lg Lk Ls index g k b N : ℕ) (entries : List (Bool × ℕ)) (hg : g < 2 ^ Lg) (hgpositive : 0 < g) (hk : k < 2 ^ Lk)
    (hwidth : Lg ≤ Li + Lk) (hN : N < 2 ^ (Li + Lk))
    (hready : GroupedProfileReady Li Ls g k b N index entries)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls entries) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg (.coordinate (.arithmetic .index))) = binSyms Li index)
    (hgroup : S.R (rg (.coordinate (.arithmetic .group))) = binSyms Lg g)
    (hstride : S.R (rg (.coordinate (.arithmetic .stride))) = binSyms Lk k) (hoffset : S.R (rg (.coordinate (.arithmetic .base))) = binSyms (Li + Lk) b)
    (hlast : S.R (rg (.coordinate .last)) = binSyms (Li + Lk) (N - 1)) (hone : S.R (rg (.coordinate .one)) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ∉ groupedProfileLive → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ entries.length * (groupedProfileCallCost Li Lg Lk Ls + 2) +
        2 * (affineProfileFrames (A := A) Ls entries).length + 16 * Li + 20 ∧
      Exec body (groupedProfileGenerateProgram rg saved) (mk v S)
        steps
        (mk v' { S with R := Function.update S.R (rg (.coordinate .dst)) (groupedProfileOutput Li Lg Lk Ls index g k b N entries ++ S.R (rg (.coordinate .dst))) }) := by
  have ht := hblank (.coordinate (.arithmetic .tx)) (by simp [groupedProfileLive])
  have hw := hblank (.coordinate (.arithmetic .ty)) (by simp [groupedProfileLive])
  have hregs : [rg (.coordinate (.arithmetic .index)), saved, rg (.coordinate (.arithmetic .tx)), rg (.coordinate (.arithmetic .ty))].Nodup := by
    simp [List.nodup_cons, hrg.eq_iff, hsep, Ne.symm (hsep (.coordinate (.arithmetic .index)))]
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec body hregs v S ht hw
  rw [hindex, hsaved, List.append_nil, length_binSyms] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R saved (binSyms Li index) }
  have hkeep (r : GroupedProfileReg) : S₁.R (rg r) = S.R (rg r) := Function.update_of_ne (hsep r).symm _ _
  obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := groupedProfileCompile_exec body rg hrg Li Lg Lk Ls index g k b N entries hg hgpositive hk hwidth hN hready v₁ S₁
    ((hkeep .src).trans hsrc) ((hkeep .archive).trans harchive) ((hkeep (.coordinate (.arithmetic .index))).trans hindex)
    ((hkeep (.coordinate (.arithmetic .group))).trans hgroup) ((hkeep (.coordinate (.arithmetic .stride))).trans hstride) ((hkeep (.coordinate (.arithmetic .base))).trans hoffset) ((hkeep (.coordinate .last)).trans hlast) ((hkeep (.coordinate .one)).trans hone)
    (by intro r hr; rw [hkeep]; exact hblank r hr)
  have hd : S₁.R (rg (.coordinate .dst)) = S.R (rg (.coordinate .dst)) := hkeep (.coordinate .dst)
  rw [hd] at he₂
  let out := groupedProfileOutput (A := A) Li Lg Lk Ls index g k b N entries ++ S.R (rg (.coordinate .dst))
  let S₂ : Stacks T A := { S₁ with R := Function.update (Function.update S₁.R (rg (.coordinate .dst)) out) (rg (.coordinate (.arithmetic .index))) (binSyms Li (index + entries.length)) }
  obtain ⟨v₃, hu₃, he₃⟩ := sparseCursorRestore_exec body (rg (.coordinate (.arithmetic .index))) saved (rg (.coordinate (.arithmetic .tx))) (rg (.coordinate (.arithmetic .ty))) hregs
    Li (index + entries.length) index v₂ S₂
    (by simp [S₂]) (by simp [S₂, S₁, hsep])
    (by simp [S₂, S₁, (hsep (.coordinate (.arithmetic .tx))).symm, hrg.eq_iff, ht]) (by simp [S₂, S₁, (hsep (.coordinate (.arithmetic .ty))).symm, hrg.eq_iff, hw])
  have hf : Function.update (Function.update S₂.R (rg (.coordinate (.arithmetic .index))) (binSyms Li index)) saved [] =
      Function.update S.R (rg (.coordinate .dst)) out := by
    funext j
    by_cases hs : j = saved
    · subst j; simp [hsep, hsaved]
    · by_cases hc : j = rg (.coordinate (.arithmetic .index))
      · subst j; simp [hs, hrg.eq_iff, hindex]
      · by_cases hd : j = rg (.coordinate .dst)
        · subst j; simp [S₂, S₁, hs, hc]
        · simp [S₂, S₁, hs, hc, hd]
  rw [hf] at he₃
  refine ⟨v₃, (6 * Li + 6) + (n₂ + (10 * Li + 10)), hu₃.trans (hu₂.trans hu₁), by omega, ?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  convert he using 1; first | omega | rfl

end IntegerMultBounds.MathlibTM2.Routing
