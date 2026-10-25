module

public import IntegerMultBounds.MathlibTM2.Host.SSMul
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! # Install table variables from ordinary binary input words

A structural list of padded copies reads caller words without consuming them.
The width counter and all scratch are restored; sources may be reused, including
one empty source for every zero-valued table variable.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Host.SS

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpBankCopies (width savedWidth savedSource buf : Fin T) : List (Fin T × Fin T) → Pr P T Q A U
  | [] => .act .done
  | (src, dst) :: ls => .seq (padCopy width src dst savedWidth savedSource buf (bitSymbol false))
      (chirpBankCopies width savedWidth savedSource buf ls)

def chirpBankCopiesR (W : ℕ) (value : Fin T → ℕ) (R : Fin T → List (Fin (A + 4))) :
    List (Fin T × Fin T) → Fin T → List (Fin (A + 4))
  | [] => R
  | (src, dst) :: ls => chirpBankCopiesR W value (Function.update R dst (binSyms W (value src) ++ R dst)) ls

def chirpBankCopiesCost (W : ℕ) (bits : Fin T → ℕ) (ls : List (Fin T × Fin T)) : ℕ :=
  (ls.map fun p => 6 * W + 2 * bits p.1 + 8).sum + 1

/-- Every padded copy executes; all caller source words, counters and scratch are kept. -/
theorem chirpBankCopies_exec {width savedWidth savedSource buf : Fin T}
    (ls : List (Fin T × Fin T))
    (hreg : ∀ p ∈ ls, [width, p.1, p.2, savedWidth, savedSource, buf].Nodup)
    (hsources : ∀ p ∈ ls, ∀ q ∈ ls, p.2 ≠ q.1)
    (W : ℕ) (bits value : Fin T → ℕ)
    (hfit : ∀ p ∈ ls, value p.1 < 2 ^ bits p.1) (hwidth : ∀ p ∈ ls, bits p.1 ≤ W)
    (v : HS T Q A U) (S : Stacks T A)
    (hw : (S.R width).length = W) (hsrc : ∀ p ∈ ls, S.R p.1 = binSyms (bits p.1) (value p.1))
    (hsw : S.R savedWidth = []) (hss : S.R savedSource = []) (hbuf : S.R buf = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (chirpBankCopies width savedWidth savedSource buf ls) (mk v S)
        (chirpBankCopiesCost W bits ls) (mk v' { S with R := chirpBankCopiesR W value S.R ls }) := by
  induction ls generalizing v S with
  | nil => exact ⟨v, rfl, Exec.act (body := body) .done (mk v S)⟩
  | cons p ls ih =>
    obtain ⟨src, dst⟩ := p
    have hr := hreg (src, dst) (by simp)
    have hr' := hr
    regs_ne hr'
    obtain ⟨v₁, hu₁, he₁⟩ := padCopy_exec (body := body)
      (show Dist5 width savedWidth src savedSource buf by
        constructor <;> first | assumption | (apply Ne.symm; assumption))
      ‹width ≠ dst›.symm ‹src ≠ dst›.symm
      ‹dst ≠ savedWidth› ‹dst ≠ savedSource› ‹dst ≠ buf›
      (bitSymbol false) v S hsw hss hbuf
      (by rw [hsrc (src, dst) (by simp), length_binSyms, hw]; exact hwidth (src, dst) (by simp))
    rw [hw, hsrc (src, dst) (by simp), length_binSyms,
      binSyms_append_replicate (hfit (src, dst) (by simp)) (hwidth (src, dst) (by simp))] at he₁
    let S₁ : Stacks T A := { S with R := Function.update S.R dst (binSyms W (value src) ++ S.R dst) }
    obtain ⟨v₂, hu₂, he₂⟩ := ih
      (fun p hp => hreg p (List.mem_cons_of_mem _ hp))
      (fun p hp q hq => hsources p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq))
      (fun p hp => hfit p (List.mem_cons_of_mem _ hp))
      (fun p hp => hwidth p (List.mem_cons_of_mem _ hp)) v₁ S₁
      (by simpa [S₁, ‹width ≠ dst›] using hw)
      (fun p hp => by
        simpa only [S₁, Function.update_of_ne (hsources (src, dst) (by simp) p (List.mem_cons_of_mem _ hp)).symm] using
          hsrc p (List.mem_cons_of_mem _ hp))
      (by simp [S₁, ‹dst ≠ savedWidth›.symm, hsw])
      (by simp [S₁, ‹dst ≠ savedSource›.symm, hss])
      (by simp [S₁, ‹dst ≠ buf›.symm, hbuf])
    exact ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by
      simp [chirpBankCopiesCost]; omega) rfl⟩

/-- Destinations are the only changed registers. -/
theorem chirpBankCopiesR_off (W : ℕ) (value : Fin T → ℕ) (R : Fin T → List (Fin (A + 4)))
    (ls : List (Fin T × Fin T)) (k : Fin T) (hk : ∀ p ∈ ls, p.2 ≠ k) :
    chirpBankCopiesR W value R ls k = R k := by
  induction ls generalizing R with
  | nil => rfl
  | cons p ls ih =>
    rw [chirpBankCopiesR, ih _ (fun q hq => hk q (List.mem_cons_of_mem _ hq))]
    exact Function.update_of_ne (hk p (by simp)).symm _ _

/-- A distinct destination receives exactly its assigned input word at the target width. -/
theorem chirpBankCopiesR_at (W : ℕ) (value : Fin T → ℕ) (R : Fin T → List (Fin (A + 4)))
    (ls : List (Fin T × Fin T)) (hnd : (ls.map Prod.snd).Nodup)
    (p : Fin T × Fin T) (hp : p ∈ ls) :
    chirpBankCopiesR W value R ls p.2 = binSyms W (value p.1) ++ R p.2 := by
  induction ls generalizing R with
  | nil => simp at hp
  | cons q ls ih =>
    have hn := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hp with he | hp
    · subst p
      rw [chirpBankCopiesR, chirpBankCopiesR_off W value _ ls q.2 (by
        intro p hp he
        exact hn.1 (List.mem_map.mpr ⟨p, hp, he⟩))]
      exact Function.update_self ..
    · rw [chirpBankCopiesR, ih _ hn.2 hp]
      have hne : p.2 ≠ q.2 := by
        intro he
        exact hn.1 (List.mem_map.mpr ⟨p, hp, he⟩)
      rw [Function.update_of_ne hne]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
