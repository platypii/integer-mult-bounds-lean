module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileComplete
public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileTerminal
public import IntegerMultBounds.MathlibTM2.Routing.BinaryZeroTest

/-! One fixed generator handles zero and positive offsets, including empty
profiles. Live tests decide whether the terminal zero frame is needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A W m : ℕ} {P U : Type}

theorem affineSourceProfile_flag (Ls : ℕ) (src : Fin m → Option (Fin W)) :
    (affineProfileFrames (A := A) Ls (affineSourceProfile src)).head?.isSome = decide (0 < m) := by
  have hl : (affineProfileFrames (A := A) Ls (affineSourceProfile src)).length = m * (Ls + 3) := by
    rw [affineProfileFrames_length]
    simp only [affineSourceProfile, List.length_ofFn]
  cases he : affineProfileFrames (A := A) Ls (affineSourceProfile src) with
  | nil =>
    have hm : m = 0 := by
      rw [he] at hl
      simp only [List.length_nil] at hl
      rcases Nat.mul_eq_zero.mp (by omega : m * (Ls + 3) = 0) with hm | hz
      · exact hm
      · omega
    simp [hm]
  | cons x xs =>
    have hm : 0 < m := by
      rw [he] at hl
      by_contra hm
      have hmzero : m = 0 := by omega
      simp [hmzero] at hl
    simp [hm]

def affineProfileClosedProgram (rg : AffineProfileReg → Fin T) (saved : Fin T) : Pr P T Q A U :=
  .seq (binaryZeroTestProgram (rg .offset) (rg .pos) (rg .tx) (rg .ty) (rg .tz) (rg .gap))
    (.cond (fun v => symBit (v.scan (rg .gap)))
      (.seq (.act (peekR (rg .src)))
        (.cond (·.flag) (affineProfileGenerateProgram rg saved) (affineProfileTerminalProgram rg saved)))
      (affineProfileTerminalProgram rg saved))

def affineProfileClosedCost (Li Lk Ls m : ℕ) :=
  m * (affineProfileCallCost Li Lk Ls + 2) + 2 * (m * (Ls + 3)) + 16 * Li + 20 +
    (36 * (Li + Lk) + 12 * Ls + 54)

theorem affineProfileClosed_exec (body : P → Pr P T Q A U)
    (rg : AffineProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lk Ls k o N : ℕ) (src : Fin m → Option (Fin W))
    (hk : k < 2 ^ Lk) (hN : N < 2 ^ (Li + Lk))
    (ho : o < 2 ^ (Li + Lk)) (hpositive : 0 < N)
    (hi : m ≤ 2 ^ Li) (hpos : ∀ j : Fin m, j.val * k + o < N)
    (hW : W + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls (affineSourceProfile src)) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg .index) = binSyms Li 0)
    (hstride : S.R (rg .stride) = binSyms Lk k) (hoffset : S.R (rg .offset) = binSyms (Li + Lk) o)
    (hlast : S.R (rg .last) = binSyms (Li + Lk) (N - 1)) (hone : S.R (rg .one) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ≠ .src → r ≠ .archive → r ≠ .index → r ≠ .stride →
      r ≠ .offset → r ≠ .last → r ≠ .one → r ≠ .dst → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ affineProfileClosedCost Li Lk Ls m ∧
      Exec body (affineProfileClosedProgram rg saved) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg .dst) (sparseCoordinateFrames (Li + Lk) Ls
          (sparseCoordinateValues (sparseCoordinateClose N (sparsePatternCoordinates (N := N)
            (fun j => j * k + o) src))) ++ S.R (rg .dst)) }) := by
  obtain ⟨v₁, hu₁, hc₁, he₁⟩ := binaryZeroTest_exec body
    (rg .offset) (rg .pos) (rg .tx) (rg .ty) (rg .tz) (rg .gap)
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    (Li + Lk) o ho v S hoffset
    (by apply hblank <;> decide) (by apply hblank <;> decide)
    (by apply hblank <;> decide) (by apply hblank <;> decide)
  by_cases hz : o = 0
  · subst o
    let v₂ := { v₁ with flag := decide (0 < m) }
    have hp : (peekR (rg .src) : Act T Q A U).run (mk v₁ S) = mk v₂ S := by
      simp only [peekR_run, hsrc, affineSourceProfile_flag]; rfl
    have hc : symBit (v₁.scan (rg .gap)) = true := by rw [hc₁]; simp
    by_cases hm : 0 < m
    · obtain ⟨v₃, n₃, hu₃, ht₃, he₃⟩ := affineSourceProfileGenerate_exec body rg hrg saved hsep
        Li Lk Ls 0 k 0 N src hk hN (by simpa using hi) (by simpa using hpos) hW v₂ S
        hsrc harchive hindex hstride hoffset hlast hone hsaved hblank
      have hclose := sparseCoordinateClose_zero (N := N) hm (fun j => j * k + 0) (by simp) src
      simp only [Nat.zero_add] at he₃
      rw [← hclose] at he₃
      refine ⟨v₃, (14 * (Li + Lk) + 14) + (1 + ((1 + (n₃ + 1)))), hu₃.trans hu₁,
        by dsimp only [affineProfileClosedCost]; omega, ?_⟩
      have he := Exec.seq he₁ (Exec.cond_true
        (f := fun v => symBit (v.scan (rg .gap))) (q := affineProfileTerminalProgram rg saved)
        (by simpa only [mk_var] using hc)
        (Exec.seq (hp ▸ Exec.act (body := body) (peekR (rg .src)) (mk v₁ S))
          (Exec.cond_true (f := (·.flag)) (q := affineProfileTerminalProgram rg saved) (by simp [v₂, hm]) he₃)))
      exact Exec.cast he (by omega) rfl
    · have hempty : m = 0 := by omega
      have hpos' : ∀ j : Fin m, 0 < (0 + j.val) * k + 0 ∧ (0 + j.val) * k + 0 < N := by
        intro j; have hj := j.isLt; omega
      obtain ⟨v₃, n₃, hu₃, ht₃, he₃⟩ := affineProfileTerminal_exec body rg hrg saved hsep
        Li Lk Ls 0 k 0 N src hk hN hpositive (by simpa using hi) hpos' hW v₂ S
        hsrc harchive hindex hstride hoffset hlast hone hsaved hblank
      simp only [Nat.zero_add] at he₃
      refine ⟨v₃, (14 * (Li + Lk) + 14) + (1 + (1 + (n₃ + 1))), hu₃.trans hu₁,
        by dsimp only [affineProfileClosedCost]; omega, ?_⟩
      have he := Exec.seq he₁ (Exec.cond_true
        (f := fun v => symBit (v.scan (rg .gap))) (q := affineProfileTerminalProgram rg saved)
        (by simpa only [mk_var] using hc)
        (Exec.seq (hp ▸ Exec.act (body := body) (peekR (rg .src)) (mk v₁ S))
          (Exec.cond_false (f := (·.flag)) (p := affineProfileGenerateProgram rg saved) (by simp [v₂, hm]) he₃)))
      exact Exec.cast he (by omega) rfl
  · have hc : symBit (v₁.scan (rg .gap)) = false := by rw [hc₁]; simp [hz]
    have hpos' : ∀ j : Fin m, 0 < (0 + j.val) * k + o ∧ (0 + j.val) * k + o < N := by
      intro j
      simp only [Nat.zero_add]
      exact ⟨by omega, hpos j⟩
    obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := affineProfileTerminal_exec body rg hrg saved hsep
      Li Lk Ls 0 k o N src hk hN hpositive (by simpa using hi) hpos' hW v₁ S
      hsrc harchive hindex hstride hoffset hlast hone hsaved hblank
    simp only [Nat.zero_add] at he₂
    refine ⟨v₂, (14 * (Li + Lk) + 14) + (n₂ + 1), hu₂.trans hu₁,
      by dsimp only [affineProfileClosedCost]; omega, ?_⟩
    exact Exec.seq he₁ (Exec.cond_false (by simpa only [mk_var] using hc) he₂)

end IntegerMultBounds.MathlibTM2.Routing
