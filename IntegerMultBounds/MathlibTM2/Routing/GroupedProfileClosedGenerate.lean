module

public import IntegerMultBounds.MathlibTM2.Routing.AffineProfileClosedGenerate
public import IntegerMultBounds.MathlibTM2.Routing.GroupedProfileTerminal

/-! A closed grouped-profile generator handles zero and positive bases and empty
profiles using the existing live tests. Only the coordinate output changes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
variable {T Q A W m : ℕ} {P U : Type}

def groupedProfileClosedProgram (rg : GroupedProfileReg → Fin T) (saved : Fin T) : Pr P T Q A U :=
  .seq (binaryZeroTestProgram (rg (.coordinate (.arithmetic .base))) (rg (.coordinate (.arithmetic .dst))) (rg (.coordinate (.arithmetic .tx))) (rg (.coordinate (.arithmetic .ty))) (rg (.coordinate (.arithmetic .tz))) (rg (.coordinate .gap)))
    (.cond (fun v => symBit (v.scan (rg (.coordinate .gap))))
      (.seq (.act (peekR (rg .src)))
        (.cond (·.flag) (groupedProfileGenerateProgram rg saved) (groupedProfileTerminalProgram rg saved)))
      (groupedProfileTerminalProgram rg saved))

def groupedProfileClosedCost (Li Lg Lk Ls m : ℕ) :=
  m * (groupedProfileCallCost Li Lg Lk Ls + 2) + 2 * (m * (Ls + 3)) + 16 * Li + 20 +
    (36 * (Li + Lk) + 12 * Ls + 54)

theorem groupedProfileClosed_exec (body : P → Pr P T Q A U)
    (rg : GroupedProfileReg → Fin T) (hrg : Function.Injective rg)
    (saved : Fin T) (hsep : ∀ r, saved ≠ rg r)
    (Li Lg Lk Ls g k o N : ℕ) (src : Fin m → Option (Fin W))
    (hg : g < 2^Lg) (hgpositive : 0 < g) (hk : k < 2 ^ Lk) (hwidth : Lg ≤ Li+Lk) (hN : N < 2 ^ (Li + Lk))
    (ho : o < 2 ^ (Li + Lk)) (hpositive : 0 < N)
    (hi : m ≤ 2 ^ Li) (hpos : ∀ j : Fin m, j.val / g * k + (j.val % g + o) < N)
    (hW : W + 1 < 2 ^ Ls)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R (rg .src) = affineProfileFrames Ls (affineSourceProfile src)) (harchive : S.R (rg .archive) = [])
    (hindex : S.R (rg (.coordinate (.arithmetic .index))) = binSyms Li 0)
    (hgroup : S.R (rg (.coordinate (.arithmetic .group))) = binSyms Lg g)
    (hstride : S.R (rg (.coordinate (.arithmetic .stride))) = binSyms Lk k) (hoffset : S.R (rg (.coordinate (.arithmetic .base))) = binSyms (Li + Lk) o)
    (hlast : S.R (rg (.coordinate .last)) = binSyms (Li + Lk) (N - 1)) (hone : S.R (rg (.coordinate .one)) = binSyms Ls 1)
    (hsaved : S.R saved = [])
    (hblank : ∀ r, r ∉ groupedProfileLive → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ groupedProfileClosedCost Li Lg Lk Ls m ∧
      Exec body (groupedProfileClosedProgram rg saved) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg (.coordinate .dst)) (sparseCoordinateFrames (Li + Lk) Ls
          (sparseCoordinateValues (sparseCoordinateClose N (sparsePatternCoordinates (N := N)
            (fun j => j / g * k + (j % g + o)) src))) ++ S.R (rg (.coordinate .dst))) }) := by
  obtain ⟨v₁, hu₁, hc₁, he₁⟩ := binaryZeroTest_exec body
    (rg (.coordinate (.arithmetic .base))) (rg (.coordinate (.arithmetic .dst))) (rg (.coordinate (.arithmetic .tx))) (rg (.coordinate (.arithmetic .ty))) (rg (.coordinate (.arithmetic .tz))) (rg (.coordinate .gap))
    (by simp [List.nodup_cons, hrg.eq_iff]) (by simp [hrg.eq_iff]) (by simp [hrg.eq_iff])
    (Li + Lk) o ho v S hoffset
    (by apply hblank; simp [groupedProfileLive]) (by apply hblank; simp [groupedProfileLive])
    (by apply hblank; simp [groupedProfileLive]) (by apply hblank; simp [groupedProfileLive])
  by_cases hz : o = 0
  · subst o
    let v₂ := { v₁ with flag := decide (0 < m) }
    have hp : (peekR (rg .src) : Act T Q A U).run (mk v₁ S) = mk v₂ S := by
      simp only [peekR_run, hsrc, affineSourceProfile_flag]; rfl
    have hc : symBit (v₁.scan (rg (.coordinate .gap))) = true := by rw [hc₁]; simp
    by_cases hm : 0 < m
    · obtain ⟨v₃, n₃, hu₃, ht₃, he₃⟩ := groupedSourceProfileGenerate_exec body rg hrg saved hsep
        Li Lg Lk Ls 0 g k 0 N src hg hgpositive hk hwidth hN (by simpa using hi) (by simpa using hpos) hW v₂ S
        hsrc harchive hindex hgroup hstride hoffset hlast hone hsaved hblank
      have hclose := sparseCoordinateClose_zero (N := N) hm (fun j => j / g * k + (j % g + 0)) (by simp) src
      simp only [Nat.zero_add] at he₃
      rw [← hclose] at he₃
      refine ⟨v₃, (14 * (Li + Lk) + 14) + (1 + ((1 + (n₃ + 1)))), hu₃.trans hu₁,
        by dsimp only [groupedProfileClosedCost]; omega, ?_⟩
      have he := Exec.seq he₁ (Exec.cond_true
        (f := fun v => symBit (v.scan (rg (.coordinate .gap)))) (q := groupedProfileTerminalProgram rg saved)
        (by simpa only [mk_var] using hc)
        (Exec.seq (hp ▸ Exec.act (body := body) (peekR (rg .src)) (mk v₁ S))
          (Exec.cond_true (f := (·.flag)) (q := groupedProfileTerminalProgram rg saved) (by simp [v₂, hm]) he₃)))
      exact Exec.cast he (by omega) rfl
    · have hempty : m = 0 := by omega
      have hpos' : ∀ j : Fin m, 0 < (0 + j.val) / g * k + ((0 + j.val) % g + 0) ∧ (0 + j.val) / g * k + ((0 + j.val) % g + 0) < N := by
        intro j; have hj := j.isLt; omega
      obtain ⟨v₃, n₃, hu₃, ht₃, he₃⟩ := groupedProfileTerminal_exec body rg hrg saved hsep
        Li Lg Lk Ls 0 g k 0 N src hg hgpositive hk hwidth hN hpositive (by simpa using hi) hpos' hW v₂ S
        hsrc harchive hindex hgroup hstride hoffset hlast hone hsaved hblank
      simp only [Nat.zero_add] at he₃
      refine ⟨v₃, (14 * (Li + Lk) + 14) + (1 + (1 + (n₃ + 1))), hu₃.trans hu₁,
        by dsimp only [groupedProfileClosedCost]; omega, ?_⟩
      have he := Exec.seq he₁ (Exec.cond_true
        (f := fun v => symBit (v.scan (rg (.coordinate .gap)))) (q := groupedProfileTerminalProgram rg saved)
        (by simpa only [mk_var] using hc)
        (Exec.seq (hp ▸ Exec.act (body := body) (peekR (rg .src)) (mk v₁ S))
          (Exec.cond_false (f := (·.flag)) (p := groupedProfileGenerateProgram rg saved) (by simp [v₂, hm]) he₃)))
      exact Exec.cast he (by omega) rfl
  · have hc : symBit (v₁.scan (rg (.coordinate .gap))) = false := by rw [hc₁]; simp [hz]
    have hpos' : ∀ j : Fin m, 0 < (0 + j.val) / g * k + ((0 + j.val) % g + o) ∧ (0 + j.val) / g * k + ((0 + j.val) % g + o) < N := by
      intro j
      simp only [Nat.zero_add]
      exact ⟨by omega, hpos j⟩
    obtain ⟨v₂, n₂, hu₂, ht₂, he₂⟩ := groupedProfileTerminal_exec body rg hrg saved hsep
      Li Lg Lk Ls 0 g k o N src hg hgpositive hk hwidth hN hpositive (by simpa using hi) hpos' hW v₁ S
      hsrc harchive hindex hgroup hstride hoffset hlast hone hsaved hblank
    simp only [Nat.zero_add] at he₂
    refine ⟨v₂, (14 * (Li + Lk) + 14) + (n₂ + 1), hu₂.trans hu₁,
      by dsimp only [groupedProfileClosedCost]; omega, ?_⟩
    exact Exec.seq he₁ (Exec.cond_false (by simpa only [mk_var] using hc) he₂)


end IntegerMultBounds.MathlibTM2.Routing
