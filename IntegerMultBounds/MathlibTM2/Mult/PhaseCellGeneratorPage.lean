module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedGeneratorSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseGeneratorPage

/-! # Layout and release of the constructed generator page -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[simp] theorem generatorPage_length (A P s t u band L q n : ℕ) :
    (generatorPage A P s t u band L q n).length = (2 * L + 1) * (2 * q + 8) := by
  simp [generatorPage, csyms]; ring

/-- The two banks and scalar have exactly the runtime fetch offsets. -/
theorem generatorPage_reads (A P s t u band L q n : ℕ) (tail : List (Fin (A + 4))) :
    let page := generatorPage A P s t u band L q n ++ tail
    page.take (L * (2 * q + 8)) = cstream A (2 * q + 8) (columnWords P s t u band L q n) ∧
    (page.drop (L * (2 * q + 8))).take (L * (2 * q + 8)) =
      cstream A (2 * q + 8) (reversedColumnWords P s t u band L q n) ∧
    (page.drop (2 * L * (2 * q + 8))).take (2 * q + 8) =
      csyms A (2 * q + 8) (reciprocalWord P s t u band L q n) := by
  let xs := cstream A (2 * q + 8) (columnWords P s t u band L q n)
  let ys := cstream A (2 * q + 8) (reversedColumnWords P s t u band L q n)
  let a := csyms A (2 * q + 8) (reciprocalWord P s t u band L q n)
  have hx : xs.length = L * (2 * q + 8) := by simp [xs]
  have hy : ys.length = L * (2 * q + 8) := by simp [ys]
  have ha : a.length = 2 * q + 8 := by simp [a]
  change ((xs ++ (ys ++ a)) ++ tail).take _ = _ ∧
    (((xs ++ (ys ++ a)) ++ tail).drop _).take _ = _ ∧
    (((xs ++ (ys ++ a)) ++ tail).drop _).take _ = _
  rw [List.append_assoc, List.append_assoc, ← hx]
  simp only [List.take_left, List.drop_left]
  refine ⟨rfl, ?_, ?_⟩
  · rw [show xs.length = ys.length by omega, List.take_left]
  · have htwo : 2 * L * (2 * q + 8) = xs.length + ys.length := by rw [hx, hy]; ring
    rw [htwo, ← List.drop_drop, List.drop_left, List.drop_left, ← ha, List.take_left]
    rw [ha]

/-- Releasing the constructed page recovers the original payload. Retained
setup counters, iteration header and factor page are unchanged by this release. -/
theorem releasePackedGeneratorBank_exec (P s t u band L q W n : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hrows : (S.R 102).length = L) (hq : (S.R 112).length = q)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseGeneratorPageCost L q ∧
      Exec body releaseGeneratorPage (mk v (packedGeneratorBank S P s t u band L q W n)) m
        (mk v' { S with R := (Function.update (counterR 0 W S.R) 116 (List.replicate n tick)) }) := by
  let S₁ := packedGeneratorBank S P s t u band L q W n
  obtain ⟨v', m, hu, hm, he⟩ := releaseGeneratorPage_exec (body := body) L q
    (generatorPage A P s t u band L q n) (S.R 110) v S₁
    (by simpa [S₁, packedGeneratorBank, counterR, cr, OutputPlacement.code] using hrows)
    (by simpa [S₁, packedGeneratorBank, counterR, cr, OutputPlacement.code] using hq)
    (generatorPage_length A P s t u band L q n) (by simp [S₁, packedGeneratorBank]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        simpa [S₁, packedGeneratorBank, counterR, cr, OutputPlacement.code] using hfresh _ (by simp))
  refine ⟨v', m, hu, hm, he.cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hx : k = 110
  · subst k; simp [counterR, cr, OutputPlacement.code]
  simp [S₁, packedGeneratorBank, hx, Function.update_apply]

/-- Release the runtime page and every counter introduced by generator setup. -/
def releasePackedSetup : Pr P₀ 117 Q A U :=
  .seq releaseGeneratorPage (clearWords [cr .wn, cr .pn, cr .nn, 116])

def releasePackedSetupCost (L q W n : ℕ) : ℕ :=
  releaseGeneratorPageCost L q + 2 * (W + Schoenhage.Schedule.topN W + n) + 9

/-- Setup teardown restores the complete original bank, including factor-page
storage, unary header symbols and every borrowed payload suffix. -/
theorem releasePackedSetup_exec (P s t u band L q W n : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hrows : (S.R 102).length = L) (hq : (S.R 112).length = q)
    (hblank : ∀ r, S.R (cr r) = []) (hiteration : S.R 116 = [])
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releasePackedSetupCost L q W n ∧
      Exec body releasePackedSetup (mk v (packedGeneratorBank S P s t u band L q W n)) m (mk v' S) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := releasePackedGeneratorBank_exec (body := body)
    P s t u band L q W n v S hrows hq hfresh
  let S₁ : Stacks 117 A := { S with R := (Function.update (counterR 0 W S.R) 116 (List.replicate n tick)) }
  obtain ⟨v₂, hu₂, he₂⟩ := clearWords_exec (body := body) [cr .wn, cr .pn, cr .nn, 116]
    (by decide) v₁ S₁
  have hsum : ([cr .wn, cr .pn, cr .nn, (116 : Fin 117)].map (fun k => (S₁.R k).length)).sum =
      W + Schoenhage.Schedule.topN W + n := by
    simp [S₁, counterR, cr, OutputPlacement.code]
    omega
  refine ⟨v₂, m₁ + (2 * (W + Schoenhage.Schedule.topN W + n) + 9), hu₂.trans hu₁,
    by unfold releasePackedSetupCost; omega, (Exec.seq he₁ he₂).cast (by rw [hsum]; rfl) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases h116 : k = 116
  · subst k; simp [hiteration]
  by_cases hwn : k = cr .wn
  · subst k; simp [hblank .wn]
  by_cases hpn : k = cr .pn
  · subst k; simp [hblank .pn]
  by_cases hnn : k = cr .nn
  · subst k; simp [hblank .nn]
  simp [S₁, counterR, h116, hwn, hpn, hnn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
