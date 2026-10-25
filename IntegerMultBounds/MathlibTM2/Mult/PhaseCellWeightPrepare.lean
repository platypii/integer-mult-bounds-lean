module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarPrepare
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease

/-! # Execute weight-multiplier readiness at the combined shift precision

A retained unary normalization descriptor on port 116 is temporarily copied
above the grid precision header. The existing setup generates readiness for
`q+b`, then the temporary prefix is released, preserving both original headers.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def prepareWeights : Pr P 117 Q A U :=
  .seq (copyR 116 100 26 id) (.seq prepare (releasePrefix 116 100 26 27))

def prepareWeightsCost (q b w : ℕ) : ℕ := prepareCost (q + b) w + 10 * b + 10

/-- Execute the combined precision setup. The only retained changes are the
three multiplier counters; the actual grid and normalization headers survive. -/
theorem prepareWeights_exec (q b w : ℕ) (hq : 1 ≤ q) (hw : q + b + 4 ≤ w)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hqR : (S.R 100).length = q) (hbR : (S.R 116).length = b) (hwR : (S.R 94).length = w)
    (hclean : ∀ k : Fin 117, k.val < 28 → S.R k = [])
    (hcounters : ∀ r ∈ [CR.wn, .pn, .nn], S.R (cr r) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareWeightsCost q b w ∧
      Exec body prepareWeights (mk v S) m (mk v' { S with R := counterR (q + b) w S.R }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := copyR_exec body 116 100 26 (by decide) (by decide) (by decide)
    id v S (hclean 26 (by decide))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 100 ((S.R 116).reverse ++ S.R 100) }
  have he₁' : Exec body (copyR 116 100 26 id) (mk v S) (4 * b + 4) (mk v₁ S₁) := by
    simpa only [S₁, List.map_id, hbR] using he₁
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := prepare_exec (body := body) (q + b) w (by omega) hw v₁ S₁
    (by simp [S₁, hqR, hbR, Nat.add_comm]) (by simpa [S₁] using hwR)
    (by intro k hk; simp [S₁, show k ≠ (100 : Fin 117) by intro h; subst k; omega, hclean k (by omega)])
    (by
      intro r hr
      have hn : cr r ≠ (100 : Fin 117) := by
        intro h
        have hh := (cr_range r).2.1
        have he := congrArg (fun k : Fin 117 => k.val) h
        omega
      simpa only [S₁, Function.update_of_ne hn] using hcounters r hr)
  let S₂ : Stacks 117 A := { S₁ with R := counterR (q + b) w S₁.R }
  obtain ⟨v₃, hu₃, he₃⟩ := releasePrefix_exec (body := body)
    (count := 116) (src := 100) (saved := 26) (tmp := 27) (by decide)
    v₂ S₂ (S.R 116).reverse (S.R 100)
    (by simp [S₂, S₁, counterR, cr, OutputPlacement.code])
    (by simp [S₂, S₁, counterR, cr, OutputPlacement.code])
    (by simp [S₂, S₁, counterR, cr, OutputPlacement.code, hclean 26 (by decide)])
    (by simp [S₂, S₁, counterR, cr, OutputPlacement.code, hclean 27 (by decide)])
  refine ⟨v₃, (4 * b + 4) + (m₂ + (6 * b + 6)), hu₃.trans (hu₂.trans hu₁), ?_, ?_⟩
  · unfold prepareWeightsCost
    omega
  · refine (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by simp [hbR]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = (100 : Fin 117)
    · subst k
      simp [S₂, S₁, counterR, cr, OutputPlacement.code]
    · simp [S₂, S₁, counterR, cr, OutputPlacement.code, Function.update_apply, hk]

/-- Release exactly the three installed readiness counters. -/
def releaseWeightCounters : Pr P 117 Q A U := clearWords [90, 91, 92]

def releaseWeightCountersCost (p w : ℕ) : ℕ :=
  2 * (w + p + Schoenhage.Schedule.topN w) + 7

theorem releaseWeightCounters_exec (p w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (result : List (Fin (A + 4))) (hcounters : ∀ r ∈ [CR.wn, .pn, .nn], S.R (cr r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body releaseWeightCounters
        (mk v { S with R := Function.update (counterR p w S.R) 93 result })
        (releaseWeightCountersCost p w)
        (mk v' { S with R := Function.update S.R 93 result }) := by
  let S₀ : Stacks 117 A := { S with R := Function.update (counterR p w S.R) 93 result }
  obtain ⟨v', hu, he⟩ := clearWords_exec (body := body) [(90 : Fin 117), 91, 92] (by decide) v S₀
  have h90 : S.R 90 = [] := hcounters .wn (by simp)
  have h91 : S.R 91 = [] := hcounters .pn (by simp)
  have h92 : S.R 92 = [] := hcounters .nn (by simp)
  refine ⟨v', hu, he.cast ?_ ?_⟩
  · simp [S₀, counterR, cr, OutputPlacement.code, releaseWeightCountersCost, Nat.add_assoc]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk90 : k = (90 : Fin 117)
    · subst k; simp [S₀, h90]
    · by_cases hk91 : k = (91 : Fin 117)
      · subst k; simp [S₀, h91]
      · by_cases hk92 : k = (92 : Fin 117)
        · subst k; simp [S₀, h92]
        · simp [S₀, counterR, cr, OutputPlacement.code, Function.update_apply, hk90, hk91, hk92]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
