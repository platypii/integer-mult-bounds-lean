module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRhsSeed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowData

/-! # Initialize the actual integer column and its iteration header -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def initializeIntegerColumn : Pr P₀ 117 Q A U :=
  .seq (generateSeed 102 94 114 110 99 104 106 105) (.act (pushOne 116))

def initializedColumn {A : ℕ} (S : Stacks 117 A) (w : ℕ) (xs : List GaussianInt) : Stacks 117 A :=
  { S with R := (Function.update (Function.update S.R 110 (cstream A w xs ++ S.R 110)) 116 [tick]) }

theorem initializeIntegerColumn_exec (P s t u band L w : ℕ) (hL : 0 < L) (hP : P < w)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hrows : (S.R 102).length = L) (hwidth : (S.R 94).length = w)
    (hprecision : (S.R 114).length = P) (hiteration : S.R 116 = [])
    (hfresh : ∀ k ∈ [(99 : Fin 117), 104, 105, 106], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 10 * (L * w) + 9 * L + 6 * P + 18 ∧
      Exec body initializeIntegerColumn (mk v S) m
        (mk v' (initializedColumn S w (rowColumnWords P s t u band L 1))) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateSeed_exec (body := body)
    (show [(102 : Fin 117), 94, 114, 110, 99, 104, 106, 105].Nodup by decide)
    L w P hL hP v S hrows hwidth hprecision
    (hfresh 99 (by simp)) (hfresh 104 (by simp)) (hfresh 106 (by simp)) (hfresh 105 (by simp))
  have hseed : seedWords P L = rowColumnWords P s t u band L 1 := by
    rw [rowColumnWords_eq, seedWords_eq_column]
  rw [hseed] at he₁
  let S₁ : Stacks 117 A := { S with R := (Function.update S.R 110
    (cstream A w (rowColumnWords P s t u band L 1) ++ S.R 110)) }
  have hpush : (pushOne 116 : Act 117 Q A U).run (mk v₁ S₁) =
      mk v₁ (initializedColumn S w (rowColumnWords P s t u band L 1)) := by
    simp [pushOne, Action.run, update_rt, S₁, initializedColumn, hiteration]
  exact ⟨v₁, m₁ + 1, hu₁, by omega,
    Exec.seq he₁ (hpush ▸ Exec.act (body := body) (pushOne 116) (mk v₁ S₁))⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
