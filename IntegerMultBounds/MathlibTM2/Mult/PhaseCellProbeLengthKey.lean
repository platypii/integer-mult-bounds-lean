module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateOriginControls

/-! Probe the generated row count of an installed length key. Empty classes
leave the original bank unchanged, so the outer iterator can skip their solver. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def probeLengthKey : Pr P₀ 117 Q A U := .seq generateOriginControls (.act (peekR 116))

theorem probeLengthKey_exec (P q s t u band L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ v'.flag = decide (0 < (naturalLengthGroup s t band L).length) ∧ m ≤ generateOriginControlsCost P q s t u band L+1 ∧
      Exec body probeLengthKey (mk v S) m
        (mk v' { S with R := originControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band L S.R }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateOriginControls_exec (body := body)
    P q s t u band L hP hs hst hu hband hL hLs hA v S hPSrc hq hsSrc htSrc huSrc hbSrc hLSrc hblank hfresh
  let S₁ : Stacks 117 A := { S with R := originControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band L S.R }
  have hflag : (S₁.R 116).head?.isSome = decide (0 < (naturalLengthGroup s t band L).length) := by
    cases he : (naturalLengthGroup s t band L).length <;> simp [S₁, originControlsR, he]
  have hp := Exec.act (body := body) (peekR 116) (mk v₁ S₁)
  rw [peekR_run, hflag] at hp
  exact ⟨{ v₁ with flag := decide (0 < (naturalLengthGroup s t band L).length) },
    m₁+1, hu₁, rfl, by omega, Exec.seq he₁ hp⟩

theorem originControlsR_empty (V s t band L : ℕ) (R : Fin 117 → List (Fin (A+4)))
    (hB : (naturalLengthGroup s t band L).length = 0) (h116 : R 116 = []) :
    originControlsR A V s t band L R = R := by
  have hp : naturalOriginPackets A V s t band L = [] := List.eq_nil_of_length_eq_zero (by simp [hB])
  funext k
  by_cases h116k : k = 116
  · subst k; simp [originControlsR, hB, h116]
  simp [originControlsR, hB, hp, h116k]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
