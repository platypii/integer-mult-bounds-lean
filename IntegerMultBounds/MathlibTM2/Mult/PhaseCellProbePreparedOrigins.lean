module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareOriginControls

/-! Probe the generated row count while retaining origins and width headers
for either the nonempty continuation or empty-class release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def probePreparedOrigins : Pr P₀ 117 Q A U := .seq prepareOriginControls (.act (peekR 116))

theorem probePreparedOrigins_exec (P q s t u band L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ v'.flag = decide (0 < (naturalLengthGroup s t band L).length) ∧ m ≤ prepareOriginControlsCost P q s t u band L+1 ∧
      Exec body probePreparedOrigins (mk v S) m
        (mk v' { S with R := preparedOriginR A P q s t u band L S.R }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := prepareOriginControls_exec (body := body)
    P q s t u band L hP hs hst hu hband hL hLs hA v S hPSrc hq hsSrc htSrc huSrc hbSrc hLSrc hblank hfresh
  let S₁ : Stacks 117 A := { S with R := preparedOriginR A P q s t u band L S.R }
  have hflag : (S₁.R 116).head?.isSome = decide (0 < (naturalLengthGroup s t band L).length) := by
    cases he : (naturalLengthGroup s t band L).length <;> simp [S₁, preparedOriginR, originControlsR, he]
  have hp := Exec.act (body := body) (peekR 116) (mk v₁ S₁)
  rw [peekR_run, hflag] at hp
  exact ⟨{ v₁ with flag := decide (0 < (naturalLengthGroup s t band L).length) },
    m₁+1, hu₁, rfl, by omega, Exec.seq he₁ hp⟩

theorem preparedOriginR_empty (P q s t u band L : ℕ) (R : Fin 117 → List (Fin (A+4)))
    (hB : (naturalLengthGroup s t band L).length = 0) (h116 : R 116 = []) :
    preparedOriginR A P q s t u band L R =
      Function.update (Function.update R 94 (List.replicate (2*q+8) tick)) 115
        (List.replicate (weightWorkspaceWidth P q (2*q+8) t u) tick) := by
  have hp : naturalOriginPackets A (weightWorkspaceWidth P q (2*q+8) t u) s t band L = [] :=
    List.eq_nil_of_length_eq_zero (by simp [hB])
  funext k
  by_cases hk : k = 116
  · subst k; simp [preparedOriginR,originControlsR,hB,h116]
  by_cases hk109 : k = 109
  · subst k; simp [preparedOriginR,originControlsR,hB,hp]
  simp [preparedOriginR,originControlsR,hB,hp,Function.update_apply,hk,hk109]

theorem releaseEmptyPreparedOrigins_exec (P q s t u band L : ℕ)
    (hB : (naturalLengthGroup s t band L).length = 0) (v : HS 117 Q A U) (S : Stacks 117 A)
    (h94 : S.R 94 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (clearWords [94,115])
        (mk v { S with R := preparedOriginR A P q s t u band L S.R })
        (2*((2*q+8)+weightWorkspaceWidth P q (2*q+8) t u)+5) (mk v' S) := by
  let S₁ : Stacks 117 A := { S with R := preparedOriginR A P q s t u band L S.R }
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [(94 : Fin 117),115] (by decide) v S₁
  refine ⟨v',hu,he.cast ?_ ?_⟩
  · simp [S₁,preparedOriginR,originControlsR]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [S₁,preparedOriginR_empty P q s t u band L S.R hB h116]
    by_cases hk94 : k = 94
    · subst k; simp [h94]
    by_cases hk115 : k = 115
    · subst k; simp [h115]
    simp [hk94,hk115]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
