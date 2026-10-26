module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareHaloClassControls

/-! Generate the origins and owned count for one positive halo length class,
including both runtime widths, and release every temporary stack. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateHaloClassControls : Pr P₀ 117 Q A U :=
  .seq prepareHaloClassControls (clearWords [94,115])

def generateHaloClassControlsCost (P q s t u band a b L : ℕ) : ℕ :=
  prepareHaloClassControlsCost P q s t u band a b L+
    2*((2*q+8)+weightWorkspaceWidth P q (2*q+8) t u)+5

theorem generateHaloClassControls_exec (P q s t u band a b L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115,116], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateHaloClassControlsCost P q s t u band a b L ∧
      Exec body generateHaloClassControls (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R 109
          (haloOriginPackets A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L ++ S.R 109)) 116 (List.replicate (haloLengthGroup s t band a b L).length tick)) }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareHaloClassControls_exec (body := body)
    P q s t u band a b L hP hs hst hu hband has hbs hL hLs hA v S
    hPSrc hq hsSrc htSrc huSrc hbSrc haSrc hbEndSrc hLSrc hblank hfresh
  let S₁ : Stacks 117 A := { S with R := preparedHaloClassR A P q s t u band a b L S.R }
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) [(94 : Fin 117),115] (by decide) v₁ S₁
  have hsum : (([(94 : Fin 117),115]).map (fun k => (S₁.R k).length)).sum = w+V := by
    simp [S₁,preparedHaloClassR,haloClassControlsR,w,V]
  refine ⟨v₂,n₁+(2*(w+V)+5),hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp only [generateHaloClassControlsCost,w,V] at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h94 : k = 94
    · subst k; simp [hfresh 94 (by simp)]
    by_cases h115 : k = 115
    · subst k; simp [hfresh 115 (by simp)]
    simp [S₁,preparedHaloClassR,haloClassControlsR,Function.update_apply,h94,h115]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
