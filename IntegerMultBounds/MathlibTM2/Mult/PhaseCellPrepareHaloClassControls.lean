module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateOriginControls

/-! Generate the origins and owned count for one positive halo length class,
retaining both runtime widths and releasing arithmetic workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareHaloClassControls : Pr P₀ 117 Q A U :=
  .seq generateRuntimeWidth (.seq generateWeightWidth preparedHaloClass)

def prepareHaloClassControlsCost (P q s t u band a b L : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  (4*q+5)+weightWidthCost P q w t u+preparedHaloClassCost s t band a b L V

def haloClassControlsR (A V s t band a b L : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  Function.update (Function.update R 109 (haloOriginPackets A V s t band a b L++R 109))
    116 (List.replicate (haloLengthGroup s t band a b L).length tick)

def preparedHaloClassR (A P q s t u band a b L : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  haloClassControlsR A V s t band a b L
    (Function.update (Function.update R 94 (List.replicate w tick)) 115 (List.replicate V tick))

theorem prepareHaloClassControls_exec (P q s t u band a b L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115,116], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareHaloClassControlsCost P q s t u band a b L ∧
      Exec body prepareHaloClassControls (mk v S) n
        (mk v' { S with R := preparedHaloClassR A P q s t u band a b L S.R }) := by
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁, hu₁, he₁⟩ := generateRuntimeWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 104 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate w tick) }
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := generateWeightWidth_exec (body := body) P q w t u v₁ S₁
    (by simpa [S₁] using hPSrc) (by simpa [S₁] using hq) (by simp [S₁])
    (by simpa [S₁] using htSrc) (by simpa [S₁] using huSrc) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [S₁, Function.update_apply]
      all_goals norm_num
      all_goals first | exact hblank _ (by decide) | exact hfresh _ (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 115 (List.replicate V tick) }
  obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hi₃, ho₃, hl₃, hr₃⟩ := preparedHaloClass_exec (body := body)
    P q w s t u band a b L hP hs hst hu hband has hbs hL hLs hA v₂ S₂
    (by simpa [S₂, S₁] using hsSrc) (by simpa [S₂, S₁] using htSrc) (by simpa [S₂, S₁] using hbSrc)
    (by simpa [S₂, S₁] using haSrc) (by simpa [S₂, S₁] using hbEndSrc) (by simpa [S₂, S₁] using hLSrc)
    (by simp [S₂, V]) (by simpa [S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₂, S₁] using hfresh 106 (by simp)) (by simpa [S₂, S₁] using hfresh 116 (by simp)) (by
      intro k hk
      have h94 : k ≠ (94 : Fin 117) := by intro he; subst k; norm_num at hk
      have h115 : k ≠ (115 : Fin 117) := by intro he; subst k; norm_num at hk
      simpa [S₂, S₁, h94, h115] using hblank k hk)
  have hS₃ : S₃ = { S₂ with R := (Function.update (Function.update S₂.R 109
      (haloOriginPackets A V s t band a b L ++ S₂.R 109)) 116 (List.replicate (haloLengthGroup s t band a b L).length tick)) } := Stacks.ext hi₃ ho₃ hl₃ hr₃
  subst S₃
  refine ⟨v₃,(4*q+5)+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · dsimp only [prepareHaloClassControlsCost]
    dsimp only [w,V] at *
    omega
  · rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
