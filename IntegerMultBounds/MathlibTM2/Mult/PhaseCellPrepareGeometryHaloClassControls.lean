module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareHaloClassControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloGeometryWidth

/-! Generate the origins and owned count for one positive halo length class,
generating a separate geometry width and releasing arithmetic workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareGeometryHaloClassControls : Pr P₀ 117 Q A U :=
  .seq generateRuntimeWidth (.seq generateHaloGeometryWidth preparedHaloClass)

def prepareGeometryHaloClassControlsCost (q s t band a b L : ℕ) : ℕ :=
  let w := 2*q+8
  let V := haloGeometryWidth t w
  (4*q+5)+generateHaloGeometryWidthCost t w+preparedHaloClassCost s t band a b L V

def preparedGeometryHaloClassR (A q s t band a b L : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  let w := 2*q+8
  let V := haloGeometryWidth t w
  haloClassControlsR A V s t band a b L
    (Function.update (Function.update R 94 (List.replicate w tick)) 115 (List.replicate V tick))

theorem prepareGeometryHaloClassControls_exec (q s t band a b L : ℕ)
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115,116], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareGeometryHaloClassControlsCost q s t band a b L ∧
      Exec body prepareGeometryHaloClassControls (mk v S) n
        (mk v' { S with R := preparedGeometryHaloClassR A q s t band a b L S.R }) := by
  let w := 2*q+8
  let V := haloGeometryWidth t w
  obtain ⟨v₁, hu₁, he₁⟩ := generateRuntimeWidth_exec (body := body) q v S hq
    (hfresh 94 (by simp)) (hfresh 104 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 94 (List.replicate w tick) }
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := generateHaloGeometryWidth_exec (body := body) t w v₁ S₁
    (by simpa [S₁] using htSrc) (by simp [S₁])
    (by simpa [S₁] using hfresh 115 (by simp)) (by
      intro k hk
      have hne : k ≠ (94 : Fin 117) := by intro he; subst k; norm_num at hk
      simpa [S₁,hne] using hblank k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 115 (List.replicate V tick) }
  have hwide : 8*(t+1)^2+2*band+8 < 2^V := by
    have h := (haloControlWidth_bounds s t band w).1
    exact h.trans_le (Nat.pow_le_pow_right (by decide) (haloControlWidth_le_geometryWidth hst.le (hband.trans hst.le)))
  obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hi₃, ho₃, hl₃, hr₃⟩ := preparedHaloClass_width_exec (body := body)
    V s t band a b L hwide hs hst hband has hbs hL hLs hA v₂ S₂
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
  · dsimp only [prepareGeometryHaloClassControlsCost]
    dsimp only [w,V] at *
    omega
  · rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
