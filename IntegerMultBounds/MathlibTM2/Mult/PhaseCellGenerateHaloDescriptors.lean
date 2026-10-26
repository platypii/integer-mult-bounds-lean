module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloDescriptorLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateOriginControls

/-! Generate clipped origin/length descriptors from ordinary unary parameters,
including both runtime widths, and release every temporary stack. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateHaloDescriptors : Pr P₀ 117 Q A U :=
  .seq generateRuntimeWidth (.seq generateWeightWidth (.seq preparedHaloDescriptors (clearWords [94, 115])))

def generateHaloDescriptorsCost (P q s t u band a b : ℕ) : ℕ :=
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  (4*q+5)+weightWidthCost P q w t u+preparedHaloDescriptorsCost s t band a b V+2*(w+V)+5

theorem generateHaloDescriptors_exec (P q s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPSrc : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b)
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 104, 106, 115], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateHaloDescriptorsCost P q s t u band a b ∧
      Exec body generateHaloDescriptors (mk v S) n
        (mk v' { S with R := (Function.update S.R 109
          (haloDescriptorPackets A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b ++ S.R 109)) }) := by
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
  obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hi₃, ho₃, hl₃, hr₃⟩ := preparedHaloDescriptors_exec (body := body)
    P q w s t u band a b hP hs hst hu hband has hbs hA v₂ S₂
    (by simpa [S₂, S₁] using hsSrc) (by simpa [S₂, S₁] using htSrc) (by simpa [S₂, S₁] using hbSrc)
    (by simpa [S₂, S₁] using haSrc) (by simpa [S₂, S₁] using hbEndSrc)
    (by simp [S₂, V]) (by simpa [S₂, S₁] using hfresh 106 (by simp)) (by
      intro k hk
      have h94 : k ≠ (94 : Fin 117) := by intro he; subst k; norm_num at hk
      have h115 : k ≠ (115 : Fin 117) := by intro he; subst k; norm_num at hk
      simpa [S₂, S₁, h94, h115] using hblank k hk)
  have hS₃ : S₃ = { S₂ with R := (Function.update S₂.R 109
      (haloDescriptorPackets A V s t band a b ++ S₂.R 109)) } := Stacks.ext hi₃ ho₃ hl₃ hr₃
  subst S₃
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update S₂.R 109
    (haloDescriptorPackets A V s t band a b ++ S₂.R 109)) }
  obtain ⟨v₄, hu₄, he₄⟩ := clearWords_exec (body := body) [(94 : Fin 117), 115] (by decide) v₃ S₃
  have hsum : (([(94 : Fin 117), 115]).map (fun k => (S₃.R k).length)).sum = w+V := by
    simp [S₃, S₂, S₁]
  refine ⟨v₄, (4*q+5)+(n₂+(n₃+(2*(w+V)+5))), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [hsum]; rfl) ?_⟩
  · dsimp only [generateHaloDescriptorsCost]
    dsimp only [w, V] at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h94 : k = 94
      · subst k; simp [hfresh 94 (by simp)]
      by_cases h115 : k = 115
      · subst k; simp [hfresh 115 (by simp)]
      simp [S₃, S₂, S₁, h94, h115, Function.update_apply, V, w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
