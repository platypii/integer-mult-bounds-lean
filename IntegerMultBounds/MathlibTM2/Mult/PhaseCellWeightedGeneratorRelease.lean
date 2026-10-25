module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightedGeneratorSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderGeneratorRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseWeightPage

/-! Release the complete generated numerical setup. Only the explicitly owned
geometry and lower-endpoint headers are consumed; borrowed state returns exactly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def weightedGeneratorRelease : Pr P₀ 117 Q A U := .seq headerGeneratorRelease releaseWeightPage

def consumedWeightedGeometryBank {A : ℕ} (S : Stacks 117 A) : Stacks 117 A :=
  let B := consumedGeometryBank S
  { B with R := Function.update B.R 111 [] }

def weightedGeneratorReleaseCost (P L q M : ℕ) : ℕ :=
  let W := integerSetupWidth P q (M + 1) 0
  releasePackedSetupCost L q W (M + 1) + releaseFactorPageCost L W + 2 * W + 2 +
    releaseWeightPageCost L q

theorem weightedGeneratorRelease_exec (P s t u band L q M lo : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L) (hq : (S.R 112).length = q)
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 96, 104, 105, 106, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ weightedGeneratorReleaseCost P L q M ∧
      Exec body weightedGeneratorRelease (mk v (weightedGeneratorBank S P s t u band L q M lo)) m
        (mk v' (consumedWeightedGeometryBank S)) := by
  let B := runtimeWeightBank S P s t u q L lo
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := headerGeneratorRelease_exec (body := body)
    P s t u band L q M v B
    (by simpa [B, runtimeWeightBank] using hrows) (by simpa [B, runtimeWeightBank] using hcount)
    (by simpa [B, runtimeWeightBank] using hq)
    (runtimeWeightBank_clean S P s t u q L lo hclean) (runtimeWeightBank_blank S P s t u q L lo hblank) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simpa [B, runtimeWeightBank] using hfresh _ (by simp))
  let C := consumedGeometryBank B
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseWeightPage_exec (body := body) L q
    (weightPage A (2 * q + 8) q P s t u lo L) (S.R 110) v₁ C
    (by simpa [C, B, consumedGeometryBank, geometryHeaderPorts, runtimeWeightBank] using hrows)
    (by simpa [C, B, consumedGeometryBank, geometryHeaderPorts, runtimeWeightBank] using hq)
    (weightPage_length _ _ _ _ _ _ _ _ _) (by simp [C, B, consumedGeometryBank, geometryHeaderPorts, runtimeWeightBank]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [C, B, consumedGeometryBank, geometryHeaderPorts, runtimeWeightBank] using hfresh 94 (by simp)
      · simpa [C, B, consumedGeometryBank, geometryHeaderPorts, runtimeWeightBank] using hfresh 96 (by simp)
      · simp [C, consumedGeometryBank, geometryHeaderPorts]
      · simpa [C, B, consumedGeometryBank, geometryHeaderPorts, runtimeWeightBank] using hfresh 104 (by simp)
      · simpa [C, B, consumedGeometryBank, geometryHeaderPorts, runtimeWeightBank] using hfresh 105 (by simp)
      · simpa [C, B, consumedGeometryBank, geometryHeaderPorts, runtimeWeightBank] using hfresh 106 (by simp))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by dsimp only [weightedGeneratorReleaseCost]; omega,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk110 : k = 110
    · subst k; simp [consumedWeightedGeometryBank, consumedGeometryBank, geometryHeaderPorts]
    by_cases hk111 : k = 111
    · subst k; simp [C, B, consumedWeightedGeometryBank, consumedGeometryBank, geometryHeaderPorts, runtimeWeightBank]
    by_cases hklo : k.val < 63
    · have hcore : S.R k = [] := by
        have hh := (hclean ⟨k.val, by omega⟩).2
        simpa [mul] using hh
      have hgeo : k ∉ geometryHeaderPorts := by
        intro hg
        simp only [geometryHeaderPorts, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with he | he | he | he | he <;> have hv := congrArg Fin.val he <;> omega
      simp [C, B, consumedWeightedGeometryBank, consumedGeometryBank, runtimeWeightBank,
        hk110, hk111, hklo, hgeo, hcore]
    simp [C, B, consumedWeightedGeometryBank, consumedGeometryBank, runtimeWeightBank,
      hk110, hk111, hklo]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
