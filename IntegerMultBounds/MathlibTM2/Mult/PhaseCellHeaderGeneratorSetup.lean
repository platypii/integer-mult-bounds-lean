module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCoefficientHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNumericalGeneratorRelease

/-! # Generate the inverse setup from ordinary unary headers

Geometry headers 97--100 are owned setup input. All table words, both widths,
coefficients, factors, inverse generators, reciprocal and packed page are generated.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def unaryGeometryBase {A : ℕ} (S : Stacks 117 A) (P q M : ℕ) : Stacks 117 A :=
  let S₁ := setupWidthBank S P q M
  { S₁ with R := fun k => if k ∈ geometryHeaderPorts then [] else S₁.R k }

noncomputable def headerGeneratorSetup (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq generateSetupWidth (.seq generateCoefficientWidth (.seq prepareCoefficientHeaders (numericalGeneratorSetup hQ)))

def headerGeneratorSetupCost (P M q s t u band L : ℕ) : ℕ :=
  let W := integerSetupWidth P q (M + 1) 0
  let V := coefficientWorkspaceWidth P W t u band L
  (4 * (P * M) + 13 * P + 4 * q + 13) + coefficientWidthCost P W t u band L +
    prepareCoefficientHeadersCost P s t u band L V W + numericalGeneratorSetupCost P M L q V W

/-- The caller supplies ordinary header symbols and clean workspace, not binary
table words, word-width counters, numerical samples or precomputed setup pages. -/
theorem headerGeneratorSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q M : ℕ} (hP : 13 ≤ P) (hqMax : q ≤ 2 * (M + 1))
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hrowCount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hcount : (S.R 101).length = M)
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 96, 104, 105, 106, 107, 108, 113, 115, 116], S.R k = []) :
    let W := integerSetupWidth P q (M + 1) 0
    ∃ v' m, v'.user = v.user ∧ m ≤ headerGeneratorSetupCost P M q s t u band L ∧
      Exec body (headerGeneratorSetup hQ) (mk v S) m
        (mk v' (packedGeneratorBank (constructedFactorBank (unaryGeometryBase S P q M) P s t u band L W)
          P s t u band L q W (M + 1))) := by
  let W := integerSetupWidth P q (M + 1) 0
  let V := coefficientWorkspaceWidth P W t u band L
  have hcore (k : Fin 117) (hk : k.val < 64) : S.R k = [] := by
    have hh := (hclean ⟨k.val, hk⟩).2
    simpa [mul] using hh
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateSetupWidth_exec (body := body) P M q v S hprecision hcount hq
    (fun k hk => hfresh k ((by decide : [(94 : Fin 117), 104, 105].Sublist
      [94, 96, 104, 105, 106, 107, 108, 113, 115, 116]).subset hk))
  let S₁ := setupWidthBank S P q M
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := generateCoefficientWidth_exec (body := body) P W t u band L v₁ S₁
    (by simpa [S₁, setupWidthBank] using hprecision) (by simp [S₁, setupWidthBank, W])
    (by simpa [S₁, setupWidthBank] using htR) (by simpa [S₁, setupWidthBank] using huR)
    (by simpa [S₁, setupWidthBank] using hband) (by simpa [S₁, setupWidthBank] using hrows) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | simpa [S₁, setupWidthBank] using hcore _ (by decide)
        | simpa [S₁, setupWidthBank] using hfresh _ (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 115 (List.replicate V tick) }
  have hoff₂ (k : Fin 117) (h94 : k ≠ 94) (h115 : k ≠ 115) : S₂.R k = S.R k := by
    simp [S₂, S₁, setupWidthBank, h94, h115]
  have htableBlank : ∀ r, S₂.R (coefficientReg r) = [] := by
    intro r
    have hr := coefficientReg_range r
    have h94 : coefficientReg r ≠ (94 : Fin 117) := by intro he; have hv := congrArg Fin.val he; omega
    have h115 : coefficientReg r ≠ (115 : Fin 117) := by intro he; have hv := congrArg Fin.val he; omega
    rw [hoff₂ _ h94 h115]
    exact hcore _ (by omega)
  obtain ⟨v₃, S₃, m₃, hu₃, hm₃, he₃, hholds, hin, hout, hleft, hframe⟩ := prepareCoefficientHeaders_exec (body := body)
    P s t u band L V W v₂ S₂
    (by rw [hoff₂ 114 (by decide) (by decide)]; exact hprecision)
    (by rw [hoff₂ 97 (by decide) (by decide)]; exact hsR)
    (by rw [hoff₂ 98 (by decide) (by decide)]; exact htR)
    (by rw [hoff₂ 99 (by decide) (by decide)]; exact huR)
    (by rw [hoff₂ 100 (by decide) (by decide)]; exact hband)
    (by rw [hoff₂ 102 (by decide) (by decide)]; exact hrows)
    (by simp [S₂]) (by simp [S₂, S₁, setupWidthBank, W])
    (by rw [hoff₂ 106 (by decide) (by decide)]; exact hfresh 106 (by simp)) htableBlank
  have hbase (k : Fin 117) (hk : 63 ≤ k.val) : S₃.R k = (unaryGeometryBase S P q M).R k := by
    rw [hframe k hk]
    by_cases hg : k ∈ geometryHeaderPorts
    · simp [unaryGeometryBase, hg]
    have h115 : k ≠ 115 := by intro he; subst k; simp [geometryHeaderPorts] at hg
    simp [unaryGeometryBase, S₂, S₁, hg, h115]
  have hhigh (k : Fin 117) (hk : 63 ≤ k.val) (hg : k ∉ geometryHeaderPorts) (h94 : k ≠ 94) : S₃.R k = S.R k := by
    rw [hbase k hk]
    simp [unaryGeometryBase, setupWidthBank, hg, h94]
  have hblank₃ : ∀ r, S₃.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have hg : cr r ∉ geometryHeaderPorts := by
      intro hk
      simp only [geometryHeaderPorts, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with he | he | he | he | he <;> have hv := congrArg Fin.val he <;> omega
    have h94 : cr r ≠ (94 : Fin 117) := by intro he; exact hr.2.2.2 (congrArg Fin.val he)
    rw [hhigh _ (by omega) hg h94]
    exact hblank r
  have hleft₃ : ∀ i : Fin 64, S₃.L (mul i) = [] := by
    intro i
    rw [hleft]
    exact (hclean i).1
  have hfresh₃ : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 100, 104, 105, 106, 107, 108, 113, 115, 116], S₃.R k = [] := by
    intro k hk
    have hk63 : 63 ≤ k.val := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hbase k hk63]
    by_cases hg : k ∈ geometryHeaderPorts
    · simp [unaryGeometryBase, hg]
    have hi : k ∈ [(94 : Fin 117), 96, 104, 105, 106, 107, 108, 113, 115, 116] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [geometryHeaderPorts] at hg ⊢
    have h94 : k ≠ 94 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [unaryGeometryBase, setupWidthBank, hg, h94] using hfresh k hi
  obtain ⟨hWV, _, _, _, _, _, _, harg⟩ := coefficientWorkspaceWidth_bound P W s t u band L hst
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := numericalGeneratorSetup_exec (body := body) (band := band)
    hQ hA hP hqMax hs hst hu hL rfl harg hWV (coefficientHeaderState P s t u band L)
    (by simp [coefficientHeaderState]) (by simp [coefficientHeaderState]) (by simp [coefficientHeaderState])
    (by simp [coefficientHeaderState]) (by simp [coefficientHeaderState]) (by simp [coefficientHeaderState])
    (coefficientHeaderState_fits P W s t u band L hst) rfl
    (List.replicate V tick) (List.replicate W tick) (by simp only [List.length_replicate]; rfl)
    (by simp only [List.length_replicate]; rfl) v₃ S₃ hholds
    (by rw [hbase 94 (by decide)]; simp [unaryGeometryBase, geometryHeaderPorts, setupWidthBank, W])
    (by rw [hhigh 102 (by decide) (by decide) (by decide)]; exact hrows)
    (by rw [hhigh 103 (by decide) (by decide) (by decide)]; exact hrowCount)
    (by rw [hhigh 114 (by decide) (by decide) (by decide)]; exact hprecision)
    (by rw [hhigh 112 (by decide) (by decide) (by decide)]; exact hq)
    (by rw [hhigh 101 (by decide) (by decide) (by decide)]; exact hcount) hleft₃
    (by rw [hhigh 63 (by decide) (by decide) (by decide)]; exact hcore 63 (by decide)) hblank₃ hfresh₃
  have hfactorFrame : constructedFactorBank S₃ P s t u band L W =
      constructedFactorBank (unaryGeometryBase S P q M) P s t u band L W := by
    ext1
    · exact hin
    · exact hout
    · exact hleft
    funext k
    by_cases hk : k.val < 63
    · simp [constructedFactorBank, hk]
    by_cases h109 : k = 109
    · subst k; simp [constructedFactorBank, hbase 109 (by decide)]
    simp [constructedFactorBank, hk, h109, hbase k (by omega)]
  rw [hfactorFrame] at he₄
  refine ⟨v₄, m₁ + (m₂ + (m₃ + m₄)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))⟩
  simpa only [headerGeneratorSetupCost, W, V, Nat.add_assoc] using
    Nat.add_le_add hm₁ (Nat.add_le_add hm₂ (Nat.add_le_add hm₃ hm₄))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
