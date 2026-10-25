module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRuntimeWeightSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderGeneratorSetup

/-! Compose unary weight construction with inverse-generator construction in the
same 117-tape bank. The owned lower endpoint is consumed before cell execution. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def weightedGeneratorSetup (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq runtimeWeightSetup (headerGeneratorSetup hQ)

def weightedGeneratorSetupCost (P M q s t u band L lo : ℕ) : ℕ :=
  runtimeWeightSetupCost P s t u q L lo + headerGeneratorSetupCost P M q s t u band L

def weightedGeneratorBank {A : ℕ} (S : Stacks 117 A) (P s t u band L q M lo : ℕ) : Stacks 117 A :=
  let W := integerSetupWidth P q (M + 1) 0
  packedGeneratorBank (constructedFactorBank
    (unaryGeometryBase (runtimeWeightBank S P s t u q L lo) P q M) P s t u band L W)
    P s t u band L q W (M + 1)

theorem runtimeWeightBank_clean {A : ℕ} (S : Stacks 117 A) (P s t u q L lo : ℕ)
    (hclean : CClean mul S) : CClean mul (runtimeWeightBank S P s t u q L lo) := by
  let B := runtimeWeightBank S P s t u q L lo
  change CClean mul B
  intro i
  refine ⟨(hclean i).1, ?_⟩
  have h110 : mul i ≠ (110 : Fin 117) := by
    intro he; have hv := congrArg (fun x : Fin 117 => x.val) he
    have hi := i.isLt; simp only [mul] at hv; omega
  have h111 : mul i ≠ (111 : Fin 117) := by
    intro he; have hv := congrArg (fun x : Fin 117 => x.val) he
    have hi := i.isLt; simp only [mul] at hv; omega
  simp [B, runtimeWeightBank, h110, h111, (hclean i).2]

theorem runtimeWeightBank_blank {A : ℕ} (S : Stacks 117 A) (P s t u q L lo : ℕ)
    (hblank : ∀ r, S.R (cr r) = []) : ∀ r, (runtimeWeightBank S P s t u q L lo).R (cr r) = [] := by
  let B := runtimeWeightBank S P s t u q L lo
  change ∀ r, B.R (cr r) = []
  intro r
  obtain ⟨hlo, hhi, _⟩ := cr_range r
  have h110 : cr r ≠ (110 : Fin 117) := by intro he; rw [he] at hhi; norm_num at hhi
  have h111 : cr r ≠ (111 : Fin 117) := by intro he; rw [he] at hhi; norm_num at hhi
  simp [B, runtimeWeightBank, show ¬ (cr r).val < 63 by omega, h110, h111, hblank r]

theorem weightedGeneratorSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q M lo : ℕ} (hP : 13 ≤ P) (hqMax : q ≤ 2 * (M + 1))
    (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hL : 0 < L) (hLs : L ≤ s) (hlo : lo < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hprecision : (S.R 114).length = P) (hsR : (S.R 97).length = s) (htR : (S.R 98).length = t)
    (huR : (S.R 99).length = u) (hband : (S.R 100).length = band)
    (hrows : (S.R 102).length = L) (hrowCount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hcount : (S.R 101).length = M) (hloR : (S.R 111).length = lo)
    (hclean : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 96, 104, 105, 106, 107, 108, 113, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ weightedGeneratorSetupCost P M q s t u band L lo ∧
      Exec body (weightedGeneratorSetup hQ) (mk v S) m
        (mk v' (weightedGeneratorBank S P s t u band L q M lo)) := by
  have htable : ∀ r, S.R (coefficientReg r) = [] := by
    intro r
    have hr := coefficientReg_range r
    have hh := (hclean ⟨(coefficientReg r).val, by omega⟩).2
    simpa [mul] using hh
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := runtimeWeightSetup_exec (body := body) P s t u q L lo v S
    hprecision hsR htR huR hq hrows hrowCount hloR htable (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
    hP hs hst hu hlo hLs
  let B := runtimeWeightBank S P s t u q L lo
  have hcleanB := runtimeWeightBank_clean S P s t u q L lo hclean
  have hblankB := runtimeWeightBank_blank S P s t u q L lo hblank
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := headerGeneratorSetup_exec (body := body) hQ hA hP hqMax
    hs hst.le hu hL v₁ B
    (by simpa [B, runtimeWeightBank] using hprecision) (by simpa [B, runtimeWeightBank] using hsR)
    (by simpa [B, runtimeWeightBank] using htR) (by simpa [B, runtimeWeightBank] using huR)
    (by simpa [B, runtimeWeightBank] using hband) (by simpa [B, runtimeWeightBank] using hrows)
    (by simpa [B, runtimeWeightBank] using hrowCount) (by simpa [B, runtimeWeightBank] using hq)
    (by simpa [B, runtimeWeightBank] using hcount) hcleanB hblankB (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [B, runtimeWeightBank] using hfresh _ (by simp))
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by unfold weightedGeneratorSetupCost; omega, Exec.seq he₁ he₂⟩

/-- The retained page contains both generators, their reciprocal, output weights
and reciprocal input weights, in the exact generated word orders. -/
theorem weightedGeneratorBank_page {A : ℕ} (S : Stacks 117 A) (P s t u band L q M lo : ℕ) :
    (weightedGeneratorBank S P s t u band L q M lo).R 110 =
      generatorPage A P s t u band L q (M + 1) ++
        (weightPage A (2 * q + 8) q P s t u lo L ++ S.R 110) := by
  simp [weightedGeneratorBank, packedGeneratorBank, constructedFactorBank,
    unaryGeometryBase, setupWidthBank, geometryHeaderPorts, runtimeWeightBank]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
