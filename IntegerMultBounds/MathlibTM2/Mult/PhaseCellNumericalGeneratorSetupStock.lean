module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNumericalGeneratorSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorFactoryStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedGeneratorSetupStock

/-! Numerical setup constructs its factor data and packed inverse using shared reserves. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def numericalGeneratorSetupWorkspace (C L q V W M : ℕ) : ℕ :=
  factorFactoryWorkspace L V W+packedGeneratorSetupWorkspace C L q W M

theorem numericalGeneratorSetup_trace_within (hQ : SS.states ≤ Q) (C L q V W M m₁ m₂ : ℕ)
    (v₀ v₁ v₂ : HS 117 Q A U) (S₀ S₁ S₂ : Stacks 117 A)
    (h₁ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+factorFactoryWorkspace L V W)
      depth factorFactory (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+packedGeneratorSetupWorkspace C L q W M)
      depth (generatePackedGenerators hQ) (mk v₁ S₁) m₂ (mk v₂ S₂)) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+numericalGeneratorSetupWorkspace C L q V W M)
      depth (numericalGeneratorSetup hQ) (mk v₀ S₀) (m₁+m₂) (mk v₂ S₂) := by
  exact (mn_seq_within_add (h₁ depth) (h₂ depth)).mono (by
    intro d z hz; simpa only [numericalGeneratorSetupWorkspace] using hz)

theorem numericalGeneratorSetup_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q M V W : ℕ} (hP : 13 ≤ P) (hqMax : q ≤ 2 * (M + 1))
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (hWdef : W = integerSetupWidth P q (M + 1) 0)
    (hV : u * t * (L + 1) ^ 2 * 2 ^ (13 * P + 8) < 2 ^ V) (hw : W ≤ V)
    (st : TblSt 48 A) (hP' : st.val 19 = P) (hs' : st.val 34 = s) (ht' : st.val 35 = t)
    (hu' : st.val 36 = u) (hb' : st.val 38 = band) (hL' : st.val 42 = L)
    (hstV : ∀ j, st.val j < 2 ^ V) (hacc : st.acc = [])
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = V) (hnl : nl.length = W)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hS : tblHolds coefficientReg S (tblRho V wl nl st))
    (hwidth : (S.R 94).length = W) (hrows : (S.R 102).length = L) (hrowCount : (S.R 103).length = L)
    (hprecision : (S.R 114).length = P) (hq : (S.R 112).length = q) (hcount : (S.R 101).length = M)
    (hleft : ∀ i : Fin 64, S.L (mul i) = []) (h63 : S.R 63 = []) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 100, 104, 105, 106, 107, 108, 113, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ numericalGeneratorSetupCost P M L q V W ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+numericalGeneratorSetupWorkspace C L q V W M)
        depth (numericalGeneratorSetup hQ) (mk v S) m
        (mk v' (packedGeneratorBank (constructedFactorBank S P s t u band L W)
          P s t u band L q W (M + 1)))) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := factorFactory_exec_within (body := body) st hP' hs' ht' hu' hb' hL'
    hP hs hst hu hV hstV hacc wl nl hwl hnl hw v S hS hwidth hrows hrowCount
    (fun k hk => hfresh k ((by decide : [(97 : Fin 117), 98, 99, 100, 104, 105, 106, 107, 108].Sublist
      [96, 97, 98, 99, 100, 104, 105, 106, 107, 108, 113, 115, 116]).subset hk))
  let S₁ := constructedFactorBank S P s t u band L W
  have hclean : CClean mul S₁ := by
    intro i
    refine ⟨hleft i, ?_⟩
    have hi := i.isLt
    by_cases hk : i.val < 63
    · simp [S₁, constructedFactorBank, mul, hk]
    have hval : i.val = 63 := by omega
    simpa [S₁, constructedFactorBank, mul, hval] using h63
  have hblank₁ : ∀ r, S₁.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have hlo : ¬ (cr r).val < 63 := by omega
    have h109 : cr r ≠ (109 : Fin 117) := by intro he; have hv := congrArg Fin.val he; omega
    simpa [S₁, constructedFactorBank, hlo, h109] using hblank r
  have hfresh₁ : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 113, 115, 116], S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [S₁, constructedFactorBank] using hfresh _ (by simp)
  have hreq : P * (M + 2) + 3 ≤ W ∧ q ≤ P * (M + 1) + 1 ∧
      P * (M + 1) + 1 - q + (2 * q + 8) ≤ W ∧ q + P * (M + 1) < W ∧ 2 * q + 8 ≤ W := by
    simpa only [hWdef] using integerSetupWidth_generator hP hqMax
  obtain ⟨hW, hqr, henc, hd, hrun⟩ := hreq
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := generatePackedGenerators_exec_within (body := body) (band := band)
    hQ hA hW hP hs hst hu hL hqr henc hd hrun C hpush v₁ S₁ (S.R 109)
    (by simpa [S₁, constructedFactorBank] using hrows) (by simpa [S₁, constructedFactorBank] using hwidth)
    (by simpa [S₁, constructedFactorBank] using hrowCount) (by simpa [S₁, constructedFactorBank] using hprecision)
    (by simpa [S₁, constructedFactorBank] using hq)
    (by simpa [S₁, constructedFactorBank] using hfresh 108 (by simp))
    (by simpa [S₁, constructedFactorBank] using hcount)
    (by simpa [S₁, constructedFactorBank] using hfresh 100 (by simp))
    (by simp [S₁, constructedFactorBank]) hclean hblank₁ hfresh₁
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by unfold numericalGeneratorSetupCost; omega, (fun depth => numericalGeneratorSetup_trace_within hQ C L q V W M m₁ m₂
    v v₁ v₂ S S₁ _ he₁ he₂ depth)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
