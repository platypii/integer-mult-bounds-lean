module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSizedGeneratorSetup

/-! # Construct the packed inverse setup from numerical metadata

The factor page is generated internally. No exponential samples, coefficient
vectors, matrix rows, inverse columns or reciprocal words are supplied.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def constructedFactorBank {A : ℕ} (S : Stacks 117 A) (P s t u band L W : ℕ) : Stacks 117 A :=
  { S with R := (fun k => if k.val < 63 then [] else if k = 109 then
    (cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ S.R 109) else S.R k) }

noncomputable def numericalGeneratorSetup (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq factorFactory (generatePackedGenerators hQ)

def numericalGeneratorSetupCost (P M L q V W : ℕ) : ℕ :=
  factorFactoryCost P L V W + generatorSetupCost P M L q W + packGeneratorsCost L W q

/-- Numerical binary table headers and ordinary unary dimensions generate the
complete packed setup. All factor data are constructed and all transient
coefficient/table/raw-column workspace is released. -/
theorem numericalGeneratorSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q M V W : ℕ} (hP : 13 ≤ P) (hqMax : q ≤ 2 * (M + 1))
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (hWdef : W = integerSetupWidth P q (M + 1) 0)
    (hV : u * t * (L + 1) ^ 2 * 2 ^ (13 * P + 8) < 2 ^ V) (hw : W ≤ V)
    (st : TblSt 48 A) (hP' : st.val 19 = P) (hs' : st.val 34 = s) (ht' : st.val 35 = t)
    (hu' : st.val 36 = u) (hb' : st.val 38 = band) (hL' : st.val 42 = L)
    (hstV : ∀ j, st.val j < 2 ^ V) (hacc : st.acc = [])
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = V) (hnl : nl.length = W)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hS : tblHolds coefficientReg S (tblRho V wl nl st))
    (hwidth : (S.R 94).length = W) (hrows : (S.R 102).length = L) (hrowCount : (S.R 103).length = L)
    (hprecision : (S.R 114).length = P) (hq : (S.R 112).length = q) (hcount : (S.R 101).length = M)
    (hleft : ∀ i : Fin 64, S.L (mul i) = []) (h63 : S.R 63 = []) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 100, 104, 105, 106, 107, 108, 113, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ numericalGeneratorSetupCost P M L q V W ∧
      Exec body (numericalGeneratorSetup hQ) (mk v S) m
        (mk v' (packedGeneratorBank (constructedFactorBank S P s t u band L W)
          P s t u band L q W (M + 1))) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := factorFactory_exec (body := body) st hP' hs' ht' hu' hb' hL'
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
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := generatePackedGenerators_exec (body := body) (band := band)
    hQ hA hW hP hs hst hu hL hqr henc hd hrun v₁ S₁ (S.R 109)
    (by simpa [S₁, constructedFactorBank] using hrows) (by simpa [S₁, constructedFactorBank] using hwidth)
    (by simpa [S₁, constructedFactorBank] using hrowCount) (by simpa [S₁, constructedFactorBank] using hprecision)
    (by simpa [S₁, constructedFactorBank] using hq)
    (by simpa [S₁, constructedFactorBank] using hfresh 108 (by simp))
    (by simpa [S₁, constructedFactorBank] using hcount)
    (by simpa [S₁, constructedFactorBank] using hfresh 100 (by simp))
    (by simp [S₁, constructedFactorBank]) hclean hblank₁ hfresh₁
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by unfold numericalGeneratorSetupCost; omega, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
