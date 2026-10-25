module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPageConstruct
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease

/-! # Construct the retained factor page from numerical table headers

Pi and each distance sample are generated, the samples are reused to assemble
all rows, and both table workspace and the temporary distance vector are released.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def factorFactory : Pr P₀ 117 Q A U :=
  .seq coefficientHost (.seq constructFactorPage (releaseFromDimensions 102 94 99 110 104 105 106))

def factorFactoryCost (P L V W : ℕ) : ℕ :=
  (L * (310 * P + 114) + (160 * P + 450)) * tblC V W +
    14 * (L * W) + 126 * V + 9 * L + 141 + constructFactorPageCost L W

/-- No coefficient samples, matrix rows or factor page are provided. Numerical
binary table headers are owned setup input; every other field is retained. -/
theorem factorFactory_exec {V W P s t u band L : ℕ} (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hs' : st.val 34 = s) (ht' : st.val 35 = t)
    (hu' : st.val 36 = u) (hb' : st.val 38 = band) (hL' : st.val 42 = L)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (hV : u * t * (L + 1) ^ 2 * 2 ^ (13 * P + 8) < 2 ^ V)
    (hstV : ∀ j, st.val j < 2 ^ V) (hacc : st.acc = [])
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = V) (hnl : nl.length = W) (hw : W ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hS : tblHolds coefficientReg S (tblRho V wl nl st))
    (hwidth : (S.R 94).length = W) (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 100, 104, 105, 106, 107, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ factorFactoryCost P L V W ∧
      Exec body factorFactory (mk v S) m
        (mk v' { S with R := (fun k => if k.val < 63 then [] else if k = 109 then
          (cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ S.R 109) else S.R k) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := coefficientHost_exec (body := body) st hP' hs' ht' hu' hb' hL'
    hP hs hst hu hV hstV hacc wl nl hwl hnl hw v S hS
  let S₁ : Stacks 117 A := { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
    (cstream A W (distanceFactorWords P s t u band L) ++ S.R 110) else S.R k) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := constructFactorPage_exec (body := body) P s t u band L W v₁ S₁ (S.R 110)
    (by simpa [S₁] using hwidth) (by simpa [S₁] using hrows) (by simpa [S₁] using hcount)
    (by simp [S₁]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [S₁] using hfresh _ (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update S₁.R 109
    (cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ S₁.R 109)) }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := releaseFromDimensions_exec (body := body)
    (show [(102 : Fin 117), 94, 99, 110, 104, 105, 106].Nodup by decide) v₂ S₂
    (cstream A W (distanceFactorWords P s t u band L)) (S.R 110)
    (by simp [S₂, S₁]) (by simp [S₂, S₁, hrows, hwidth])
    (by simpa [S₂, S₁] using hfresh 99 (by simp)) (by simpa [S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₂, S₁] using hfresh 105 (by simp)) (by simpa [S₂, S₁] using hfresh 106 (by simp))
  have hm₃' : m₃ ≤ 12 * (L * W) + 9 * L + 12 := by
    simpa [S₂, S₁, hrows] using hm₃
  refine ⟨v₃, m₁ + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁), ?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · unfold factorFactoryCost
    nlinarith only [hm₁, hm₂, hm₃']
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hc : k.val < 63
    · have h110 : k ≠ 110 := by intro he; have hv := congrArg Fin.val he; omega
      have h109 : k ≠ 109 := by intro he; have hv := congrArg Fin.val he; omega
      simp [S₂, S₁, hc, h110, h109]
    by_cases h110 : k = 110
    · subst k; simp
    by_cases h109 : k = 109
    · subst k; simp [S₂, S₁]
    simp [S₂, S₁, hc, h110, h109]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
