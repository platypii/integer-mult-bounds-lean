module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightPage

/-! Unary-header weight setup followed by the actual runtime row ordering. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def packedWeightSetup : Pr P₀ 117 Q A U := .seq weightSetup pairLayout

def packedWeightSetupCost (P s t u q L lo w : ℕ) : ℕ :=
  weightSetupCost P s t u q L lo w + pairLayoutCost L w

theorem packedWeightSetup_exec (P s t u q L lo w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hlo' : (S.R 111).length = lo) (hw : (S.R 94).length = w)
    (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 104, 105, 106, 108, 115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hlo : lo < s) (hL : L ≤ s) :
    ∃ v' m, v'.user = v.user ∧ m ≤ packedWeightSetupCost P s t u q L lo w ∧
      Exec body packedWeightSetup (mk v S) m
        (mk v' { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
          weightPage A w q P s t u lo L ++ S.R 110 else S.R k) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := weightSetup_exec (body := body) P s t u q L lo w v S
    hP' hs' ht' hu' hq hL' hlo' hw (hfresh 106 (by simp)) hblank
    (fun k hk => hfresh k (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> simp)) hP hs hst hu hlo hL
  let S₁ : Stacks 117 A := { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
    (List.range L).flatMap (weightPairSymbols A w q P s t u lo) ++ S.R 110 else S.R k) }
  let X := fun i => rationalWord q (ambientWeightSample P s t u lo i)
  let Y := fun i => reciprocalWeightWord q (ambientWeightSample P s t u lo i)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := pairLayout_exec (body := body) w L X Y v₁ S₁ (S.R 110)
    (by simpa [S₁] using hw) (by simpa [S₁] using hcount)
    (by rfl) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by unfold packedWeightSetupCost; omega,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk : k = 110
    · subst k; simp [S₁, weightPage, X, Y, List.append_assoc]
    simp [S₁, hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
