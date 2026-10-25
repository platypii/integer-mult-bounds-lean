module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNumericalWeightHost

/-! Generate the complete interleaved weight page from retained unary headers.
No binary table state, pi, scale, exponential sample or weight is provided. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def weightFactory : Pr P₀ 117 Q A U :=
  .seq initializeCoefficientBank (.seq loadWeightHeaders numericalWeightHost)

def weightFactoryCost (P s t u q L lo w : ℕ) : ℕ :=
  let V := weightWorkspaceWidth P q w t u
  (292 * V + 4 * w + 393) + weightHeadersCost P s t u q L lo V +
    (numericalWeightAtoms P q L * tblC V w + 4 * L * w + 126 * V + 129)

theorem weightFactory_exec (P s t u q L lo w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hlo' : (S.R 111).length = lo)
    (hwidth : (S.R 115).length = weightWorkspaceWidth P q w t u) (hw : (S.R 94).length = w)
    (hz : S.R 106 = []) (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hlo : lo < s) (hL : L ≤ s) :
    ∃ v' m, v'.user = v.user ∧ m ≤ weightFactoryCost P s t u q L lo w ∧
      Exec body weightFactory (mk v S) m
        (mk v' { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
          ((List.range L).flatMap (weightPairSymbols A w q P s t u lo) ++ S.R 110) else S.R k) }) := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁, hu₁, he₁, hholds₁⟩ := initializeCoefficientBank_exec (body := body) V w v S
    hwidth hw hz hblank
  let S₁ : Stacks 117 A := { S with R := chirpBankLoadR coefficientReg (fun _ => 106) V w (fun _ => 0) S.R }
  have hoff₁ (k : Fin 117) (hk : 63 ≤ k.val) : S₁.R k = S.R k := by
    apply chirpBankLoad_off
    intro r he
    have hr := coefficientReg_range r
    rw [he] at hk
    omega
  obtain ⟨v₂, S₂, m₂, hu₂, hm₂, he₂, hholds₂, hf₂⟩ := loadWeightHeaders_exec (body := body)
    P s t u q L lo V w v₁ S₁
    (by rw [hoff₁ 114 (by decide)]; exact hP') (by rw [hoff₁ 97 (by decide)]; exact hs')
    (by rw [hoff₁ 98 (by decide)]; exact ht') (by rw [hoff₁ 99 (by decide)]; exact hu')
    (by rw [hoff₁ 112 (by decide)]; exact hq) (by rw [hoff₁ 111 (by decide)]; exact hlo')
    (by rw [hoff₁ 102 (by decide)]; exact hL') hholds₁
  have hoff₂ (k : Fin 117) (hk : 63 ≤ k.val) : S₂.R k = S.R k := by
    rw [hf₂.2.2.2 k (fun r he => by have hr := coefficientReg_range r; rw [he] at hr; omega)]
    exact hoff₁ k hk
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := numericalWeightHost_exec (body := body)
    (weightHeaderState (A := A) P s t u q L lo)
    (by simp [weightHeaderState]) (by simp [weightHeaderState]) (by simp [weightHeaderState])
    (by simp [weightHeaderState]) (by simp [weightHeaderState]) (by simp [weightHeaderState])
    (by simp [weightHeaderState]) hP hs hst hu hlo hL (weightHeaderState_fits hP hs hst hu hlo hL)
    rfl (List.replicate V tick) (List.replicate w tick) (by simp [V]) (by simp) v₂ S₂ hholds₂
  refine ⟨v₃, (292 * V + 4 * w + 393) + (m₂ + m₃), hu₃.trans (hu₂.trans hu₁), ?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · unfold weightFactoryCost
    dsimp only [V] at hm₂ ⊢
    omega
  · congr 1
    ext1
    · exact hf₂.1
    · exact hf₂.2.1
    · exact hf₂.2.2.1
    · funext k
      by_cases hk : k.val < 63
      · simp [hk]
      by_cases ho : k = 110
      · subst k; simp [hoff₂ 110 (by decide)]
      simp [hk, ho, hoff₂ k (by omega)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
