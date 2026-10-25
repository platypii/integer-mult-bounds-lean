module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWeightWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightFactory

/-! Weight setup from unary headers, with generated arithmetic width and paid
release of the generated width source. All borrowed headers survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def weightSetup : Pr P₀ 117 Q A U :=
  .seq generateWeightWidth (.seq weightFactory (uclear 115))

def weightSetupCost (P s t u q L lo w : ℕ) : ℕ :=
  weightWidthCost P q w t u + weightFactoryCost P s t u q L lo w +
    2 * weightWorkspaceWidth P q w t u + 2

theorem weightSetup_exec (P s t u q L lo w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hlo' : (S.R 111).length = lo) (hw : (S.R 94).length = w)
    (hz : S.R 106 = []) (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(104 : Fin 117), 115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hlo : lo < s) (hL : L ≤ s) :
    ∃ v' m, v'.user = v.user ∧ m ≤ weightSetupCost P s t u q L lo w ∧
      Exec body weightSetup (mk v S) m
        (mk v' { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
          ((List.range L).flatMap (weightPairSymbols A w q P s t u lo) ++ S.R 110) else S.R k) }) := by
  let V := weightWorkspaceWidth P q w t u
  have hlow (k : Fin 117) (hk : k.val < 63) : S.R k = [] := by
    obtain ⟨r, rfl⟩ := coefficientReg_covers k hk
    exact hblank r
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateWeightWidth_exec (body := body) P q w t u v S
    hP' hq hw ht' hu' (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hlow _ (by decide) | exact hfresh _ (by simp))
  let Sw : Stacks 117 A := { S with R := Function.update S.R 115 (List.replicate V tick) }
  have hblankw : ∀ r, Sw.R (coefficientReg r) = [] := by
    intro r
    have hn : coefficientReg r ≠ (115 : Fin 117) := by
      intro he
      have hr := coefficientReg_range r
      rw [he] at hr
      omega
    simpa [Sw, hn] using hblank r
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := weightFactory_exec (body := body) P s t u q L lo w v₁ Sw
    (by simpa [Sw] using hP') (by simpa [Sw] using hs') (by simpa [Sw] using ht')
    (by simpa [Sw] using hu') (by simpa [Sw] using hq) (by simpa [Sw] using hL')
    (by simpa [Sw] using hlo') (by simp [Sw, V]) (by simpa [Sw] using hw)
    (by simpa [Sw] using hz) hblankw hP hs hst hu hlo hL
  let B : Stacks 117 A := { Sw with R := (fun k => if k.val < 63 then [] else if k = 110 then
    ((List.range L).flatMap (weightPairSymbols A w q P s t u lo) ++ Sw.R 110) else Sw.R k) }
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 115 v₂ B
  have h115 : B.R 115 = List.replicate V tick := by simp [B, Sw]
  have he₃' : Exec body (uclear 115) (mk v₂ B) (2 * V + 2)
      (mk v₃ { B with R := Function.update B.R 115 [] }) := by
    simpa only [h115, List.length_replicate] using he₃
  refine ⟨v₃, m₁ + (m₂ + (2 * V + 2)), hu₃.trans (hu₂.trans hu₁),
    by unfold weightSetupCost; dsimp only [V] at *; omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃')).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases hk : k = 115
    · subst k
      simp [B, Sw, hfresh 115 (by simp)]
    simp [B, Sw, hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
