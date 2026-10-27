module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareHaloWeightFamily

/-! Construct the numerical interior family once in the complete inverse bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 263 Q A U}

def placedFamilySetup : Pr P₀ 263 Q A U :=
  embProg familyInverseReg Empty.elim (prepareHaloWeightFamily (P₀ := Empty))

theorem placedFamilySetup_exec (P N q l s t u band a b : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hst : s < t) (hu : 1 ≤ u) (hbandpos : 0 < band) (hband : band ≤ s)
    (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 263 Q A U) (S : Stacks 263 A) (raw : List (Fin (A+4)))
    (hready : LengthKeyReady P N q l s t u band 0 0 raw
      (embStk couplingSourceReg (embStk familyInverseLegacyReg S)))
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (hcache : ∀ i ∈ ([(256 : Fin 263),257,258,259,261,262] : List (Fin 263)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareHaloWeightFamilyCost A P N q l s t u band a b ∧
      Exec body placedFamilySetup (mk v S) n
        (mk v' {S with R := (Function.update S.R 260
          (weightKeyFamily (haloWeightKeyPages A (2*q+8) q P s t u band a b
            (haloLengthKeys s t band a b))++S.R 260))}) := by
  obtain ⟨vi,n,hui,hn,hei⟩ := prepareHaloWeightFamily_exec
    (body := fun p : Empty => nomatch p) P N q l s t u band a b hP hst hu hbandpos hband has hbs hA
    (embDn familyInverseReg v) (embStk familyInverseReg S) raw
    (by rw [familyInverse_legacy_view]; exact hready) ha hb h127 h138 (hcache 262 (by simp)) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact hcache 256 (by simp)
        | exact hcache 257 (by simp)
        | exact hcache 258 (by simp)
        | exact hcache 259 (by simp)
        | exact hcache 261 (by simp))
  obtain ⟨v',hv,hu',he⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    familyInverseReg_injective (fun p => nomatch p) hei v rfl S rfl
  refine ⟨v',n,hu'.trans hui,hn,he.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [embOvr_updR familyInverseReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
