module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyGeneratedBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFamilyInteriorForCoupling

/-! Supply the generated RHS frame from the invariant already retained by the
family residual caller. Only the coordinate bank's occupied ports are excluded. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem familyCouplingSourceReg_identity (i : Fin 144)
    (h109 : i ≠ 109) (h115 : i ≠ 115) (h116 : i ≠ 116) :
    familyCouplingSourceReg i = familyGeneratedRhsReg (boundaryRhsHeaderReg i) := by
  apply Fin.ext
  change (boundaryArithmeticReg (componentReg i)).val = i.val
  simp only [ne_eq,Fin.ext_iff] at h109 h115 h116
  norm_num at h109 h115 h116
  simp [boundaryArithmeticReg,componentReg,Fin.ext_iff,h109,h115,h116]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 263 Q A U}

theorem familyGeneratedBoundaryRhs_ready_exec {s t : ℕ} [NeZero s]
    (P N q l u band a b : ℕ) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 263 Q A U) (S : Stacks 263 A)
    (hsrc : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (hready : LengthKeyReady P N q l s t u band 0 0 (S.R 110) (embStk familyCouplingSourceReg S))
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (hcount : (S.R 116).length = (haloBoundary s t band a b).card)
    (h138 : S.R 138 = []) (h139 : S.R 139 = []) (h143 : S.R 143 = [])
    (hleft : ∀ r : Fin 148, S.L (familyGeneratedRhsReg r) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ familyGeneratedBoundaryRhsCost P q s t u band a b ∧
      Exec body familyGeneratedBoundaryRhs (mk v S) m
        (mk v' {S with R := (Function.update S.R 206
          (cstream A (2*q+8) ((bFoldOrder s (haloBoundary s t band a b)).map C)++S.R 206))}) := by
  have hid (i : Fin 144) (h109 : i ≠ 109) (h115 : i ≠ 115) (h116 : i ≠ 116) :
      S.R (familyCouplingSourceReg i) = S.R (familyGeneratedRhsReg (boundaryRhsHeaderReg i)) := by
    rw [familyCouplingSourceReg_identity i h109 h115 h116]
  have hblank (i : Fin 144) (hi : i.val < 117) (h93 : i ≠ 93) (h110 : i ≠ 110)
      (h109 : i ≠ 109) (h115 : i ≠ 115) (h116 : i ≠ 116) :
      S.R (familyGeneratedRhsReg (boundaryRhsHeaderReg i)) = [] := by
    rw [← hid i h109 h115 h116]
    exact hready.blank i hi h93 h110
  apply familyGeneratedBoundaryRhs_exec P q u band a b hst haS hbS hA C tail v S hsrc
  · intro r hr
    simp only [couplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have hm := hready.masters (117,114) (by simp [groupHeaderCopies])
      simpa [embStk,Function.comp_def,familyCouplingSourceReg_identity,
        groupHeaderValue,couplingHeaderValue] using hm
    · have hm := hready.masters (119,112) (by simp [groupHeaderCopies])
      simpa [embStk,Function.comp_def,familyCouplingSourceReg_identity,
        groupHeaderValue,couplingHeaderValue] using hm
    · have hm := hready.masters (121,97) (by simp [groupHeaderCopies])
      simpa [embStk,Function.comp_def,familyCouplingSourceReg_identity,
        groupHeaderValue,couplingHeaderValue] using hm
    · have hm := hready.masters (122,98) (by simp [groupHeaderCopies])
      simpa [embStk,Function.comp_def,familyCouplingSourceReg_identity,
        groupHeaderValue,couplingHeaderValue] using hm
    · have hm := hready.masters (123,99) (by simp [groupHeaderCopies])
      simpa [embStk,Function.comp_def,familyCouplingSourceReg_identity,
        groupHeaderValue,couplingHeaderValue] using hm
    · have hm := hready.masters (124,100) (by simp [groupHeaderCopies])
      simpa [embStk,Function.comp_def,familyCouplingSourceReg_identity,
        groupHeaderValue,couplingHeaderValue] using hm
    · simpa [couplingHeaderValue,familyGeneratedRhsReg,boundaryRhsHeaderReg] using ha
    · simpa [couplingHeaderValue,familyGeneratedRhsReg,boundaryRhsHeaderReg] using hb
  · intro r hr
    simp only [couplingHeaderRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact hblank _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact hcount
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hblank 106 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hblank 108 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · have hm := hready.fresh 135 (by simp)
      simpa [embStk,Function.comp_def,familyCouplingSourceReg_identity,familyGeneratedRhsReg,boundaryRhsHeaderReg] using hm
    · exact h138
    · exact h139
    · exact h143
  · intro r hr
    let i : Fin 144 := ⟨r.val,by omega⟩
    have hi : i.val < 77 := hr
    have hz := hblank i (by omega) (by simp only [ne_eq,Fin.ext_iff]; omega)
      (by simp only [ne_eq,Fin.ext_iff]; omega) (by simp only [ne_eq,Fin.ext_iff]; omega)
      (by simp only [ne_eq,Fin.ext_iff]; omega) (by simp only [ne_eq,Fin.ext_iff]; omega)
    simpa [familyGeneratedRhsReg,boundaryRhsHeaderReg,i] using hz
  · exact hleft

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
