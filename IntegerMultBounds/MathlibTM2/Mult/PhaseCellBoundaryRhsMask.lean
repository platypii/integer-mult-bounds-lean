module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedCouplingSourceMask
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Generate an owned boundary mask without touching the borrowed coordinate page or its width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def boundaryRhsMaskReg (i : Fin 117) : Fin 148 :=
  Equiv.swap 109 139 (Equiv.swap 115 138 ⟨i.val,by omega⟩)

theorem boundaryRhsMaskReg_injective : Function.Injective boundaryRhsMaskReg := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun r : Fin 148 => r.val)
    ((Equiv.injective (Equiv.swap (115 : Fin 148) 138))
      ((Equiv.injective (Equiv.swap (109 : Fin 148) 139)) hij))

@[simp] theorem boundaryRhsMaskReg_s : boundaryRhsMaskReg 97 = 97 := by norm_num [boundaryRhsMaskReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsMaskReg_t : boundaryRhsMaskReg 98 = 98 := by norm_num [boundaryRhsMaskReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsMaskReg_band : boundaryRhsMaskReg 100 = 100 := by norm_num [boundaryRhsMaskReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsMaskReg_a : boundaryRhsMaskReg 101 = 101 := by norm_num [boundaryRhsMaskReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsMaskReg_b : boundaryRhsMaskReg 103 = 103 := by norm_num [boundaryRhsMaskReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsMaskReg_work : boundaryRhsMaskReg 106 = 106 := by norm_num [boundaryRhsMaskReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsMaskReg_clock : boundaryRhsMaskReg 108 = 108 := by norm_num [boundaryRhsMaskReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsMaskReg_output : boundaryRhsMaskReg 109 = 139 := by norm_num [boundaryRhsMaskReg,Equiv.swap_apply_def]
@[simp] theorem boundaryRhsMaskReg_width : boundaryRhsMaskReg 115 = 138 := by norm_num [boundaryRhsMaskReg,Equiv.swap_apply_def]

theorem boundaryRhsMaskReg_low (i : Fin 117) (hi : i.val < 31) : boundaryRhsMaskReg i = ⟨i.val,by omega⟩ := by
  have h109 : (⟨i.val,by omega⟩ : Fin 148) ≠ 109 := by intro hh; have := congrArg Fin.val hh; norm_num at this; omega
  have h115 : (⟨i.val,by omega⟩ : Fin 148) ≠ 115 := by intro hh; have := congrArg Fin.val hh; norm_num at this; omega
  have h138 : (⟨i.val,by omega⟩ : Fin 148) ≠ 138 := by intro hh; have := congrArg Fin.val hh; norm_num at this; omega
  have h139 : (⟨i.val,by omega⟩ : Fin 148) ≠ 139 := by intro hh; have := congrArg Fin.val hh; norm_num at this; omega
  simp [boundaryRhsMaskReg,Equiv.swap_apply_def,h109,h115,h138,h139]

def boundaryRhsMask : Pr P 148 Q A U :=
  embProg boundaryRhsMaskReg Empty.elim (closedCouplingSourceMask (P₀ := Empty) true)

theorem boundaryRhsMask_exec {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t) (hband : (S.R 100).length = band)
    (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h138 : S.R 138 = []) (h139 : S.R 139 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 148, r.val < 31 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ closedCouplingSourceMaskCost s t band a b ∧
      Exec body boundaryRhsMask (mk v S) m
        (mk v' {S with R := Function.update S.R 139 (couplingSourceMaskSymbols true A s t band a b)}) := by
  obtain ⟨vi,m,hu,hm,he⟩ := closedCouplingSourceMask_exec (body := fun p : Empty => nomatch p)
    true hst haS hbS hA (embDn boundaryRhsMaskReg v) (embStk boundaryRhsMaskReg S)
    (by simpa [embStk] using hs) (by simpa [embStk] using ht) (by simpa [embStk] using hband)
    (by simpa [embStk] using ha) (by simpa [embStk] using hb)
    (by simpa [embStk] using h138) (by simpa [embStk] using h106) (by simpa [embStk] using h108)
    (by intro r hr; simpa [embStk,boundaryRhsMaskReg_low r hr] using hblank ⟨r.val,by omega⟩ hr)
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    boundaryRhsMaskReg_injective (fun p => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [embOvr_updR boundaryRhsMaskReg_injective,embOvr_stk]
  simp [embStk,h139]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
