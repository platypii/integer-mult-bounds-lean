module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalPageInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalPageWidth

/-! Ordinary diagonal-page loading, with register separation and input fits derived. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
noncomputable section

theorem diagonalPageWords_fits (s t u p w c n : ℕ) (hst : s ≤ t) (hfit : c+n ≤ s) :
    ∀ a ∈ diagonalPageWords s t u p c n, a.2 < 2^diagonalPageWidth p w u t := by
  let B := diagonalPageWidth p w u t
  have hsmall (x : ℕ) (hx : Nat.size x ≤ B) : x < 2^B :=
    (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by decide) hx)
  have ht : t < 2^B := hsmall t (by dsimp [B,diagonalPageWidth,coefficientWorkspaceWidth]; omega)
  have hu : u < 2^B := hsmall u (by dsimp [B,diagonalPageWidth,coefficientWorkspaceWidth]; omega)
  have hp : p < 2^B := Nat.lt_two_pow_self.trans_le
    (Nat.pow_le_pow_right (by decide) (show p ≤ B by dsimp [B,diagonalPageWidth,coefficientWorkspaceWidth]; omega))
  dsimp only [B] at ht hu hp
  intro a ha
  simp only [diagonalPageWords,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem diagonalPageState_fits {A : ℕ} (s t u p w c n : ℕ) (hst : s ≤ t) (hfit : c+n ≤ s) :
    ∀ i, (loadedBinaryState (diagonalPageWords s t u p c n)
      (⟨fun _ => 0,[]⟩ : TblSt 48 A)).val i < 2^diagonalPageWidth p w u t := by
  intro i
  have h := diagonalPageWords_fits s t u p w c n hst hfit
  have hs := h (34,s) (by simp [diagonalPageWords])
  have ht := h (35,t) (by simp [diagonalPageWords])
  have hu := h (36,u) (by simp [diagonalPageWords])
  have hp := h (19,p) (by simp [diagonalPageWords])
  have hc := h (37,c) (by simp [diagonalPageWords])
  have he := h (47,c+n) (by simp [diagonalPageWords])
  simp only [loadedBinaryState,diagonalPageWords]
  simp only [Function.update_apply]
  split_ifs <;> first | assumption | positivity

theorem diagonal_page_conversion_regs : ∀ src ∈ diagonalPageInputs.map Prod.snd,
    [src,diagonalTable .wr,diagonalWord,diagonalConvertSaved,diagonalConvertTmp,diagonalHeader].Nodup := by
  intro src hsrc
  have ht304 := diagonalTable_ne_work (TblR.wr : TblR 48) 304 (by decide)
  have ht305 := diagonalTable_ne_work (TblR.wr : TblR 48) 305 (by decide)
  have ht306 := diagonalTable_ne_work (TblR.wr : TblR 48) 306 (by decide)
  have ht307 := diagonalTable_ne_work (TblR.wr : TblR 48) 307 (by decide)
  have hwork : [diagonalWord,diagonalConvertSaved,diagonalConvertTmp,diagonalHeader].Nodup := by
    simp [diagonalWord,diagonalConvertSaved,diagonalConvertTmp,diagonalHeader,recovery_injective.eq_iff]
  have hoff : src ≠ diagonalTable .wr ∧ src ≠ diagonalWord ∧ src ≠ diagonalConvertSaved ∧
      src ≠ diagonalConvertTmp ∧ src ≠ diagonalHeader := by
    simp only [diagonalPageInputs,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hsrc
    rcases hsrc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | solve | simp [diagonalTable,diagonalWord,diagonalConvertSaved,diagonalConvertTmp,diagonalHeader,
          recovery_injective.eq_iff]
      | simp only [diagonalCoreStart,diagonalCoreEnd]
        constructor
        · exact (diagonalTable_ne_work _ _ (by decide)).symm
        · simp [diagonalWord,diagonalConvertSaved,diagonalConvertTmp,diagonalHeader,recovery_injective.eq_iff]
  regs_ne hwork
  regs_nodup

variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def loadDiagonalPageInputs : Pr P tapes Q A U :=
  installUnaryScalarInputs diagonalTable diagonalHeader diagonalWord diagonalConvertSaved
    diagonalConvertTmp diagonalCarry diagonalPageInputs

theorem loadDiagonalPageInputs_exec (s t u p w c n : ℕ) (hst : s ≤ t) (hfit : c+n ≤ s)
    (wl : List (Fin (A+4))) (hwl : wl.length = diagonalPageWidth p w u t)
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hS : (S.R (recovery (.parameter 4))).length = s)
    (hT : (S.R (recovery (.parameter 5))).length = t)
    (hu : (S.R (recovery (.parameter 1))).length = u)
    (hp : (S.R (recovery (.parameter 0))).length = p)
    (hc : (S.R diagonalCoreStart).length = c) (hend : (S.R diagonalCoreEnd).length = c+n)
    (hwidth : S.R (diagonalTable .wr) = wl)
    (hblank : ∀ r : TblR 48, r ≠ .wr → S.R (diagonalTable r) = [])
    (hwork : ∀ k ∈ [diagonalWord,diagonalConvertSaved,diagonalConvertTmp], S.R k = []) :
    ∃ v' F steps, v'.user = v.user ∧
      steps ≤ binaryHeaderQueueCost S.R (diagonalPageWidth p w u t) (diagonalPageInputs.map Prod.snd)+
        48*(4*diagonalPageWidth p w u t+4)+6*(8*diagonalPageWidth p w u t+8)+2 ∧
      Exec body loadDiagonalPageInputs (mk v S) steps (mk v' F) ∧
      tblHolds diagonalTable F (tblRho (diagonalPageWidth p w u t) wl []
        (loadedBinaryState (diagonalPageWords s t u p c n) ⟨fun _ => 0,[]⟩)) ∧
      (∀ i, (loadedBinaryState (diagonalPageWords s t u p c n)
        (⟨fun _ => 0,[]⟩ : TblSt 48 A)).val i < 2^diagonalPageWidth p w u t) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ k, (∀ r, diagonalTable r ≠ k) → F.R k = S.R k) := by
  obtain ⟨v',F,steps,hv,hm,he,hh,hin,hout,hL,hframe⟩ := installUnaryScalarInputs_exec
    (body := body) diagonalTable diagonalTable_injective diagonalHeader diagonalWord
    diagonalConvertSaved diagonalConvertTmp diagonalCarry
    (fun r => diagonalTable_ne_work r 304 (by decide)) diagonalPageInputs
    diagonal_page_conversion_regs (diagonalPageWidth p w u t) wl hwl v S hwidth hblank hwork
  rw [diagonalPageInputs_values S s t u p c n hS hT hu hp hc hend] at hh
  refine ⟨v',F,steps,hv,?_,he,hh,diagonalPageState_fits s t u p w c n hst hfit,hin,hout,hL,hframe⟩
  simpa only [diagonalPageInputs,List.length_cons,List.length_nil] using hm

def installDiagonalStreamWidth : Pr P tapes Q A U :=
  ucopy (recovery (.control .packet)) (diagonalTable .wn) diagonalConvertTmp

theorem installDiagonalStreamWidth_exec (B w : ℕ) (wl : List (Fin (A+4)))
    (st : TblSt 48 A) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hw : (S.R (recovery (.control .packet))).length = w)
    (hh : tblHolds diagonalTable S (tblRho B wl [] st))
    (htmp : S.R diagonalConvertTmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body installDiagonalStreamWidth (mk v S) (4*w+4)
        (mk v' {S with R := Function.update S.R (diagonalTable .wn) (List.replicate w tick)}) ∧
      tblHolds diagonalTable
        {S with R := Function.update S.R (diagonalTable .wn) (List.replicate w tick)}
        (tblRho B wl (List.replicate w tick) st) := by
  have hsource : recovery (.control .packet) ≠ diagonalTable .wn := by
    simp [diagonalTable,recovery_injective.eq_iff]
  have hsrcTmp : recovery (.control .packet) ≠ diagonalConvertTmp := by
    simp [diagonalConvertTmp,recovery_injective.eq_iff]
  have htableTmp : diagonalTable .wn ≠ diagonalConvertTmp :=
    diagonalTable_ne_work _ 307 (by decide)
  have hblank : S.R (diagonalTable .wn) = [] := hh .wn
  obtain ⟨v',hv,he⟩ := ucopy_exec (body := body) hsource hsrcTmp htableTmp v S htmp
  refine ⟨v',hv,?_,?_⟩
  · simpa [installDiagonalStreamWidth,hw,hblank] using he
  · intro r
    by_cases hr : r = .wn
    · subst r; simp [tblRho]
    · have hne : diagonalTable r ≠ diagonalTable .wn := fun h => hr (diagonalTable_injective h)
      simp only [Function.update_of_ne hne]
      rw [hh r]
      cases r <;> first | rfl | exact (hr rfl).elim

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
