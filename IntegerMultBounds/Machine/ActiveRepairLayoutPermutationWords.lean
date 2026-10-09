import IntegerMultBounds.Machine.BinaryAddressTableData
import IntegerMultBounds.Machine.ActiveRepairLayoutPermutationFields

/-! The real recovered machine words are the local permutation destination,
including unrestricted bad addresses. Concatenation is mathematical only. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutPermutationWords
noncomputable section
open ActiveRepairLayoutPermutationFields
open IntegerMultBounds.Compact IntegerMultBounds.Compact.PowerTwo

def wordFin (w : ℕ) (xs : List Bool) (hx : xs.length=w) : Fin (2^w) :=
  ⟨Counter.value xs,by simpa only [hx] using Counter.value_lt xs⟩
@[simp] theorem wordFin_val (w : ℕ) (xs : List Bool) (hx : xs.length=w) :
    (wordFin w xs hx).val=Counter.value xs := rfl
@[simp] theorem wordFin_row (w : ℕ) (x : Fin (2^w)) :
    wordFin w (BinaryAddressTableData.row w x.val) (BinaryAddressTableData.row_length _ _)=x := by
  apply Fin.ext
  exact BinaryAddressTableData.row_rank w x.val x.isLt

def earlyWords (q b n : ℕ) (V W : List Bool) (hV : V.length=n*q) (hW : W.length=n*b) : RawEarly q b n :=
  (wordFin _ V hV,wordFin _ W hW)
def lateWords (q b n : ℕ) (V W U : List Bool)
    (hV : V.length=n*q) (hW : W.length=n*b) (hU : U.length=n*b) : RawLate q b n :=
  (wordFin _ U hU,earlyWords q b n V W hV hW)

theorem early_words_addr (q b n : ℕ) (Z V W : List Bool) (hq : 1≤q) (hZ : Z.length=n)
    (hV : V.length=n*q) (hW : W.length=n*b) :
    earlyEquiv q b n Z hq hZ (earlyWords q b n V W hV hW)=addr q b Z (V++W) hq := by
  obtain ⟨hv,hw⟩ := ActiveRepairEarlyFieldsValue.original_fields q b V W Z
    (by simpa only [hZ] using hV) (by simpa only [hZ] using hW)
  change Gather.field (V++W) 0 (Z.length*q)=V at hv
  change Gather.field (V++W) (Z.length*q) (Z.length*b)=W at hw
  apply Prod.ext <;> apply Subtype.ext
  · simp only [earlyEquiv,Equiv.prodCongr_apply,Prod.map,target_value,earlyWords,wordFin_val,addr,Vw,hv]
  · simp only [earlyEquiv,Equiv.prodCongr_apply,Prod.map,temp_value,earlyWords,wordFin_val,addr,Ww,hw]

theorem late_words_addr (q b n : ℕ) (Z V W U : List Bool) (hq : 1≤q) (hZ : Z.length=n)
    (hV : V.length=n*q) (hW : W.length=n*b) (hU : U.length=n*b) :
    lateEquiv q b n Z hq hZ (lateWords q b n V W U hV hW hU)=
      lateWordsAddr q b Z V W U hq
        (by simpa only [hZ] using hV) (by simpa only [hZ] using hW) (by simpa only [hZ] using hU) := by
  apply Prod.ext
  · apply Subtype.ext
    simp only [lateEquiv,Equiv.prodCongr_apply,Prod.map,temp_value,lateWords,wordFin_val,lateWordsAddr]
  · apply Prod.ext <;> apply Subtype.ext
    · simp only [lateEquiv,earlyEquiv,Equiv.prodCongr_apply,Prod.map,target_value,lateWords,
        earlyWords,wordFin_val,lateWordsAddr]
    · simp only [lateEquiv,earlyEquiv,Equiv.prodCongr_apply,Prod.map,temp_value,lateWords,
        earlyWords,wordFin_val,lateWordsAddr]

def earlyRepaired (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (Z V W : List Bool)
    (hZ : Z.length=n) (hV : V.length=n*q) (hW : W.length=n*b) : RawEarly q b n := by
  have hv : V.length=Z.length*q := by simpa only [hZ] using hV
  have hw : W.length=Z.length*b := by simpa only [hZ] using hW
  have hwt := (PackedInverse.lengths q b hb hbq V W Z hv hw).2.2.2.2.2.2.2.1
  have hvt := (PackedInverse.lengths q b hb hbq V W Z hv hw).2.2.2.2.2.2.2.2.2
  exact earlyWords q b n (CountedIdealToggle.word q (PackedInverse.v q b hb hbq V W Z) Z)
    (PackedInverse.w q b hb hbq V W Z)
    (by rw [CountedIdealToggle.word_length q _ Z (by omega) hvt,hvt,hZ])
    (by simpa only [hZ] using hwt)

def lateRepaired (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (Z V W U : List Bool)
    (hZ : Z.length=n) (hV : V.length=n*q) (hW : W.length=n*b) (hU : U.length=n*b) : RawLate q b n := by
  have hv : V.length=Z.length*q := by simpa only [hZ] using hV
  have hw : W.length=Z.length*b := by simpa only [hZ] using hW
  have hu : U.length=Z.length*b := by simpa only [hZ] using hU
  have hu' := (CountedLateRepairInverse.lengths q b hb hbq V W U Z hv hw hu).2.2.2.1
  have hv' := (CountedLateRepairInverse.lengths q b hb hbq V W U Z hv hw hu).2.2.2.2.1
  have hw' := (CountedLateRepairInverse.lengths q b hb hbq V W U Z hv hw hu).2.2.2.2.2
  exact lateWords q b n (CountedIdealToggle.word q (CountedLateRepairInverse.target q b hb hbq V W U Z) Z)
    (CountedLateRepairInverse.temp q b hb hbq V W U Z) (CountedLateRepairInverse.restored b hb U Z)
    (by rw [CountedIdealToggle.word_length q _ Z (by omega) (hv'.trans hv),hv',hV])
    (hw'.trans hW) (hu'.trans hU)

theorem early_destination (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (Z V W : List Bool)
    (hZ : Z.length=n) (hV : V.length=n*q) (hW : W.length=n*b) :
    (earlyEquiv q b n Z (by omega) hZ).symm
      (Tperm q b Z ((Sperm q b Z).symm (earlyEquiv q b n Z (by omega) hZ
        (earlyWords q b n V W hV hW))))=earlyRepaired q b n hb hbq Z V W hZ hV hW := by
  rw [Equiv.symm_apply_eq,early_words_addr,inverse_bridge q b hb hbq Z (V++W) (by omega),toggle_bridge q b hb hbq Z (V++W) (by omega)]
  obtain ⟨hv,hw⟩ := ActiveRepairEarlyFieldsValue.original_fields q b V W Z
    (by simpa only [hZ] using hV) (by simpa only [hZ] using hW)
  change Gather.field (V++W) 0 (Z.length*q)=V at hv
  change Gather.field (V++W) (Z.length*q) (Z.length*b)=W at hw
  apply Prod.ext <;> apply Subtype.ext
  · simp only [toggled,recovered,Vw,Ww,hv,hw,earlyRepaired,earlyEquiv,Equiv.prodCongr_apply,
      Prod.map,target_value,earlyWords,wordFin_val,CountedIdealToggle.word]
  · simp only [toggled,recovered,Vw,Ww,hv,hw,earlyRepaired,earlyEquiv,Equiv.prodCongr_apply,
      Prod.map,temp_value,earlyWords,wordFin_val]

theorem late_destination (q b n : ℕ) (hb : 1≤b) (hbq : b+1≤q) (Z V W U : List Bool)
    (hZ : Z.length=n) (hV : V.length=n*q) (hW : W.length=n*b) (hU : U.length=n*b) :
    (lateEquiv q b n Z (by omega) hZ).symm
      (lateTperm q b Z ((lateSperm q b Z).symm (lateEquiv q b n Z (by omega) hZ
        (lateWords q b n V W U hV hW hU))))=lateRepaired q b n hb hbq Z V W U hZ hV hW hU := by
  rw [Equiv.symm_apply_eq,late_words_addr,late_inverse_words q b hb hbq]
  unfold lateRecovered
  rw [late_ideal_words]
  unfold lateRepaired
  rw [late_words_addr]

theorem early_flag (q b n : ℕ) (hb : 1≤b) (hbq : b+3≤q) (Z V W : List Bool)
    (hZ : Z.length=n) (hV : V.length=n*q) (hW : W.length=n*b) :
    ActiveRepairEarlyFieldsBank.flag q b V W Z=
      decide (badSet q b Z (earlyEquiv q b n Z (by omega) hZ (earlyWords q b n V W hV hW))) := by
  have hv : V.length=Z.length*q := by simpa only [hZ] using hV
  have hw : W.length=Z.length*b := by simpa only [hZ] using hW
  have hj := ActiveRepairEarlyFieldsValue.local_bound q b (by omega) V W Z hv hw
  have h := ActiveRepairEarlyFieldsValue.flag_rank q b hb hbq V W Z hv hw
  rw [rankFlag,dite_eq_left hj,rank_split q b Z (V++W) (by omega) _ hj rfl (by simp [hV,hW,hZ])] at h
  rw [←early_words_addr q b n Z V W (by omega) hZ hV hW] at h
  exact h

theorem late_flag (q b n : ℕ) (hb : 1≤b) (hbq : b+3≤q) (Z V W U : List Bool)
    (hZ : Z.length=n) (hV : V.length=n*q) (hW : W.length=n*b) (hU : U.length=n*b) :
    (CountedLateRepairGuard.flag q b V W Z || CountedLateRepairGuard.flag q b V U Z)=
      decide (lateBadSet q b Z (lateEquiv q b n Z (by omega) hZ (lateWords q b n V W U hV hW hU))) := by
  have hv : V.length=Z.length*q := by simpa only [hZ] using hV
  have hw : W.length=Z.length*b := by simpa only [hZ] using hW
  have hu : U.length=Z.length*b := by simpa only [hZ] using hU
  have hj := ActiveRepairLateFieldsValue.local_bound q b (by omega) V W U Z hv hw hu
  have h := ActiveRepairLateFieldsValue.flag_rank q b hb hbq V W U Z hv hw hu
  rw [rankFlag,dite_eq_left hj,late_rank_split q b Z (V++W++U) (by omega) _ hj rfl] at h
  have he : lateAddr q b Z (V++W++U) (by omega)=
      lateEquiv q b n Z (by omega) hZ (lateWords q b n V W U hV hW hU) := by
    rw [lateAddr_words]
    obtain ⟨h0,h1,h2⟩ := ActiveRepairLateFieldsValue.original_fields q b V W U Z hv hw hu
    change Gather.field (V++W++U) 0 (Z.length*q)=V at h0
    change Gather.field (V++W++U) (Z.length*q) (Z.length*b)=W at h1
    change Gather.field (V++W++U) (Z.length*q+Z.length*b) (Z.length*b)=U at h2
    change lateWordsAddr q b Z (Gather.field _ _ _) (Gather.field _ _ _) (Gather.field _ _ _) _ _ _ _ = _
    simpa only [h0,h1,h2] using (late_words_addr q b n Z V W U (by omega) hZ hV hW hU).symm
  rw [he] at h
  exact h

end
end IntegerMultBounds.Machine.ActiveRepairLayoutPermutationWords
