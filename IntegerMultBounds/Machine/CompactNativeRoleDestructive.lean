import IntegerMultBounds.Machine.CompactNativeRoleTransfer

/-! Complete native cyclic transfers with separately paid source erasure.
Split clears the common word; merge clears every role word. All origins and
the reset workspace return to zero, with the exact immutable count retained. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleDestructive
noncomputable section
open CompactNativeRoleGeometry
open NativeZeroPaddingArray (word)
open RecursiveChildQuotientsConstant (bits)
open CompactNativeRoleTransfer

abbrev localCount (c : ℕ) := ((1+c)+2)+2
def withCount {t : ℕ} (v : Tapes t 2) (n : ℕ) := v.append
  (⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary (bits n)⟩ : Tapes 1 2)
def bank {t : ℕ} (v : Tapes t 2) (n : ℕ) := (withCount v n).append (SharedBank.empty 2 2)
def sourceMask (c : ℕ) (i : Fin (localCount c+1)) := decide (i.val=0)
def roleMask (c : ℕ) (i : Fin (localCount c+1)) := decide (1 ≤ i.val ∧ i.val < 1+c)
def countSlot (c : ℕ) : Fin (localCount c+1) := Fin.natAdd (localCount c) 0

def splitProgram (c : ℕ) := seq (extend (extend (CyclicRowNormalized.splitProgram c 2) 1) 2)
  (resetProgram (by omega) (sourceMask c) (countSlot c))
def mergeProgram (c : ℕ) := seq (extend (extend (CyclicRowNormalized.mergeProgram c 2) 1) 2)
  (resetProgram (by omega) (roleMask c) (countSlot c))

theorem restore_source {n c L : ℕ} (w : ℕ) (f : Array n c L)
    (hw : ∀ z,(f z).1.length=w ∧ (f z).2.length=w) :
    CountedBankReset.restored (sourceMask c) (withCount (output f w) ((n*c)*L*(2*(w+1))))
      ((n*c)*L*(2*(w+1)))=withCount (roles f w) ((n*c)*L*(2*(w+1))) := by
  have hlen := CompactReservationNativePaddingBudget.word_length w f hw
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    induction i using Fin.addCases with
    | right i =>
      have hm : sourceMask c (Fin.natAdd (localCount c) i)=false := by
        simp only [sourceMask,Fin.val_natAdd]
        apply decide_eq_false_iff_not.mpr
        unfold localCount
        omega
      simp only [CountedBankReset.after,hm,Bool.false_eq_true,ite_false]
      simp only [withCount,Tapes.append,Fin.addCases_right]
    | left i =>
      induction i using Fin.addCases with
      | right i =>
        have hm : sourceMask c (Fin.castAdd 1 (Fin.natAdd ((1+c)+2) i))=false := by
          simp only [sourceMask,Fin.val_natAdd,Fin.val_castAdd]
          apply decide_eq_false_iff_not.mpr
          omega
        simp only [CountedBankReset.after,hm,Bool.false_eq_true,ite_false]
        simp only [withCount,Tapes.append,Fin.addCases_left,Fin.addCases_right,output,roles,CyclicRowSplit.bank,CountedLoopReuseAlphabet.bank]
      | left i =>
        induction i using Fin.addCases with
        | right i =>
          have hm : sourceMask c (Fin.castAdd 1 (Fin.castAdd 2 (Fin.natAdd (1+c) i)))=false := by
            simp only [sourceMask,Fin.val_natAdd,Fin.val_castAdd]
            apply decide_eq_false_iff_not.mpr
            omega
          simp only [CountedBankReset.after,hm,Bool.false_eq_true,ite_false]
          simp only [withCount,Tapes.append,Fin.addCases_left,Fin.addCases_right,output,roles,CyclicRowSplit.bank,CyclicRowCopy.bank,CountedLoopReuseAlphabet.bank]
        | left i =>
          induction i using Fin.addCases with
          | right i =>
            have hm : sourceMask c (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 (Fin.natAdd 1 i))))=false := by
              simp only [sourceMask,Fin.val_natAdd,Fin.val_castAdd]
              apply decide_eq_false_iff_not.mpr
              omega
            simp only [CountedBankReset.after,hm,Bool.false_eq_true,ite_false]
            simp only [withCount,Tapes.append,Fin.addCases_left,Fin.addCases_right,output,roles,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,CountedLoopReuseAlphabet.bank]
          | left i =>
            fin_cases i
            simpa only [CountedBankReset.after,sourceMask,withCount,Tapes.append,
              output,roles,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,CountedLoopReuseAlphabet.bank,
              Fin.addCases_left,Fin.val_castAdd,decide_true,ite_true,NativeZeroPadding.word,hlen] using
              CountedBankReset.erased_word (word f) 0

theorem split_runs {n c L : ℕ} (w : ℕ) (f : Array n c L)
    (hw : ∀ z,(f z).1.length=w ∧ (f z).2.length=w) :
    HoareTime (splitProgram c)
      (fun v => v=bank (CompactNativeRoleTransfer.input f w) ((n*c)*L*(2*(w+1))))
      (fun v => v=bank (roles f w) ((n*c)*L*(2*(w+1))))
      (CyclicRowNormalized.cost c n (L*(2*(w+1))) (bits (L*(2*(w+1)))) (bits n)+
        30*((n*c)*L*(2*(w+1)))+2*(bits ((n*c)*L*(2*(w+1)))).length+69) := by
  have h0 := hoare_extend_eq (hoare_extend_eq (CompactNativeRoleTransfer.split_runs w f hw)
    (⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary (bits ((n*c)*L*(2*(w+1))))⟩ : Tapes 1 2))
    (SharedBank.empty 2 2)
  have h1 := reset_runs (by omega) (sourceMask c) (countSlot c)
    (withCount (output f w) ((n*c)*L*(2*(w+1)))) ((n*c)*L*(2*(w+1))) (by
      simp [withCount,countSlot,Tapes.append])
  rw [restore_source w f hw] at h1
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem restore_roles {n c L : ℕ} (w : ℕ) (f : Array n c L)
    (hw : ∀ z,(f z).1.length=w ∧ (f z).2.length=w) :
    CountedBankReset.restored (roleMask c) (withCount (output f w) (n*L*(2*(w+1))))
      (n*L*(2*(w+1)))=withCount (CompactNativeRoleTransfer.input f w) (n*L*(2*(w+1))) := by
  have hlen (j : Fin c) : (word (role f j)).length=n*L*(2*(w+1)) :=
    CompactReservationNativePaddingBudget.word_length w _ (fun z => hw _)
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    induction i using Fin.addCases with
    | right i =>
      have hm : roleMask c (Fin.natAdd (localCount c) i)=false := by
        simp only [roleMask,Fin.val_natAdd]
        apply decide_eq_false_iff_not.mpr
        unfold localCount
        omega
      simp only [CountedBankReset.after,hm,Bool.false_eq_true,ite_false,withCount,Tapes.append,Fin.addCases_right]
    | left i =>
      induction i using Fin.addCases with
      | right i =>
        have hm : roleMask c (Fin.castAdd 1 (Fin.natAdd ((1+c)+2) i))=false := by
          simp only [roleMask,Fin.val_natAdd,Fin.val_castAdd]
          apply decide_eq_false_iff_not.mpr
          omega
        simp only [CountedBankReset.after,hm,Bool.false_eq_true,ite_false,withCount,Tapes.append,
          Fin.addCases_left,Fin.addCases_right,output,CompactNativeRoleTransfer.input,CyclicRowSplit.bank,CountedLoopReuseAlphabet.bank]
      | left i =>
        induction i using Fin.addCases with
        | right i =>
          have hm : roleMask c (Fin.castAdd 1 (Fin.castAdd 2 (Fin.natAdd (1+c) i)))=false := by
            simp only [roleMask,Fin.val_natAdd,Fin.val_castAdd]
            apply decide_eq_false_iff_not.mpr
            omega
          simp only [CountedBankReset.after,hm,Bool.false_eq_true,ite_false,withCount,Tapes.append,
            Fin.addCases_left,Fin.addCases_right,output,CompactNativeRoleTransfer.input,CyclicRowSplit.bank,CyclicRowCopy.bank,CountedLoopReuseAlphabet.bank]
        | left i =>
          induction i using Fin.addCases with
          | right i =>
            have hm : roleMask c (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 2 (Fin.natAdd 1 i))))=true := by
              simp only [roleMask,Fin.val_natAdd,Fin.val_castAdd]
              apply decide_eq_true_eq.mpr
              have := i.isLt
              omega
            simpa only [CountedBankReset.after,hm,ite_true,withCount,Tapes.append,
              Fin.addCases_left,Fin.addCases_right,output,CompactNativeRoleTransfer.input,CyclicRowSplit.bank,CyclicRowCopy.bank,
              CyclicRowCopy.payload,CountedLoopReuseAlphabet.bank,NativeZeroPadding.word,hlen] using
              CountedBankReset.erased_word (word (role f i)) 0
          | left i =>
            fin_cases i
            simp [CountedBankReset.after,roleMask,withCount,Tapes.append,
              Fin.addCases_left,output,CompactNativeRoleTransfer.input,CyclicRowSplit.bank,CyclicRowCopy.bank,
              CyclicRowCopy.payload,CountedLoopReuseAlphabet.bank]

theorem merge_runs {n c L : ℕ} (w : ℕ) (f : Array n c L)
    (hw : ∀ z,(f z).1.length=w ∧ (f z).2.length=w) :
    HoareTime (mergeProgram c)
      (fun v => v=bank (roles f w) (n*L*(2*(w+1))))
      (fun v => v=bank (CompactNativeRoleTransfer.input f w) (n*L*(2*(w+1))))
      (CyclicRowNormalized.cost c n (L*(2*(w+1))) (bits (L*(2*(w+1)))) (bits n)+
        30*(n*L*(2*(w+1)))+2*(bits (n*L*(2*(w+1)))).length+69) := by
  have h0 := hoare_extend_eq (hoare_extend_eq (CompactNativeRoleTransfer.merge_runs w f hw)
    (⟨fun _ => 1,fun _ => RadixZeroFill.encodedBinary (bits (n*L*(2*(w+1))))⟩ : Tapes 1 2))
    (SharedBank.empty 2 2)
  have h1 := reset_runs (by omega) (roleMask c) (countSlot c)
    (withCount (output f w) (n*L*(2*(w+1)))) (n*L*(2*(w+1))) (by
      simp [withCount,countSlot,Tapes.append])
  rw [restore_roles w f hw] at h1
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CompactNativeRoleDestructive
