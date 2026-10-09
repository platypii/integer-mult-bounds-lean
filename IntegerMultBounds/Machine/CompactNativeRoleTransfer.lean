import IntegerMultBounds.Machine.CompactNativeRoleGeometry
import IntegerMultBounds.Machine.CyclicRowNormalized
import IntegerMultBounds.Machine.CountedLoopHeaderClean

/-! Native coefficient role copy contracts use complete physical records and
paid origin rewinds; a clean counted source reset is reusable by the original
header caller. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleTransfer
noncomputable section
open CompactNativeRoleGeometry
open NativeZeroPaddingArray (word)
open CyclicRowSplit (bank)
open RecursiveChildQuotientsConstant (bits)
variable {a t : ℕ}

theorem binary_descriptor (bs : List Bool) :
    CountedLoopReuseAlphabet.binary (a:=a) bs=BinaryDescriptorStack.descriptor bs := by
  rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact CountedLoopReuseAlphabet.encoding_binary bs |>.symm

theorem controls_clean (bs : List Bool) :
    HoareTime (CountedLoopHeaderClean.controlCleanup (a:=a))
      (fun w => w=CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty
        (CountedLoopReuseAlphabet.binary bs) 1 1)
      (fun w => w=SharedBank.empty 2 a) (2*bs.length+10) := by
  let v := CountedLoopReuseAlphabet.controls (a:=a) CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary bs) 1 1
  have hh := BinaryDescriptorCleanupList.cleanup_hoare (a:=a) (by decide : 0<2) [0,1]
    (by decide) ![[],bs] v (by
      intro i hi
      fin_cases i
      · constructor
        · rfl
        · exact binary_descriptor []
      · constructor
        · rfl
        · exact binary_descriptor bs)
  have he : BinaryDescriptorCleanupList.cleared [0,1] v=SharedBank.empty 2 a := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  exact hh.consequence (fun _ h => h) (fun _ h => by simpa only [he] using h)
    (by simp [BinaryDescriptorCleanupList.cost]; omega)


def resetProgram (ht : 0<t) (selected : Fin t → Bool) (src : Fin t) :=
  seq (CountedBankResetHeader.program ht selected src) (CountedLoopHeaderClean.cleanup (t:=t) (a:=a))

theorem reset_runs (ht : 0<t) (selected : Fin t → Bool) (src : Fin t)
    (v : Tapes t a) (n : ℕ)
    (hv : v.head src=1 ∧ v.tape src=RadixZeroFill.encodedBinary (bits n)) :
    HoareTime (resetProgram ht selected src)
      (fun w => w=v.append (SharedBank.empty 2 a))
      (fun w => w=(CountedBankReset.restored selected v n).append (SharedBank.empty 2 a))
      (30*n+2*(bits n).length+68) := by
  have h0 := CountedBankResetHeader.resets_hoare ht selected src v (bits n) n hv
    (RecursiveChildQuotientsConstant.bits_value n) (RecursiveChildQuotientsConstant.bits_canonical n)
  have h1 := RawLinearCombinationCleanup.prepend_runs CountedLoopHeaderClean.controlCleanup
    (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary (bits n)) 1 1)
    (SharedBank.empty 2 a) (CountedBankReset.restored selected v n) (controls_clean (bits n))
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by omega)

def input {n c L : ℕ} (f : Array n c L) (w : ℕ) :=
  bank (CyclicRowCopy.bank (c:=c) (NativeZeroPadding.word (word f)) (fun _ _ => blank) 0 (fun _ => 0)
    (bits (L*(2*(w+1))))) (bits n)
def output {n c L : ℕ} (f : Array n c L) (w : ℕ) :=
  bank (CyclicRowCopy.bank (NativeZeroPadding.word (word f))
    (fun j => NativeZeroPadding.word (word (role f j))) 0 (fun _ => 0)
    (bits (L*(2*(w+1))))) (bits n)
def roles {n c L : ℕ} (f : Array n c L) (w : ℕ) :=
  bank (CyclicRowCopy.bank (fun _ => blank)
    (fun j => NativeZeroPadding.word (word (role f j))) 0 (fun _ => 0)
    (bits (L*(2*(w+1))))) (bits n)

theorem split_runs {n c L : ℕ} (w : ℕ) (f : Array n c L)
    (hw : ∀ z,(f z).1.length=w ∧ (f z).2.length=w) :
    HoareTime (CyclicRowNormalized.splitProgram c 2)
      (fun v => v=input f w) (fun v => v=output f w)
      (CyclicRowNormalized.cost c n (L*(2*(w+1))) (bits (L*(2*(w+1)))) (bits n)) := by
  have hh := CyclicRowNormalized.split_hoare (fun _ => blank) (fun _ _ => blank) 0 (fun _ => 0)
    (row f) (L*(2*(w+1))) (row_length w f hw) (bits (L*(2*(w+1)))) (bits n)
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
  simpa only [source_word,role_word,input,output,NativeZeroPadding.word] using hh

theorem merge_runs {n c L : ℕ} (w : ℕ) (f : Array n c L)
    (hw : ∀ z,(f z).1.length=w ∧ (f z).2.length=w) :
    HoareTime (CyclicRowNormalized.mergeProgram c 2)
      (fun v => v=roles f w) (fun v => v=output f w)
      (CyclicRowNormalized.cost c n (L*(2*(w+1))) (bits (L*(2*(w+1)))) (bits n)) := by
  have hh := CyclicRowNormalized.merge_hoare (fun _ => blank) (fun _ _ => blank) 0 (fun _ => 0)
    (row f) (L*(2*(w+1))) (row_length w f hw) (bits (L*(2*(w+1)))) (bits n)
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
  simpa only [source_word,role_word,roles,output,NativeZeroPadding.word] using hh

end
end IntegerMultBounds.Machine.CompactNativeRoleTransfer
