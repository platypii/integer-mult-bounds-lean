import IntegerMultBounds.Machine.CountedBankResetHeader
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.RawLinearCombinationCleanup

/-! Original-header counted loops with explicit binary-control erasure. No head
normalization is assumed: every body head may start and finish at any position.
Only two blank work tapes are needed, and both are physically blank afterwards. -/
namespace IntegerMultBounds.Machine.CountedLoopHeaderClean
noncomputable section
variable {t q a : ℕ}

def controlCleanup : Program 2 9 a := BinaryDescriptorCleanupList.program (by decide) [0,1]

def cleanup := RawLinearCombinationCleanup.prepend (controlCleanup (a:=a)) t

def rawProgram (M : Program t q a) (src : Fin t) :=
  seq (seq (CountedBankResetHeader.installProgram (a:=a) src) CountedBankResetHeader.initProgram)
    (CountedLoopReuseAlphabet.program M)

def program (M : Program t q a) (src : Fin t) :=
  seq (rawProgram M src) (cleanup (t:=t) (a:=a))

def bank (v : Tapes t a) := v.append (SharedBank.empty 2 a)
def cost (n : ℕ) (bs : List Bool) (cost : ℕ → ℕ) :=
  (∑ i ∈ Finset.range n,cost i)+6*n+11*bs.length+35

private theorem binary_descriptor (bs : List Bool) :
    CountedLoopReuseAlphabet.binary (a:=a) bs=BinaryDescriptorStack.descriptor bs := by
  rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact CountedLoopReuseAlphabet.encoding_binary bs |>.symm

private theorem controls_clean (bs : List Bool) :
    HoareTime (controlCleanup (a:=a))
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

/-- The original count descriptor is physically copied and all generated
controls are erased. Body data and their actual heads are preserved exactly. -/
theorem runs (M : Program t q a) (src : Fin t) (bs : List Bool) (n : ℕ)
    (v : ℕ → Tapes t a) (bodyCost : ℕ → ℕ)
    (hheader : (v 0).head src=1 ∧ (v 0).tape src=RadixZeroFill.encodedBinary bs)
    (hn : Counter.value bs=n)
    (hbody : ∀ i<n,HoareTime M (fun w => w=v i) (fun w => w=v (i+1)) (bodyCost i)) :
    HoareTime (program M src) (fun w => w=bank (v 0)) (fun w => w=bank (v n))
      (cost n bs bodyCost) := by
  have h0 := CountedBankResetHeader.installs_hoare src (v 0) bs hheader
  have h1 := CountedBankResetHeader.initializes_hoare (v 0) bs
  have h2 := CountedLoopReuseAlphabet.loop_hoare M bs n v bodyCost hn hbody
  have h3 := RawLinearCombinationCleanup.prepend_runs controlCleanup
    (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty
      (CountedLoopReuseAlphabet.binary bs) 1 1) (SharedBank.empty 2 a) (v n) (controls_clean bs)
  exact (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost; omega)

end
end IntegerMultBounds.Machine.CountedLoopHeaderClean
