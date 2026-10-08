import IntegerMultBounds.Machine.CountedBankReset
import IntegerMultBounds.Machine.BinaryDescriptorInstall
import IntegerMultBounds.Machine.SharedBank

/-! Reset selected native payload tapes using a physically copied existing
marked length header. Both appended work tapes start entirely blank. -/
namespace IntegerMultBounds.Machine.CountedBankResetHeader
open CountedBankReset
variable {t a : ℕ}
noncomputable section

def rawBank (v : Tapes t a) (bs : List Bool) : Tapes (t+2) a :=
  v.append ⟨![0,1],![fun _ => blank,CountedLoopReuseAlphabet.binary bs]⟩

def initProgram : Program (t+2) 2 a where
  tapes_pos := by omega
  start := 0
  transition := fun st sy => if st = 0 then some (1,fun i =>
    (if i = Fin.natAdd t (0 : Fin 2) then separator else sy i,
      if i = Fin.natAdd t (0 : Fin 2) then .right else .stay)) else none

theorem initializes_hoare (v : Tapes t a) (bs : List Bool) :
    HoareTime initProgram (fun w => w = rawBank v bs) (fun w => w = bank v bs) 1 := by
  rintro w rfl
  refine ⟨1,⟨1,(bank v bs).head,(bank v bs).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,initProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      induction i using Fin.addCases with
      | left i =>
        have hi : Fin.castAdd 2 i ≠ Fin.natAdd t (0 : Fin 2) := by
          intro he; have hv := congrArg Fin.val he; simp only [Fin.val_castAdd,Fin.val_natAdd] at hv; omega
        simp [rawBank,bank,CountedLoopReuseAlphabet.bank,Tapes.append,Move.offset,hi]
      | right i => fin_cases i <;>
          simp [rawBank,bank,CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,Tapes.append,Move.offset]
    · funext i z
      induction i using Fin.addCases with
      | left i =>
        have hi : Fin.castAdd 2 i ≠ Fin.natAdd t (0 : Fin 2) := by
          intro he; have hv := congrArg Fin.val he; simp only [Fin.val_castAdd,Fin.val_natAdd] at hv; omega
        simp [rawBank,bank,CountedLoopReuseAlphabet.bank,Tapes.append,hi]
        intro hz; subst z; rfl
      | right i => fin_cases i <;>
          simp [rawBank,bank,CountedLoopReuseAlphabet.bank,CountedLoopReuseAlphabet.controls,
            CountedLoopReuseAlphabet.empty,Tapes.append] <;> (intro hz; subst z; rfl)
  · simp [step,initProgram]

theorem distinct (src : Fin t) : Fin.castAdd 2 src ≠ Fin.natAdd t (1 : Fin 2) := by
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

def installProgram (src : Fin t) := BinaryDescriptorInstall.program a
  (Fin.castAdd 2 src) (Fin.natAdd t (1 : Fin 2)) (distinct src)

theorem installs_hoare (src : Fin t) (v : Tapes t a) (bs : List Bool)
    (hv : v.head src = 1 ∧ v.tape src = RadixZeroFill.encodedBinary bs) :
    HoareTime (installProgram (a := a) src) (fun w => w = v.append (SharedBank.empty 2 a))
      (fun w => w = rawBank v bs) (2*bs.length+5) := by
  have h := BinaryDescriptorInstall.install_hoare (Fin.castAdd 2 src) (Fin.natAdd t (1 : Fin 2))
    (distinct src) (v.append (SharedBank.empty 2 a)) bs
    (by simpa only [Tapes.append,Fin.addCases_left] using hv.2)
    (by simpa only [Tapes.append,Fin.addCases_left] using hv.1) (by simp [Tapes.append,SharedBank.empty]) (by simp [Tapes.append,SharedBank.empty])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  have he : RadixZeroFill.encodedBinary bs = CountedLoopReuseAlphabet.binary (a := a) bs :=
    CountedLoopReuseAlphabet.encoding_binary bs
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i => simp [SharedPlacementAlphabet.setTape,rawBank,Tapes.append,Function.update_of_ne (distinct i)]
  | right i => fin_cases i <;>
      simp [SharedPlacementAlphabet.setTape,rawBank,Tapes.append,SharedBank.empty,he]

def program (ht : 0 < t) (selected : Fin t → Bool) (src : Fin t) :=
  seq (seq (installProgram (a := a) src) initProgram) (CountedBankReset.program ht selected)

theorem resets_hoare (ht : 0 < t) (selected : Fin t → Bool) (src : Fin t) (v : Tapes t a)
    (bs : List Bool) (n : ℕ) (hv : v.head src = 1 ∧ v.tape src = RadixZeroFill.encodedBinary bs)
    (hn : Counter.value bs = n) (hc : GrowingCounterData.Canonical bs) :
    HoareTime (program ht selected src) (fun w => w = v.append (SharedBank.empty 2 a))
      (fun w => w = bank (restored selected v n) bs) (30*n+57) := by
  have h := ((installs_hoare src v bs hv).seq (initializes_hoare v bs)).seq
    (CountedBankReset.resets_hoare_linear ht selected v bs n hn hc)
  have hw := GrowingCounterData.canonical_width bs hc
  rw [hn] at hw
  have hl := Nat.log2_le_self n
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CountedBankResetHeader
