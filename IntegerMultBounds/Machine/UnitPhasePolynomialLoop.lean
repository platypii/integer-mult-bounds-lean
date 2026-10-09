import IntegerMultBounds.Machine.UnitPhaseSharedCoefficient
import IntegerMultBounds.Machine.CountedLoopHeaderClean

/-! A polynomial row shares one retained physical phase across its counted
coefficient stream. Persistent multiplicity on60 is read and preserved; two
loop-work tapes61/62 are physically erased afterwards. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialLoop
noncomputable section
open UnitPhaseNumerator (flags)
open UnitPhaseSharedCoefficient (coreSlots)
open DelimitedRadixRecord (Context)
open MarkedWordCleanup (one)

def body := extend UnitPhaseSharedCoefficient.program 1
def program := CountedLoopHeaderClean.program body (60 : Fin 61)
def state (v : Tapes 60 2) (ctx : ℕ → Context 2) (p : Fin 4) : ℕ → Tapes 60 2
  | 0 => v
  | i+1 => UnitPhaseSharedCoefficient.output (state v ctx p i) (ctx i) p

def flagsAt (v : Tapes 60 2) (p : Fin 4) := ∀ i : Fin 2,
  v.head ⟨48+i.val,by omega⟩=(flags p).head i ∧ v.tape ⟨48+i.val,by omega⟩=(flags p).tape i
def coreBlank (v : Tapes 60 2) := ∀ i : Fin 6,
  v.head (coreSlots i)=0 ∧ v.tape (coreSlots i)=(fun _ => blank)
def counted (v : Tapes 60 2) (ctx : ℕ → Context 2) (p : Fin 4) (R i : ℕ) :=
  (state v ctx p i).append (one (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits R)) 1)

theorem state_flags (v : Tapes 60 2) (ctx : ℕ → Context 2) (p : Fin 4)
    (h : flagsAt v p) (i : ℕ) : flagsAt (state v ctx p i) p := by
  cases i with
  | zero => exact h
  | succ i => intro j; exact UnitPhaseSharedCoefficient.flags_retained _ _ _ j

theorem state_core (v : Tapes 60 2) (ctx : ℕ → Context 2) (p : Fin 4)
    (h : coreBlank v) (i : ℕ) : coreBlank (state v ctx p i) := by
  cases i with
  | zero => exact h
  | succ i => intro j; exact UnitPhaseSharedCoefficient.core_blank _ _ _ j

theorem state_source (v : Tapes 60 2) (ctx : ℕ → Context 2) (p : Fin 4) (R : ℕ)
    (hflags : flagsAt v p) (hcore : coreBlank v)
    (hs : v.tape 56=(ctx 0).tape ∧ v.head 56=(ctx 0).start)
    (hnext : ∀ i,i+1<R → (ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2)
    (i : ℕ) (hi : i<R) :
    (state v ctx p i).tape 56=(ctx i).tape ∧ (state v ctx p i).head 56=(ctx i).start := by
  cases i with
  | zero => exact hs
  | succ i =>
    rw [state,UnitPhaseSharedCoefficient.output_eq _ _ _
      (state_flags v ctx p hflags i) (state_core v ctx p hcore i)]
    have h := hnext i hi
    simpa only [UnitPhaseSharedCoefficient.streamOutput,SharedPlacementAlphabet.setTape,
      Function.update_apply,show (56 : Fin 60)≠58 by decide,ite_false,ite_true] using ⟨h.1.symm,h.2.symm⟩

theorem runs (v : Tapes 60 2) (ctx : ℕ → Context 2) (p : Fin 4) (R w : ℕ)
    (hw : ∀ i<R,(ctx i).re.length=w ∧ (ctx i).im.length=w)
    (hflags : flagsAt v p) (hcore : coreBlank v)
    (hs : v.tape 56=(ctx 0).tape ∧ v.head 56=(ctx 0).start)
    (hnext : ∀ i,i+1<R → (ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2) :
    HoareTime program
      (fun z => z=CountedLoopHeaderClean.bank (counted v ctx p R 0))
      (fun z => z=CountedLoopHeaderClean.bank (counted v ctx p R R))
      (R*(24*w+89)+11*(RecursiveChildQuotientsConstant.bits R).length+35) := by
  have hb : ∀ i<R,HoareTime body (fun z => z=counted v ctx p R i)
      (fun z => z=counted v ctx p R (i+1)) (24*w+83) := by
    intro i hi
    exact hoare_extend_eq (UnitPhaseSharedCoefficient.runs (state v ctx p i) (ctx i) p w (hw i hi)
      (state_source v ctx p R hflags hcore hs hnext i hi)
      (state_flags v ctx p hflags i) (state_core v ctx p hcore i)) _
  have h := CountedLoopHeaderClean.runs body (60 : Fin 61) (RecursiveChildQuotientsConstant.bits R) R
    (counted v ctx p R) (fun _ => 24*w+83) ⟨rfl,rfl⟩ (RecursiveChildQuotientsConstant.bits_value _) hb
  apply h.consequence (fun _ h => h) (fun _ h => h) _
  simp only [CountedLoopHeaderClean.cost,Finset.sum_const,Finset.card_range,smul_eq_mul]
  nlinarith

end
end IntegerMultBounds.Machine.UnitPhasePolynomialLoop
