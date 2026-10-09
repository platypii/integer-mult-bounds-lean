import IntegerMultBounds.Machine.ActivePrefixOffsetHeadersData

/-! One power and four actual dimension products synthesize all original
active-prefix offset descriptors in one reusable fifteen-tape workspace. -/
namespace IntegerMultBounds.Machine.ActivePrefixOffsetHeadersRun
noncomputable section
open ActivePrefixOffsetHeadersData
open CompactGadgetReservationHeadersCore (bank)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {t a : ℕ}

def powerPorts : Fin 2 → Fin 10 := ![0,5]
def sourcePorts : Fin 3 → Fin 10 := ![1,4,6]
def tempPorts : Fin 3 → Fin 10 := ![2,3,7]
def digitPorts : Fin 3 → Fin 10 := ![5,3,8]
def targetPorts : Fin 3 → Fin 10 := ![1,3,9]

def program (focus : Fin 10 → Fin t) (hf : Function.Injective focus) := seq (seq (seq (seq
  (CompactGadgetReservationHeadersPowerRound.powerProgram (a := a) (focus ∘ powerPorts) (hf.comp (by decide)))
  (CompactGadgetReservationHeadersCore.productProgram (focus ∘ sourcePorts) (hf.comp (by decide))))
  (CompactGadgetReservationHeadersCore.productProgram (focus ∘ tempPorts) (hf.comp (by decide))))
  (CompactGadgetReservationHeadersCore.productProgram (focus ∘ digitPorts) (hf.comp (by decide))))
  (CompactGadgetReservationHeadersCore.productProgram (focus ∘ targetPorts) (hf.comp (by decide)))

def cost (W q b n f : ℕ) := FixedBasePowerDescriptor.constant 2*2^W+1+(53*(f*q)+28)+1+
  (53*(n*b)+28)+1+(53*(n*2^W)+28)+1+(53*(n*q)+28)

theorem constructs (caller : Tapes t a) (focus : Fin 10 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 5 → List Bool) (W q b n f : ℕ)
    (hsrc : SharedBank.payload caller focus=sources hs)
    (hv : ∀ i, Counter.value (hs i)=originalValues W q b n f i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hq : 0<q) (hb : 0<b) :
    HoareTime (program (a := a) focus hf) (fun v => v=bank caller)
      (fun v => v=bank (result caller focus W q b n f)) (cost W q b n f) := by
  have ht (i : Fin 10) : caller.tape (focus i)=(sources (a := a) hs).tape i :=
    congrFun (congrArg Tapes.tape hsrc) i
  have hh (i : Fin 10) : caller.head (focus i)=(sources (a := a) hs).head i :=
    congrFun (congrArg Tapes.head hsrc) i
  have h0 := CompactGadgetReservationHeadersPowerRound.power caller (focus ∘ powerPorts) (hf.comp (by decide))
    (hs 0) W (hv 0) (hc 0)
    (by simp [powerPorts,ht,sources]) (by simp [powerPorts,hh,sources])
    (by simp [powerPorts,ht,sources]) (by simp [powerPorts,hh,sources])
  have h1 := CompactGadgetReservationHeadersCore.product (power caller focus W)
    (focus ∘ sourcePorts) (hf.comp (by decide)) (hs 1) (hs 4) f q hq (hv 1) (hv 4) (hc 1) (hc 4)
    (by simp [sourcePorts,power,install,setTape,hf.eq_iff,ht,sources])
    (by simp [sourcePorts,power,install,setTape,hf.eq_iff,hh,sources])
    (by simp [sourcePorts,power,install,setTape,hf.eq_iff,ht,sources])
    (by simp [sourcePorts,power,install,setTape,hf.eq_iff,hh,sources])
    (by simp [sourcePorts,power,install,setTape,hf.eq_iff,ht,sources])
    (by simp [sourcePorts,power,install,setTape,hf.eq_iff,hh,sources])
  have h2 := CompactGadgetReservationHeadersCore.product (sourceWidth caller focus W q f)
    (focus ∘ tempPorts) (hf.comp (by decide)) (hs 2) (hs 3) n b hb (hv 2) (hv 3) (hc 2) (hc 3)
    (by simp [tempPorts,sourceWidth,power,install,setTape,hf.eq_iff,ht,sources])
    (by simp [tempPorts,sourceWidth,power,install,setTape,hf.eq_iff,hh,sources])
    (by simp [tempPorts,sourceWidth,power,install,setTape,hf.eq_iff,ht,sources])
    (by simp [tempPorts,sourceWidth,power,install,setTape,hf.eq_iff,hh,sources])
    (by simp [tempPorts,sourceWidth,power,install,setTape,hf.eq_iff,ht,sources])
    (by simp [tempPorts,sourceWidth,power,install,setTape,hf.eq_iff,hh,sources])
  have h3 := CompactGadgetReservationHeadersCore.product (tempWidth caller focus W q b n f)
    (focus ∘ digitPorts) (hf.comp (by decide)) (bits (2^W)) (hs 3) n (2^W) (by positivity)
    (RecursiveChildQuotientsConstant.bits_value _) (hv 3) (RecursiveChildQuotientsConstant.bits_canonical _) (hc 3)
    (by simp [digitPorts,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff])
    (by simp [digitPorts,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff])
    (by simp [digitPorts,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff,ht,sources])
    (by simp [digitPorts,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff,hh,sources])
    (by simp [digitPorts,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff,ht,sources])
    (by simp [digitPorts,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff,hh,sources])
  have h4 := CompactGadgetReservationHeadersCore.product (digitCount caller focus W q b n f)
    (focus ∘ targetPorts) (hf.comp (by decide)) (hs 1) (hs 3) n q hq (hv 1) (hv 3) (hc 1) (hc 3)
    (by simp [targetPorts,digitCount,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff,ht,sources])
    (by simp [targetPorts,digitCount,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff,hh,sources])
    (by simp [targetPorts,digitCount,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff,ht,sources])
    (by simp [targetPorts,digitCount,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff,hh,sources])
    (by simp [targetPorts,digitCount,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff,ht,sources])
    (by simp [targetPorts,digitCount,tempWidth,sourceWidth,power,install,setTape,hf.eq_iff,hh,sources])
  exact (((h0.seq h1).seq h2).seq h3).seq h4

end
end IntegerMultBounds.Machine.ActivePrefixOffsetHeadersRun
