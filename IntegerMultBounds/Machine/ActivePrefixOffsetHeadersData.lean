import IntegerMultBounds.Machine.CompactGadgetReservationHeadersPowerRound

/-! Original descriptor order is W/q/b/n/f. Derived output order is
P=2^W, f*q, n*b, n*P, n*q; every derived port initially is blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixOffsetHeadersData
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t a : ℕ}

def originalValues (W q b n f : ℕ) : Fin 5 → ℕ := ![W,q,b,n,f]
def values (W q b n f : ℕ) : Fin 5 → ℕ := ![2^W,f*q,n*b,n*2^W,n*q]
def words (W q b n f : ℕ) : Fin 5 → List Bool := fun i => bits (values W q b n f i)
def sources (hs : Fin 5 → List Bool) : Tapes 10 a :=
  ⟨fun i => if i.val<5 then 1 else 0,
    fun i => if h : i.val<5 then RadixZeroFill.encodedBinary (hs ⟨i.val,h⟩) else fun _ => blank⟩

def install (caller : Tapes t a) (focus : Fin 10 → Fin t) (i : Fin 10) (N : ℕ) :=
  setTape caller (focus i) (RadixZeroFill.encodedBinary (bits N)) 1

def power (caller : Tapes t a) (focus : Fin 10 → Fin t) (W : ℕ) := install caller focus 5 (2^W)
def sourceWidth (caller : Tapes t a) (focus : Fin 10 → Fin t) (W q f : ℕ) := install (power caller focus W) focus 6 (f*q)
def tempWidth (caller : Tapes t a) (focus : Fin 10 → Fin t) (W q b n f : ℕ) :=
  install (sourceWidth caller focus W q f) focus 7 (n*b)
def digitCount (caller : Tapes t a) (focus : Fin 10 → Fin t) (W q b n f : ℕ) :=
  install (tempWidth caller focus W q b n f) focus 8 (n*2^W)
def result (caller : Tapes t a) (focus : Fin 10 → Fin t) (W q b n f : ℕ) :=
  install (digitCount caller focus W q b n f) focus 9 (n*q)

def originalFocus (focus : Fin 10 → Fin t) : Fin 5 → Fin t := fun i => focus (Fin.castAdd 5 i)
def outputFocus (focus : Fin 10 → Fin t) : Fin 5 → Fin t := fun i => focus (Fin.natAdd 5 i)

theorem output_injective (focus : Fin 10 → Fin t) (hf : Function.Injective focus) :
    Function.Injective (outputFocus focus) := hf.comp (Fin.natAdd_injective _ _)

theorem source_tapes (caller : Tapes t a) (focus : Fin 10 → Fin t) (hs : Fin 5 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources hs) :
    ∀ i, caller.tape (originalFocus focus i)=RadixZeroFill.encodedBinary (hs i) := by
  intro i
  have h := congrFun (congrArg Tapes.tape hsrc) (Fin.castAdd 5 i)
  simpa [SharedBank.payload,sources,originalFocus,i.isLt] using h

theorem source_heads (caller : Tapes t a) (focus : Fin 10 → Fin t) (hs : Fin 5 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources hs) : ∀ i, caller.head (originalFocus focus i)=1 := by
  intro i
  have h := congrFun (congrArg Tapes.head hsrc) (Fin.castAdd 5 i)
  simpa [SharedBank.payload,sources,originalFocus,i.isLt] using h

theorem blank_tapes (caller : Tapes t a) (focus : Fin 10 → Fin t) (hs : Fin 5 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources hs) : ∀ i, caller.tape (outputFocus focus i)=fun _ => blank := by
  intro i
  have h := congrFun (congrArg Tapes.tape hsrc) (Fin.natAdd 5 i)
  simpa [SharedBank.payload,sources,outputFocus] using h

theorem blank_heads (caller : Tapes t a) (focus : Fin 10 → Fin t) (hs : Fin 5 → List Bool)
    (hsrc : SharedBank.payload caller focus=sources hs) : ∀ i, caller.head (outputFocus focus i)=0 := by
  intro i
  have h := congrFun (congrArg Tapes.head hsrc) (Fin.natAdd 5 i)
  simpa [SharedBank.payload,sources,outputFocus] using h

theorem result_headers (caller : Tapes t a) (focus : Fin 10 → Fin t) (hf : Function.Injective focus)
    (W q b n f : ℕ) :
    (∀ i, (result caller focus W q b n f).tape (outputFocus focus i)=RadixZeroFill.encodedBinary (words W q b n f i)) ∧
    (∀ i, (result caller focus W q b n f).head (outputFocus focus i)=1) := by
  constructor <;> intro i <;> fin_cases i
  all_goals simp [result,digitCount,tempWidth,sourceWidth,power,install,setTape,outputFocus,words,values,hf.eq_iff]

theorem words_values (W q b n f : ℕ) : ∀ i, Counter.value (words W q b n f i)=values W q b n f i :=
  fun _ => RecursiveChildQuotientsConstant.bits_value _
theorem words_canonical (W q b n f : ℕ) : ∀ i, GrowingCounterData.Canonical (words W q b n f i) :=
  fun _ => RecursiveChildQuotientsConstant.bits_canonical _


theorem frame (caller : Tapes t a) (focus : Fin 10 → Fin t) (W q b n f : ℕ)
    (i : Fin t) (hi : ∀ j, i≠outputFocus focus j) :
    (result caller focus W q b n f).tape i=caller.tape i ∧
      (result caller focus W q b n f).head i=caller.head i := by
  have h5 : i≠focus 5 := hi 0
  have h6 : i≠focus 6 := hi 1
  have h7 : i≠focus 7 := hi 2
  have h8 : i≠focus 8 := hi 3
  have h9 : i≠focus 9 := hi 4
  simp [result,digitCount,tempWidth,sourceWidth,power,install,setTape,h5,h6,h7,h8,h9]

end
end IntegerMultBounds.Machine.ActivePrefixOffsetHeadersData
