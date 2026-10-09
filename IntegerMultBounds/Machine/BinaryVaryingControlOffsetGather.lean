import IntegerMultBounds.Machine.CountedPackedShapeHeaders
import IntegerMultBounds.Machine.CountedGatherOriginalRun

/-! Physically place independently varying controls in stride-q output
words. Original q/b/count descriptors generate and erase every derived header
and clock; source and control tapes are retained. The source is scanned only
as a physical clocked field, without contributing to the output value. -/
namespace IntegerMultBounds.Machine.BinaryVaryingControlOffsetGather
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet (setTape)

def ports : Fin 3 → Fin 6 := ![0,1,2]
def focus : Fin 9 → Fin 14 := ![3,4,5,8,9,10,11,12,13]
theorem focus_injective : Function.Injective focus := by
  intro i j h; fin_cases i <;> fin_cases j <;> first | rfl | norm_num [focus] at h

def input (caller : Tapes 6 a) :=
  (CountedPackedShapeHeaders.input caller).append (FixedHeaderBankCopy.empty 6)
def ready (caller : Tapes 6 a) (hs : Fin 3 → List Bool) :=
  (CountedPackedShapeHeaders.output caller 2 hs).append (FixedHeaderBankCopy.empty 6)
def setup := extend (CountedPackedShapeHeaders.program (a := a) 2 ports) 6
def core := CountedGatherOriginalRun.program (a := a) (fun _ z => z) focus focus_injective
def cleanup := extend (CountedPackedShapeHeaders.cleanup (a := a) (t := 6)) 6
def program := seq (seq (setup (a := a)) core) cleanup

theorem input_eq (caller : Tapes 6 a) :
    input caller = caller.append (FixedHeaderBankCopy.empty 14) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def word (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) :=
  Gather.gather (fun _ z => z) (PackedArith.controlsAt q b hb hbq) xs zs zs.length

@[simp] theorem word_length (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) :
    (word q b hb hbq xs zs).length = zs.length*q :=
  Gather.gather_length _ _ _ _ _

def after (caller : Tapes 6 a) (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (xs zs : List Bool) (px pz pt : ℤ) :=
  setTape (setTape (setTape caller 3 (caller.tape 3) (px+zs.length))
    4 (caller.tape 4) (pz+zs.length))
    5 (putWord (caller.tape 5) pt ((word q b hb hbq xs zs).map bitSymbol)) (pt+zs.length*q)

theorem core_runs (caller : Tapes 6 a) (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (xs zs : List Bool) (px pz pt : ℤ) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (_ht : ∀ i, caller.tape (ports i)=RadixZeroFill.encodedBinary (hs i))
    (_hh : ∀ i, caller.head (ports i)=1)
    (hxs : zs.length≤xs.length)
    (hx : caller.tape 3=putWord (fun _ => blank) px (xs.map bitSymbol))
    (hz : caller.tape 4=putWord (fun _ => blank) pz (zs.map bitSymbol))
    (hp : caller.head 3=px) (hr : caller.head 4=pz) (ho : caller.head 5=pt) :
    HoareTime (core (a := a)) (fun v => v=ready caller hs)
      (fun v => v=ready (after caller q b hb hbq xs zs px pz pt) hs)
      (169*((zs.length+1)*(q+b+1))) := by
  let v := CountedPackedShapeHeaders.output caller 2 hs
  let hs6 := CountedPackedShapeHeaders.words 2 hs
  have hvals := CountedPackedShapeHeaders.words_values 2 q b zs.length hb hbq hs hv
  have hn := CountedGatherOriginalRun.runs v focus focus_injective (fun _ z => z)
    (PackedArith.controlsAt q b hb hbq) xs zs
    (fun _ => blank) (fun _ => blank) (caller.tape 5) px pz pt hs6
    hvals (CountedPackedShapeHeaders.words_canonical 2 hs hc)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
    hx hz rfl hp hr ho (by simpa only [PackedArith.controlsAt,Nat.mul_one] using hxs)
  have he : CountedGatherOriginalRun.result v focus
      (putWord (caller.tape 5) pt ((word q b hb hbq xs zs).map bitSymbol))
      (px+zs.length*1) (pz+zs.length) (pt+zs.length*q) =
      CountedPackedShapeHeaders.output (after caller q b hb hbq xs zs px pz pt) 2 hs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      first | rfl | (change px+(zs.length : ℤ)*1=px+zs.length; ring)
  change HoareTime _ _ (fun z => z=CountedGatherOriginalRun.input
    (CountedGatherOriginalRun.result v focus
      (putWord (caller.tape 5) pt ((word q b hb hbq xs zs).map bitSymbol))
      (px+zs.length*1) (pz+zs.length) (pt+zs.length*q))) _ at hn
  rw [he] at hn
  apply hn.consequence (fun _ h => h) (fun _ h => h) _
  have hcost := CountedGatherOriginalRun.cost_linear (PackedArith.controlsAt q b hb hbq)
    zs.length hs6 hvals (CountedPackedShapeHeaders.words_canonical 2 hs hc)
  have hbound : 169*((zs.length+1)*(1+q+1))≤169*((zs.length+1)*(q+b+1)) := by
    exact Nat.mul_le_mul_left 169 (Nat.mul_le_mul_left (zs.length+1) (by omega))
  exact hcost.trans hbound

/-- A single runtime-driven gather, with arbitrary source-address controls.
Every original header and all fourteen private tapes are restored. -/
theorem runs (caller : Tapes 6 a) (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (xs zs : List Bool) (px pz pt : ℤ) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i, caller.tape (ports i)=RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (ports i)=1)
    (hxs : zs.length≤xs.length)
    (hx : caller.tape 3=putWord (fun _ => blank) px (xs.map bitSymbol))
    (hz : caller.tape 4=putWord (fun _ => blank) pz (zs.map bitSymbol))
    (hp : caller.head 3=px) (hr : caller.head 4=pz) (ho : caller.head 5=pt) :
    HoareTime (program (a := a)) (fun v => v=input caller)
      (fun v => v=input (after caller q b hb hbq xs zs px pz pt))
      (320*((zs.length+1)*(q+b+1))) := by
  have h0 := hoare_extend_eq (CountedPackedShapeHeaders.constructs 2 ports caller
    q b zs.length hs hv hc ht hh) (FixedHeaderBankCopy.empty 6)
  have h1 := core_runs caller q b hb hbq xs zs px pz pt hs hv hc ht hh hxs hx hz hp hr ho
  have h2 := hoare_extend_eq (CountedPackedShapeHeaders.cleans 2
    (after caller q b hb hbq xs zs px pz pt) q b zs.length hs hv hc) (FixedHeaderBankCopy.empty 6)
  have hdim : q+b+zs.length+1≤(zs.length+1)*(q+b+1) := by nlinarith
  have hpos : 1≤(zs.length+1)*(q+b+1) := Nat.mul_pos (by omega) (by omega)
  exact ((h0.seq h1).seq h2).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.BinaryVaryingControlOffsetGather
