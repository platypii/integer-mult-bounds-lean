import IntegerMultBounds.Machine.BinaryVaryingParityOnlyGather
import IntegerMultBounds.Machine.BinaryVaryingOffsetGatherPlaced

/-! The pure-parity gather on six arbitrary caller ports. Its physical Boolean
transition uses only the target bit; controls are still scanned and retained. -/
namespace IntegerMultBounds.Machine.BinaryVaryingParityOnlyPlaced
noncomputable section
variable {t a : ℕ}

abbrev nativePorts := BinaryVaryingOffsetGatherPlaced.nativePorts
abbrev sourceWidth (q _b : ℕ) := q
abbrev after := @BinaryVaryingParityOnlyGather.after
abbrev installed := @BinaryVaryingOffsetGatherPlaced.installed
abbrev installed_frame := @BinaryVaryingOffsetGatherPlaced.installed_frame

def result (caller : Tapes t a) (focus : Fin 6 → Fin t)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) (px pz pt : ℤ) :=
  installed caller focus (after (SharedBank.payload caller focus) q b hb hbq xs zs px pz pt)
def program (focus : Fin 6 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (BinaryVaryingParityOnlyGather.program (a := a)) (CleanSubbank.placement nativePorts focus hf)
def input (caller : Tapes t a) := CleanSubbank.bank (s := 20) caller

theorem runs (caller : Tapes t a) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) (px pz pt : ℤ) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i : Fin 3, caller.tape (focus ⟨i.val,by omega⟩)=RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i : Fin 3, caller.head (focus ⟨i.val,by omega⟩)=1)
    (hxs : zs.length*sourceWidth q b≤xs.length)
    (hx : caller.tape (focus 3)=putWord (fun _ => blank) px (xs.map bitSymbol))
    (hz : caller.tape (focus 4)=putWord (fun _ => blank) pz (zs.map bitSymbol))
    (hp : caller.head (focus 3)=px) (hr : caller.head (focus 4)=pz) (ho : caller.head (focus 5)=pt) :
    HoareTime (program focus hf) (fun v => v=input caller)
      (fun v => v=input (result caller focus q b hb hbq xs zs px pz pt))
      (320*((zs.length+1)*(q+b+1))) := by
  let v := SharedBank.payload caller focus
  let w := after v q b hb hbq xs zs px pz pt
  apply CleanSubbank.realizes (BinaryVaryingParityOnlyGather.program (a := a)) nativePorts focus
    (Fin.castAdd_injective _ _) hf caller (result caller focus q b hb hbq xs zs px pz pt)
    (v.append (SharedBank.empty 14 a)) (w.append (SharedBank.empty 14 a)) _
  · exact BinaryVaryingOffsetGatherPlaced.native_payload v
  · rw [result,BinaryVaryingOffsetGatherPlaced.installed_payload caller focus hf]
    exact BinaryVaryingOffsetGatherPlaced.native_payload w
  · exact BinaryVaryingOffsetGatherPlaced.native_clean v
  · exact BinaryVaryingOffsetGatherPlaced.native_clean w
  · exact installed_frame caller focus w
  · have h := BinaryVaryingParityOnlyGather.runs v q b hb hbq xs zs px pz pt hs hv hc
      (by intro i; fin_cases i; exact ht 0; exact ht 1; exact ht 2)
      (by intro i; fin_cases i; exact hh 0; exact hh 1; exact hh 2) hxs hx hz hp hr ho
    simpa only [after,w,FixedHeaderBankCopy.empty,SharedBank.empty,BinaryVaryingParityOnlyGather.input_eq] using h

theorem result_payload (caller : Tapes t a) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) (px pz pt : ℤ) :
    SharedBank.payload (result caller focus q b hb hbq xs zs px pz pt) focus=
      after (SharedBank.payload caller focus) q b hb hbq xs zs px pz pt :=
  BinaryVaryingOffsetGatherPlaced.installed_payload caller focus hf _

end
end IntegerMultBounds.Machine.BinaryVaryingParityOnlyPlaced
