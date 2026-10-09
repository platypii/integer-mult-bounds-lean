import IntegerMultBounds.Machine.BinaryVaryingSelectedOffsetGather
import IntegerMultBounds.Machine.BinaryVaryingControlOffsetGather
import IntegerMultBounds.Machine.BinaryVaryingParityOffsetGather
import IntegerMultBounds.Machine.CleanSubbank
import IntegerMultBounds.Machine.SharedBankFrames

/-! All three runtime varying-control gathers on six arbitrary caller ports.
The original headers and physical streams remain on caller tapes; each native
scratch tape is blank again and every complementary caller tape is framed. -/
namespace IntegerMultBounds.Machine.BinaryVaryingOffsetGatherPlaced
noncomputable section
variable {t a : ℕ}

inductive Kind where | selected | control | parity

def nativePorts : Fin 6 → Fin 20 := Fin.castAdd 14
def sourceWidth (k : Kind) (q b : ℕ) : ℕ := match k with
  | .selected => b | .control => 1 | .parity => q

def stateCount {s : ℕ} (_ : Program 20 s a) := s
def nativeStates (k : Kind) (a : ℕ) := match k with
  | .selected => stateCount (BinaryVaryingSelectedOffsetGather.program (a := a))
  | .control => stateCount (BinaryVaryingControlOffsetGather.program (a := a))
  | .parity => stateCount (BinaryVaryingParityOffsetGather.program (a := a))
def nativeProgram (k : Kind) (a : ℕ) : Program 20 (nativeStates k a) a := match k with
  | .selected => BinaryVaryingSelectedOffsetGather.program (a := a)
  | .control => BinaryVaryingControlOffsetGather.program (a := a)
  | .parity => BinaryVaryingParityOffsetGather.program (a := a)

def after (k : Kind) (v : Tapes 6 a) (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (xs zs : List Bool) (px pz pt : ℤ) : Tapes 6 a := match k with
  | .selected => BinaryVaryingSelectedOffsetGather.after v q b hb hbq xs zs px pz pt
  | .control => BinaryVaryingControlOffsetGather.after v q b hb hbq xs zs px pz pt
  | .parity => BinaryVaryingParityOffsetGather.after v q b hb hbq xs zs px pz pt

def installed (caller : Tapes t a) (focus : Fin 6 → Fin t) (v : Tapes 6 a) : Tapes t a :=
  ⟨fun i => if h : ∃ j, focus j=i then v.head h.choose else caller.head i,
   fun i => if h : ∃ j, focus j=i then v.tape h.choose else caller.tape i⟩

theorem installed_payload (caller : Tapes t a) (focus : Fin 6 → Fin t)
    (hf : Function.Injective focus) (v : Tapes 6 a) : SharedBank.payload (installed caller focus v) focus=v := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [installed]
  all_goals split_ifs with h
  all_goals first | rw [hf h.choose_spec] | exact (h ⟨i,rfl⟩).elim

theorem installed_frame (caller : Tapes t a) (focus : Fin 6 → Fin t) (v : Tapes 6 a) :
    SharedBank.strip caller focus=SharedBank.strip (installed caller focus v) focus := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [installed]
  all_goals split_ifs <;> rfl

def result (k : Kind) (caller : Tapes t a) (focus : Fin 6 → Fin t)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) (px pz pt : ℤ) :=
  installed caller focus (after k (SharedBank.payload caller focus) q b hb hbq xs zs px pz pt)
def program (k : Kind) (focus : Fin 6 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (nativeProgram k a) (CleanSubbank.placement nativePorts focus hf)
def input (caller : Tapes t a) := CleanSubbank.bank (s := 20) caller

theorem native_clean (v : Tapes 6 a) :
    SharedBank.strip (v.append (SharedBank.empty 14 a)) nativePorts=SharedBank.empty 20 a := by
  change SharedBank.strip (v.append (SharedBank.empty 14 a)) (fun i => Fin.castAdd 14 (id i))=SharedBank.empty 20 a
  rw [SharedBankFrames.strip_append_left (slots := id),SharedBankFrames.strip_identity,
    SharedBankFrames.empty_append]

theorem native_payload (v : Tapes 6 a) :
    SharedBank.payload (v.append (SharedBank.empty 14 a)) nativePorts=v := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [nativePorts,Tapes.append,Fin.addCases_left]

private theorem native_runs (k : Kind) (v : Tapes 6 a) (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q)
    (xs zs : List Bool) (px pz pt : ℤ) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i : Fin 3, v.tape ⟨i.val,by omega⟩=RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i : Fin 3, v.head ⟨i.val,by omega⟩=1)
    (hxs : zs.length*sourceWidth k q b≤xs.length)
    (hx : v.tape 3=putWord (fun _ => blank) px (xs.map bitSymbol))
    (hz : v.tape 4=putWord (fun _ => blank) pz (zs.map bitSymbol))
    (hp : v.head 3=px) (hr : v.head 4=pz) (ho : v.head 5=pt) :
    HoareTime (nativeProgram k a) (fun w => w=v.append (SharedBank.empty 14 a))
      (fun w => w=(after k v q b hb hbq xs zs px pz pt).append (SharedBank.empty 14 a))
      (320*((zs.length+1)*(q+b+1))) := by
  cases k
  · have h := BinaryVaryingSelectedOffsetGather.runs v q b hb hbq xs zs px pz pt hs hv hc
      (by intro i; fin_cases i; exact ht 0; exact ht 1; exact ht 2) (by intro i; fin_cases i; exact hh 0; exact hh 1; exact hh 2) hxs hx hz hp hr ho
    simpa only [nativeProgram,nativeStates,stateCount,after,FixedHeaderBankCopy.empty,SharedBank.empty,BinaryVaryingSelectedOffsetGather.input_eq] using h
  · have h := BinaryVaryingControlOffsetGather.runs v q b hb hbq xs zs px pz pt hs hv hc
      (by intro i; fin_cases i; exact ht 0; exact ht 1; exact ht 2) (by intro i; fin_cases i; exact hh 0; exact hh 1; exact hh 2)
      (by simpa only [sourceWidth,Nat.mul_one] using hxs) hx hz hp hr ho
    simpa only [nativeProgram,nativeStates,stateCount,after,FixedHeaderBankCopy.empty,SharedBank.empty,BinaryVaryingControlOffsetGather.input_eq] using h
  · have h := BinaryVaryingParityOffsetGather.runs v q b hb hbq xs zs px pz pt hs hv hc
      (by intro i; fin_cases i; exact ht 0; exact ht 1; exact ht 2) (by intro i; fin_cases i; exact hh 0; exact hh 1; exact hh 2) hxs hx hz hp hr ho
    simpa only [nativeProgram,nativeStates,stateCount,after,FixedHeaderBankCopy.empty,SharedBank.empty,BinaryVaryingParityOffsetGather.input_eq] using h

theorem runs (k : Kind) (caller : Tapes t a) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) (px pz pt : ℤ) (hs : Fin 3 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=CountedPackedShapeHeaders.originalValues q b zs.length i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (ht : ∀ i : Fin 3, caller.tape (focus ⟨i.val,by omega⟩)=RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i : Fin 3, caller.head (focus ⟨i.val,by omega⟩)=1)
    (hxs : zs.length*sourceWidth k q b≤xs.length)
    (hx : caller.tape (focus 3)=putWord (fun _ => blank) px (xs.map bitSymbol))
    (hz : caller.tape (focus 4)=putWord (fun _ => blank) pz (zs.map bitSymbol))
    (hp : caller.head (focus 3)=px) (hr : caller.head (focus 4)=pz) (ho : caller.head (focus 5)=pt) :
    HoareTime (program k focus hf) (fun v => v=input caller)
      (fun v => v=input (result k caller focus q b hb hbq xs zs px pz pt))
      (320*((zs.length+1)*(q+b+1))) := by
  let v := SharedBank.payload caller focus
  let w := after k v q b hb hbq xs zs px pz pt
  apply CleanSubbank.realizes (nativeProgram k a) nativePorts focus (Fin.castAdd_injective _ _) hf caller
    (result k caller focus q b hb hbq xs zs px pz pt) (v.append (SharedBank.empty 14 a))
    (w.append (SharedBank.empty 14 a)) _
  · exact native_payload v
  · rw [result,installed_payload caller focus hf]
    exact native_payload w
  · exact native_clean v
  · exact native_clean w
  · exact installed_frame caller focus w
  · exact native_runs k v q b hb hbq xs zs px pz pt hs hv hc ht hh hxs hx hz hp hr ho

theorem result_payload (k : Kind) (caller : Tapes t a) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) (px pz pt : ℤ) :
    SharedBank.payload (result k caller focus q b hb hbq xs zs px pz pt) focus=
      after k (SharedBank.payload caller focus) q b hb hbq xs zs px pz pt :=
  installed_payload caller focus hf _

theorem headers_retained (k : Kind) (caller : Tapes t a) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) (px pz pt : ℤ) (i : Fin 3) :
    (result k caller focus q b hb hbq xs zs px pz pt).head (focus ⟨i.val,by omega⟩)=
      caller.head (focus ⟨i.val,by omega⟩) ∧
    (result k caller focus q b hb hbq xs zs px pz pt).tape (focus ⟨i.val,by omega⟩)=
      caller.tape (focus ⟨i.val,by omega⟩) := by
  have h := result_payload k caller focus hf q b hb hbq xs zs px pz pt
  have hh := congrFun (congrArg Tapes.head h) (⟨i.val,by omega⟩ : Fin 6)
  have ht := congrFun (congrArg Tapes.tape h) (⟨i.val,by omega⟩ : Fin 6)
  change (result k caller focus q b hb hbq xs zs px pz pt).head (focus ⟨i.val,by omega⟩)=_ at hh
  change (result k caller focus q b hb hbq xs zs px pz pt).tape (focus ⟨i.val,by omega⟩)=_ at ht
  rw [hh,ht]
  cases k <;> fin_cases i <;> exact ⟨rfl,rfl⟩

theorem streams_retained (k : Kind) (caller : Tapes t a) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) (px pz pt : ℤ) :
    (result k caller focus q b hb hbq xs zs px pz pt).tape (focus 3)=caller.tape (focus 3) ∧
    (result k caller focus q b hb hbq xs zs px pz pt).tape (focus 4)=caller.tape (focus 4) := by
  have h := result_payload k caller focus hf q b hb hbq xs zs px pz pt
  have h3 := congrFun (congrArg Tapes.tape h) (3 : Fin 6)
  have h4 := congrFun (congrArg Tapes.tape h) (4 : Fin 6)
  change (result k caller focus q b hb hbq xs zs px pz pt).tape (focus 3)=_ at h3
  change (result k caller focus q b hb hbq xs zs px pz pt).tape (focus 4)=_ at h4
  rw [h3,h4]
  cases k <;> exact ⟨rfl,rfl⟩

theorem result_frame (k : Kind) (caller : Tapes t a) (focus : Fin 6 → Fin t)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) (px pz pt : ℤ)
    (i : Fin t) (hi : ¬∃ j, focus j=i) :
    (result k caller focus q b hb hbq xs zs px pz pt).head i=caller.head i ∧
    (result k caller focus q b hb hbq xs zs px pz pt).tape i=caller.tape i := by
  simp only [result,installed,hi,↓reduceDIte]
  exact ⟨trivial,trivial⟩

def outputWidth (k : Kind) (q b : ℕ) : ℕ := match k with
  | .selected => q | .control => q | .parity => b

theorem result_heads (k : Kind) (caller : Tapes t a) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (q b : ℕ) (hb : 1≤b) (hbq : b+1≤q) (xs zs : List Bool) (px pz pt : ℤ) :
    (result k caller focus q b hb hbq xs zs px pz pt).head (focus 3)=px+zs.length*sourceWidth k q b ∧
    (result k caller focus q b hb hbq xs zs px pz pt).head (focus 4)=pz+zs.length ∧
    (result k caller focus q b hb hbq xs zs px pz pt).head (focus 5)=pt+zs.length*outputWidth k q b := by
  have h := result_payload k caller focus hf q b hb hbq xs zs px pz pt
  have h3 := congrFun (congrArg Tapes.head h) (3 : Fin 6)
  have h4 := congrFun (congrArg Tapes.head h) (4 : Fin 6)
  have h5 := congrFun (congrArg Tapes.head h) (5 : Fin 6)
  change (result k caller focus q b hb hbq xs zs px pz pt).head (focus 3)=_ at h3
  change (result k caller focus q b hb hbq xs zs px pz pt).head (focus 4)=_ at h4
  change (result k caller focus q b hb hbq xs zs px pz pt).head (focus 5)=_ at h5
  rw [h3,h4,h5]
  cases k
  · exact ⟨rfl,rfl,rfl⟩
  · change px+zs.length=px+(zs.length : ℤ)*1 ∧ _ ∧ _
    simp only [mul_one]
    exact ⟨trivial,rfl,rfl⟩
  · exact ⟨rfl,rfl,rfl⟩

end
end IntegerMultBounds.Machine.BinaryVaryingOffsetGatherPlaced
