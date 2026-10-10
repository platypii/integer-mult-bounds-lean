import IntegerMultBounds.Machine.NativeUniformPolynomialRotationRoles
import IntegerMultBounds.Machine.NativeEndpointNamedPorts
import IntegerMultBounds.Machine.NativeEndpointCharacterLeafPlacement

/-! Actual named sink correction: runtime-column rotation visits every Y role,
fixed negation visits every X role. The first67 borrowed leaf tapes return
blank; all remaining leaf and scalar tapes and original descriptors are frame. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotationNamedRoles
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexScalarCountLifecycle (roleDivisor roleDivisor_eq)
open CompactComplexEndpointRoleExchange (Address Wire tapes port addresses)
open NativeEndpointNamedPorts (focus sourceX sinkY)
variable {s u r : ℕ} {sh : Shape}
attribute [local irreducible] roleCount roleDivisor NativeUniformPolynomialRotationRoles.program

private theorem serialized_transport {N M : ℕ} (h : N=M)
    (xs : Fin M → ButterflyStreamData.Coefficient) :
    UnitPhaseFullStreamNormalized.serialized (fun i : Fin N => xs (Fin.cast h i))=
      UnitPhaseFullStreamNormalized.serialized xs := by
  cases h
  rfl

private theorem serialized_result_transport {N M : ℕ} (h : N=M)
    (q : Fin 4) (xs : Fin M → ButterflyStreamData.Coefficient) :
    UnitPhaseFullStreamNormalized.serialized
        (UnitPhasePolynomialArray.result q (fun i : Fin N => xs (Fin.cast h i)))=
      UnitPhaseFullStreamNormalized.serialized (UnitPhasePolynomialArray.result q xs) := by
  cases h
  rfl

/-- The mode is compiled, while the phase is read from the actual columns header. -/
def source (negative : Bool) (b : Address) : Fin (tapes s u) :=
  if negative then sourceX b else sinkY b

theorem source_injective (negative : Bool) : Function.Injective (source (s:=s) (u:=u) negative) := by
  cases negative
  · exact NativeEndpointNamedPorts.sinkY_injective
  · exact NativeEndpointNamedPorts.sourceX_injective

theorem source_focus (negative : Bool) (b : Address) (i : Fin 15) :
    source (s:=s) (u:=u) negative b≠focus i := by
  cases negative
  · exact NativeEndpointNamedPorts.sinkY_focus b i
  · exact NativeEndpointNamedPorts.sourceX_focus b i

def program (negative : Bool) (hr : 67≤r) : Σ q,Program (tapes s u+r) q 2 :=
  ⟨_,NativeEndpointCharacterLeafPlacement.program hr
    (NativeUniformPolynomialRotationRoles.actualProgram negative focus (source negative)).2⟩
def rotation (hr : 67≤r) := program (s:=s) (u:=u) false hr
def negation (hr : 67≤r) := program (s:=s) (u:=u) true hr

def selected (negative : Bool) (b : Address) : Wire :=
  if negative then Sum.inl b else Sum.inr (Sum.inl b)

def output (negative : Bool) (v : Stage sh) (parentRows ell : ℕ)
    (data : Wire → Array sh (parentRows/roleCount) ell) (caller : Tapes (tapes s u) 2) :=
  NativeUniformPolynomialRotationRoles.output negative (source negative) v
    (fun b => fun i : Fin (((parentRows/roleDivisor)*2^sh.bits)*2^ell) =>
      data (selected negative b) (Fin.cast (by simp only [roleDivisor_eq,ButterflySpectatorGeometry.Size,Nat.mul_assoc]) i)) caller addresses

 theorem runs (negative : Bool) (hprivate : 67≤r) (v : Stage sh) (parentRows ell p : ℕ)
    (hr : 0<parentRows/roleCount) (hG : 0<sh.guard) (hA : 0<sh.axes)
    (hK : 0<sh.chunk) (hpay : sh.payload=1)
    (data : Wire → Array sh (parentRows/roleCount) ell)
    (hw : ∀ a i,(data a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (caller : Tapes (tapes s u) 2) (tail : Tapes r 2)
    (hb : ∀ i : Fin 67,tail.head ⟨i.val,lt_of_lt_of_le i.isLt hprivate⟩=0 ∧
      tail.tape ⟨i.val,lt_of_lt_of_le i.isLt hprivate⟩=(fun _ => blank))
    (hs : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words v parentRows ell p i))
    (hh : ∀ i,caller.head (focus i)=1)
    (hsource : ∀ a,caller.tape (port a)=putWord (fun _ => blank) 0
      (UnitPhaseFullStreamNormalized.serialized (data a)))
    (hhead : ∀ a,caller.head (port a)=0) :
    HoareTime (program negative hprivate).2
      (fun z => z=caller.append tail)
      (fun z => z=(output negative v parentRows ell data caller).append tail)
      (NativeUniformPolynomialRotationRoles.constant*
        CompactNativeRoleTransferBudget.volume parentRows sh ell p) := by
  have hr' : 0<parentRows/roleDivisor := by rwa [roleDivisor_eq]
  let xs := fun b => fun i : Fin (((parentRows/roleDivisor)*2^sh.bits)*2^ell) =>
    data (selected negative b) (Fin.cast (by simp only [roleDivisor_eq,ButterflySpectatorGeometry.Size,Nat.mul_assoc]) i)
  have h := NativeUniformPolynomialRotationRoles.runs negative focus (source negative)
    (source_injective negative) (source_focus negative) v parentRows ell p
    (CompactNativeRoleHeaders.recordWidth sh p) hr' hG hA hK xs
    (fun b i => hw (selected negative b) _) addresses
    CompactComplexEndpointRoleExchange.addresses_nodup caller hs hh
    (by
      intro b _
      have he : source (s:=s) (u:=u) negative b=port (selected negative b) := by cases negative <;> rfl
      rw [he]
      simpa only [xs,serialized_transport] using hsource (selected negative b))
    (by intro b _; cases negative <;> exact hhead _)
  have hbound := h.consequence (fun _ h => h) (fun _ h => h)
    (NativeUniformPolynomialRotationRoles.time_linear v parentRows ell p hr' hA hG hK hpay)
  exact NativeEndpointCharacterLeafPlacement.runs hprivate caller _ tail _ hb hbound

/-- The literal original caller supplies all role words and parent descriptors;
only the first67 leaf tapes are required blank. No phase/count word is given. -/
theorem runs_caller (negative : Bool) (hprivate : 67≤r) (v : Stage sh)
    (parentRows ell p : ℕ) (hr : 0<parentRows/roleCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hpay : sh.payload=1)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (headers : Tapes 22 2)
    (storage : Tapes s 2) (extra : Tapes u 2)
    (master : ℤ → Fin 6) (masterHead : ℤ)
    (data : Wire → Array sh (parentRows/roleCount) ell)
    (hw : ∀ a i,(data a i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data a i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (tail : Tapes r 2)
    (hb : ∀ i : Fin 67,tail.head ⟨i.val,lt_of_lt_of_le i.isLt hprivate⟩=0 ∧
      tail.tape ⟨i.val,lt_of_lt_of_le i.isLt hprivate⟩=(fun _ => blank)) :
    let caller := (CompactComplexNativeCodecFrame.bank control queue scalar
      (NativeEndpointCharacterPrepare.raw v parentRows ell p) headers storage
      (CompactComplexEndpointRoleExchange.payload master masterHead data)).append extra
    HoareTime (program negative hprivate).2
      (fun z => z=caller.append tail)
      (fun z => z=(output negative v parentRows ell data caller).append tail)
      (NativeUniformPolynomialRotationRoles.constant*
        CompactNativeRoleTransferBudget.volume parentRows sh ell p) := by
  dsimp only
  apply runs negative hprivate v parentRows ell p hr hG hA hK hpay data hw _ tail hb
  · intro i
    have h := (NativeEndpointNamedPorts.focus_bank control queue scalar
      (NativeEndpointCharacterPrepare.raw v parentRows ell p) headers storage
      (CompactComplexEndpointRoleExchange.payload master masterHead data) extra i).2
    exact h.trans (by fin_cases i <;> rfl)
  · intro i
    have h := (NativeEndpointNamedPorts.focus_bank control queue scalar
      (NativeEndpointCharacterPrepare.raw v parentRows ell p) headers storage
      (CompactComplexEndpointRoleExchange.payload master masterHead data) extra i).1
    exact h.trans (by fin_cases i <;> rfl)
  · intro a
    exact (CompactComplexEndpointRoleExchange.caller_roles control queue scalar
      (NativeEndpointCharacterPrepare.raw v parentRows ell p) headers storage extra
      master masterHead data a).2
  · intro a
    exact (CompactComplexEndpointRoleExchange.caller_roles control queue scalar
      (NativeEndpointCharacterPrepare.raw v parentRows ell p) headers storage extra
      master masterHead data a).1

 theorem output_frame (negative : Bool) (v : Stage sh) (parentRows ell : ℕ)
    (data : Wire → Array sh (parentRows/roleCount) ell) (caller : Tapes (tapes s u) 2)
    (i : Fin (tapes s u)) (hi : ∀ b,source negative b≠i) :
    (output negative v parentRows ell data caller).head i=caller.head i ∧
      (output negative v parentRows ell data caller).tape i=caller.tape i :=
  NativeUniformPolynomialRotationRoles.output_frame negative (source negative) v _ addresses caller i (fun b _ => hi b)

 theorem output_role (negative : Bool) (v : Stage sh) (parentRows ell : ℕ)
    (data : Wire → Array sh (parentRows/roleCount) ell) (caller : Tapes (tapes s u) 2) (b : Address) :
    (output negative v parentRows ell data caller).head (source negative b)=0 ∧
      (output negative v parentRows ell data caller).tape (source negative b)=
        putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized
          (UnitPhasePolynomialArray.result (NativeUniformPolynomialRotationOriginal.exponent negative v)
            (data (selected negative b)))) := by
  have h := NativeUniformPolynomialRotationRoles.output_role negative (source negative)
    (source_injective negative) v
    (fun b => fun i : Fin (((parentRows/roleDivisor)*2^sh.bits)*2^ell) =>
      data (selected negative b) (Fin.cast (by simp only [roleDivisor_eq,ButterflySpectatorGeometry.Size,Nat.mul_assoc]) i))
    addresses CompactComplexEndpointRoleExchange.addresses_nodup caller b
    (CompactComplexEndpointRoleExchange.addresses_complete b)
  simpa only [output,serialized_result_transport] using h

 theorem output_scratch (negative : Bool) (v : Stage sh) (parentRows ell : ℕ)
    (data : Wire → Array sh (parentRows/roleCount) ell) (caller : Tapes (tapes s u) 2)
    (a : Networks.Wires.Invocation 25 × (Networks.NeighborCounts.ComplexPairs 25 ⊕ Fin 26)) :
    (output negative v parentRows ell data caller).head (port (Sum.inr (Sum.inr a)))=
      caller.head (port (Sum.inr (Sum.inr a))) ∧
    (output negative v parentRows ell data caller).tape (port (Sum.inr (Sum.inr a)))=
      caller.tape (port (Sum.inr (Sum.inr a))) := by
  apply output_frame
  intro b he
  cases negative
  · have h := CompactComplexEndpointRoleExchange.port_injective he
    cases h
  · have h := CompactComplexEndpointRoleExchange.port_injective he
    cases h

end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotationNamedRoles
