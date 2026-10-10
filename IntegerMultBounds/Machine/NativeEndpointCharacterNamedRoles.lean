import IntegerMultBounds.Machine.NativeEndpointCharacterLeafPlacement
import IntegerMultBounds.Machine.NativeEndpointNamedPorts

/-! Original named X/source and Y/sink sign families run on the actual retained
raw caller bank. Header readiness and original role words are derived from that
bank; execution releases all67 private tapes and retains every other caller tape. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterNamedRoles
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageHeadersData (Order)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexEndpointRoleExchange (Address Wire tapes port)
open NativeEndpointCharacterRoles (arity fixedWeights endpoints)
open NativeEndpointNamedPorts (focus sourceX sinkY)
variable {s u : ℕ} {sh : Shape}
attribute [local irreducible] NativeEndpointCharacterRoles.program NativeEndpointCharacterOriginal.cost

def role (sink : Bool) (b : Address) : Wire :=
  if sink then Sum.inr (Sum.inl b) else Sum.inl b

def source (sink : Bool) (b : Address) : Fin (tapes s u) := port (role sink b)

theorem source_injective (sink : Bool) : Function.Injective (source (s:=s) (u:=u) sink) := by
  cases sink
  · exact NativeEndpointNamedPorts.sourceX_injective
  · exact NativeEndpointNamedPorts.sinkY_injective

theorem source_focus (sink : Bool) (b : Address) (i : Fin 15) :
    source (s:=s) (u:=u) sink b≠focus i := NativeEndpointNamedPorts.role_focus _ _

def coefficients {rows ell : ℕ} (data : Wire → Array sh rows ell) (a : Wire) :
    Fin ((rows*2^sh.bits)*2^ell) → ButterflyStreamData.Coefficient :=
  fun i => data a (Fin.cast (Nat.mul_assoc rows (2^sh.bits) (2^ell)) i)

private theorem serialized_coefficients {rows ell : ℕ} (data : Wire → Array sh rows ell) (a : Wire) :
    UnitPhaseFullStreamNormalized.serialized (coefficients data a)=NativeZeroPaddingArray.word (data a) := by
  unfold UnitPhaseFullStreamNormalized.serialized NativeZeroPaddingArray.word coefficients
  congr 1
  exact (List.ofFn_congr (Nat.mul_assoc rows (2^sh.bits) (2^ell)).symm
    (fun i => ButterflyStreamData.encoded (data a i))).symm

def program (sink : Bool) (order : Order) := NativeEndpointCharacterRoles.actualProgram
  (focus (s:=s) (u:=u)) (source sink) order

def output (sink : Bool) (v : Stage sh) (ell p : ℕ)
    {rows : ℕ} (data : Wire → Array sh rows ell) (caller : Tapes (tapes s u) 2) :=
  NativeEndpointCharacterRoles.output (source sink) v ell p arity fixedWeights
    (fun b => coefficients data (role sink b)) caller endpoints

theorem fixedWeights_eq (v : Stage sh) (hslots : v.slots=arity) (b : Address) :
    fixedWeights b=NativeEndpointCharacterTerminal.terminalWeights v hslots b := by
  unfold fixedWeights NativeEndpointCharacterTerminal.terminalWeights NativeEndpointCharacterReadout.weights
    NativeEndpointCharacterTerminal.vector
  rw [List.ofFn_congr hslots.symm]
  apply List.ofFn_inj.mpr
  funext i
  congr 2
  apply Fin.ext
  simp only [finCongr_apply,Fin.val_cast,
    ActivePrefixStageRuntimeOrdinal.reverseAxis,NativeEndpointCharacterAddress.reverseSlot]
  have hv : v.slots=25^3 := hslots
  exact congrArg (fun n => n-i.val-1) hv.symm

/-- A real original raw caller, with arbitrary controller and external frame. -/
theorem runs (sink : Bool) (order : Order) (v : Stage sh) (parentRows ell p : ℕ)
    (hslots : v.slots=arity) (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order v)
    (hr : 0<parentRows/CompactComplexScalarCountLifecycle.roleDivisor)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (extra : Tapes u 2) (master : ℤ → Fin 6) (masterHead : ℤ)
    (data : Wire → Array sh (parentRows/CompactComplexScalarCountLifecycle.roleDivisor) ell)
    (hw : ∀ a i,(data a i).1.length=NativePolynomialStageShape.width sh p ∧
      (data a i).2.length=NativePolynomialStageShape.width sh p) :
    let caller := (CompactComplexNativeCodecFrame.bank control queue scalar
      (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
      (CompactComplexEndpointRoleExchange.payload master masterHead data)).append extra
    HoareTime (program (s:=s) (u:=u) sink order).2
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(output sink v ell p data caller).append (FixedHeaderBankCopy.empty 67))
      (endpoints.length*(NativeEndpointCharacterOriginal.cost (t:=tapes s u)
        CompactComplexScalarCountLifecycle.roleDivisor order v parentRows ell p+1)) := by
  dsimp only
  apply NativeEndpointCharacterRoles.runs focus (source sink) (source_injective sink) (source_focus sink)
    CompactComplexScalarCountLifecycle.roleDivisor (by rw [CompactComplexScalarCountLifecycle.roleDivisor_eq]; norm_num [CompactComplexRolePhaseSite.roleCount])
    order v parentRows ell p arity fixedWeights NativeEndpointCharacterRoles.weights_length hslots
    hG hA hK ho hr (fun b => coefficients data (role sink b)) (fun b i => hw (role sink b) (Fin.cast (Nat.mul_assoc _ _ _) i)) endpoints
    NativeEndpointCharacterRoles.endpoints_nodup
  · intro i
    have h := (NativeEndpointNamedPorts.focus_bank control queue scalar
      (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
      (CompactComplexEndpointRoleExchange.payload master masterHead data) extra i).2
    exact h.trans (by
      fin_cases i <;> rfl)
  · intro i
    have h := (NativeEndpointNamedPorts.focus_bank control queue scalar
      (CompactComplexNativeCodec.raw v parentRows ell p) tail storage
      (CompactComplexEndpointRoleExchange.payload master masterHead data) extra i).1
    exact h.trans (by
      fin_cases i <;> rfl)
  · intro b _
    simpa only [serialized_coefficients,NativeZeroPadding.word,source] using
      (CompactComplexEndpointRoleExchange.caller_roles control queue scalar
        (CompactComplexNativeCodec.raw v parentRows ell p) tail storage extra master masterHead data
        (role sink b)).2
  · intro b _
    exact (CompactComplexEndpointRoleExchange.caller_roles control queue scalar
      (CompactComplexNativeCodec.raw v parentRows ell p) tail storage extra master masterHead data
      (role sink b)).1

/-- Exact literal selected-role result, with its original terminal-vector weights. -/
theorem endpoint_role (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell p : ℕ)
    {rows : ℕ} (data : Wire → Array sh rows ell) (caller : Tapes (tapes s u) 2) (b : Address) :
    (output sink v ell p data caller).head (source sink b)=0 ∧
    (output sink v ell p data caller).tape (source sink b)=putWord (fun _ => blank) 0
      (UnitPhaseFullStreamNormalized.serialized
        (AllAxisPolynomialLiteralEndpoint.result (N:=rows*2^sh.bits) (R:=2^ell)
          (NativePolynomialStageShape.stage v ell p) arity
          (NativeEndpointCharacterTerminal.terminalWeights v hslots b) (coefficients data (role sink b)))) := by
  have h := NativeEndpointCharacterRoles.output_role (source sink) (source_injective sink)
    v ell p arity fixedWeights (fun b => coefficients data (role sink b)) endpoints
    NativeEndpointCharacterRoles.endpoints_nodup caller b (NativeEndpointCharacterRoles.endpoints_complete b)
  rw [fixedWeights_eq v hslots b] at h
  exact h

/-- Every caller tape outside this family retains its full word and head. -/
theorem endpoint_frame (sink : Bool) (v : Stage sh) (ell p : ℕ)
    {rows : ℕ} (data : Wire → Array sh rows ell) (caller : Tapes (tapes s u) 2)
    (i : Fin (tapes s u)) (hi : ∀ b,source sink b≠i) :
    (output sink v ell p data caller).head i=caller.head i ∧
    (output sink v ell p data caller).tape i=caller.tape i :=
  NativeEndpointCharacterRoles.output_frame (source sink) v ell p arity fixedWeights
    (fun b => coefficients data (role sink b)) endpoints caller i (fun b _ => hi b)

/-- The whole original named family, including every private lifecycle and join,
is paid by original parent native volume. -/
theorem time_linear (order : Order) (v : Stage sh) (parentRows ell p : ℕ)
    (hr : 0<parentRows/CompactComplexScalarCountLifecycle.roleDivisor)
    (hA : 0<sh.axes) (hG : 0<sh.guard) (hGK : sh.guard+1≤sh.chunk)
    (hpay : sh.payload=1) (ho : ActivePrefixStageHeadersSchedule.Ordered order v) :
    endpoints.length*(NativeEndpointCharacterOriginal.cost (t:=tapes s u)
      CompactComplexScalarCountLifecycle.roleDivisor order v parentRows ell p+1)≤
      NativeEndpointCharacterRoles.constant CompactComplexScalarCountLifecycle.roleDivisor*
        CompactNativeRoleTransferBudget.volume parentRows sh ell p :=
  NativeEndpointCharacterRoles.time_linear _ _ _ _ _ _ hr hA hG hGK hpay ho

/-- The fixed named family can borrow only the first67 tapes of a larger leaf
bank, retaining every remaining leaf tape and scalar workspace word. -/
def leafProgram (r : ℕ) (hr : 67≤r) (sink : Bool) (order : Order) :
    Σ q,Program (tapes s u+r) q 2 :=
  ⟨(program (s:=s) (u:=u) sink order).1,
    NativeEndpointCharacterLeafPlacement.program hr (program (s:=s) (u:=u) sink order).2⟩


end
end IntegerMultBounds.Machine.NativeEndpointCharacterNamedRoles
