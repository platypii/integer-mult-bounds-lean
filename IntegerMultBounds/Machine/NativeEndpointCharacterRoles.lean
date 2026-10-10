import IntegerMultBounds.Machine.NativeEndpointCharacterOriginalBudget
import IntegerMultBounds.Machine.NativeEndpointCharacterTerminal
import IntegerMultBounds.Machine.CompactComplexScalarCountLifecycle

/-! Fixed finite role traversal for actual source/sink endpoint characters.
Each physical role is visited once, all original descriptors and complementary
roles remain framed, and each iteration releases the entire private67 bank. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterRoles
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ActivePrefixStageHeadersData (Order)
open ButterflyStreamData (Coefficient)
open Networks
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {t : ℕ}
attribute [local irreducible] NativeEndpointCharacterOriginal.program NativeEndpointCharacterOriginal.cost

abbrev Endpoint := Wires.Address 25
abbrev arity := 25^3

@[irreducible] def fixedWeights (b : Endpoint) : List (ZMod 4) :=
  List.ofFn (fun i : Fin arity => BinaryPhase.doubleLift
    (ComplexEndpoints.terminalVector b (ActivePrefixStageRuntimeOrdinal.reverseAxis i)))

theorem weights_length (b : Endpoint) : (fixedWeights b).length=arity := by
  unfold fixedWeights
  exact List.length_ofFn

private opaque enumeration : {bs : List Endpoint // bs.Nodup ∧ ∀ b,b∈bs} :=
  ⟨Finset.univ.toList,Finset.nodup_toList _,by simp⟩
@[irreducible] def endpoints : List Endpoint := enumeration.val

theorem endpoints_nodup : endpoints.Nodup := by
  unfold endpoints
  exact enumeration.property.1
theorem endpoints_complete (b : Endpoint) : b∈endpoints := by
  unfold endpoints
  exact enumeration.property.2 b

def one (focus : Fin 15 → Fin t) (src : Endpoint → Fin t) (c : ℕ)
    (order : Order) (m : ℕ) (ws : Endpoint → List (ZMod 4)) (b : Endpoint) :=
  NativeEndpointCharacterOriginal.program focus (src b) c order m (ws b)

def program (focus : Fin 15 → Fin t) (src : Endpoint → Fin t) (c : ℕ) (order : Order) (m : ℕ) (ws : Endpoint → List (ZMod 4)) :
    List Endpoint → Σ q,Program (t+67) q 2
  | [] => ⟨1,skip (t+67) 2 (by omega)⟩
  | b::bs => ⟨_,seq (one focus src c order m ws b) (program focus src c order m ws bs).2⟩

def actualProgram (focus : Fin 15 → Fin t) (src : Endpoint → Fin t) (order : Order) :=
  program focus src CompactComplexScalarCountLifecycle.roleDivisor order arity fixedWeights endpoints

def result (src : Endpoint → Fin t) (v : Stage s) (ell p m : ℕ) (ws : Endpoint → List (ZMod 4)) {rows : ℕ}
    (xs : Endpoint → Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (caller : Tapes t 2) (b : Endpoint) :=
  NativeEndpointCharacterLifecycle.resultCaller caller (src b)
    (NativePolynomialStageShape.stage v ell p) m (ws b) (xs b)

def output (src : Endpoint → Fin t) (v : Stage s) (ell p m : ℕ) (ws : Endpoint → List (ZMod 4)) {rows : ℕ}
    (xs : Endpoint → Fin ((rows*2^s.bits)*2^ell) → Coefficient) :
    Tapes t 2 → List Endpoint → Tapes t 2
  | caller,[] => caller
  | caller,b::bs => output src v ell p m ws xs (result src v ell p m ws xs caller b) bs

private theorem one_runs (focus : Fin 15 → Fin t) (src : Endpoint → Fin t)
    (c : ℕ) (hc : 0<c) (order : Order) (v : Stage s) (parentRows ell p : ℕ)
    (m : ℕ) (hslots : v.slots=m) (ws : Endpoint → List (ZMod 4)) (b : Endpoint)
    (hlen : (ws b).length=m) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order v) (hr : 0<parentRows/c)
    (xs : Endpoint → Fin (((parentRows/c)*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs b i).1.length=NativePolynomialStageShape.width s p ∧
      (xs b i).2.length=NativePolynomialStageShape.width s p) (caller : Tapes t 2)
    (hs : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words v parentRows ell p i))
    (hh : ∀ i,caller.head (focus i)=1)
    (hsource : caller.tape (src b)=putWord (fun _ => blank) 0
      (UnitPhaseFullStreamNormalized.serialized (xs b))) (hhead : caller.head (src b)=0) :
    HoareTime (one focus src c order m ws b)
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(result src v ell p m ws xs caller b).append (FixedHeaderBankCopy.empty 67))
      (NativeEndpointCharacterOriginal.cost (t:=t) c order v parentRows ell p) := by
  subst m
  exact NativeEndpointCharacterOriginal.runs focus (src b) caller c hc order v parentRows ell p
    hG hA hK ho hr (ws b) hlen.symm (xs b) hw hs hh hsource hhead

theorem runs (focus : Fin 15 → Fin t) (src : Endpoint → Fin t)
    (hinj : Function.Injective src) (houtside : ∀ b i,src b≠focus i)
    (c : ℕ) (hc : 0<c) (order : Order) (v : Stage s) (parentRows ell p : ℕ)
    (m : ℕ) (ws : Endpoint → List (ZMod 4)) (hlen : ∀ b,(ws b).length=m)
    (hslots : v.slots=m) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order v) (hr : 0<parentRows/c)
    (xs : Endpoint → Fin (((parentRows/c)*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ b i,(xs b i).1.length=NativePolynomialStageShape.width s p ∧
      (xs b i).2.length=NativePolynomialStageShape.width s p)
    (bs : List Endpoint) (hn : bs.Nodup) (caller : Tapes t 2)
    (hs : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words v parentRows ell p i))
    (hh : ∀ i,caller.head (focus i)=1)
    (hsource : ∀ b∈bs,caller.tape (src b)=putWord (fun _ => blank) 0
      (UnitPhaseFullStreamNormalized.serialized (xs b)))
    (hhead : ∀ b∈bs,caller.head (src b)=0) :
    HoareTime (program focus src c order m ws bs).2
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(output src v ell p m ws xs caller bs).append (FixedHeaderBankCopy.empty 67))
      (bs.length*(NativeEndpointCharacterOriginal.cost (t:=t) c order v parentRows ell p+1)) := by
  induction bs generalizing caller with
  | nil =>
    simp only [program,output,List.length_nil,zero_mul]
    exact skip_hoare (by omega) _
  | cons b bs ih =>
    have hnodup := List.nodup_cons.mp hn
    have h0 := one_runs focus src c hc order v parentRows ell p m hslots ws b (hlen b)
      hG hA hK ho hr xs (hw b) caller hs hh (hsource b List.mem_cons_self) (hhead b List.mem_cons_self)
    have h1 := ih hnodup.2 (result src v ell p m ws xs caller b)
      (by intro i; simpa only [result,NativeEndpointCharacterLifecycle.resultCaller,setTape,
        Function.update_of_ne (houtside b i).symm] using hs i)
      (by intro i; simpa only [result,NativeEndpointCharacterLifecycle.resultCaller,setTape,
        Function.update_of_ne (houtside b i).symm] using hh i)
      (by
        intro a ha
        have hne : src a≠src b := fun h => hnodup.1 ((hinj h).symm ▸ ha)
        simpa only [result,NativeEndpointCharacterLifecycle.resultCaller,setTape,
          Function.update_of_ne hne] using hsource a (List.mem_cons_of_mem _ ha))
      (by
        intro a ha
        have hne : src a≠src b := fun h => hnodup.1 ((hinj h).symm ▸ ha)
        simpa only [result,NativeEndpointCharacterLifecycle.resultCaller,setTape,
          Function.update_of_ne hne] using hhead a (List.mem_cons_of_mem _ ha))
    exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by simp only [List.length_cons]; nlinarith)

theorem output_frame (src : Endpoint → Fin t) (v : Stage s) (ell p m : ℕ)
    (ws : Endpoint → List (ZMod 4)) {rows : ℕ}
    (xs : Endpoint → Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (bs : List Endpoint) (caller : Tapes t 2) (i : Fin t)
    (hi : ∀ b∈bs,src b≠i) :
    (output src v ell p m ws xs caller bs).head i=caller.head i ∧
    (output src v ell p m ws xs caller bs).tape i=caller.tape i := by
  induction bs generalizing caller with
  | nil => exact ⟨rfl,rfl⟩
  | cons b bs ih =>
    have h := ih (result src v ell p m ws xs caller b) (fun a ha => hi a (List.mem_cons_of_mem _ ha))
    simpa only [output,result,NativeEndpointCharacterLifecycle.resultCaller,setTape,
      Function.update_of_ne (hi b List.mem_cons_self).symm] using h

theorem output_role (src : Endpoint → Fin t) (hinj : Function.Injective src)
    (v : Stage s) (ell p m : ℕ) (ws : Endpoint → List (ZMod 4)) {rows : ℕ}
    (xs : Endpoint → Fin ((rows*2^s.bits)*2^ell) → Coefficient)
    (bs : List Endpoint) (hn : bs.Nodup) (caller : Tapes t 2) (b : Endpoint) (hb : b∈bs) :
    (output src v ell p m ws xs caller bs).head (src b)=0 ∧
    (output src v ell p m ws xs caller bs).tape (src b)=
      putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized
        (AllAxisPolynomialLiteralEndpoint.result (N:=rows*2^s.bits) (R:=2^ell)
          (NativePolynomialStageShape.stage v ell p) m (ws b) (xs b))) := by
  induction bs generalizing caller with
  | nil => exact (List.not_mem_nil hb).elim
  | cons a bs ih =>
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hb with rfl | hb
    · have h := output_frame src v ell p m ws xs bs (result src v ell p m ws xs caller b) (src b)
        (by intro a ha; exact fun he => hn'.1 (hinj he ▸ ha))
      constructor
      · exact h.1.trans (by simp only [result,NativeEndpointCharacterLifecycle.resultCaller,setTape,Function.update_self])
      · exact h.2.trans (by simp only [result,NativeEndpointCharacterLifecycle.resultCaller,setTape,Function.update_self]; rfl)
    · exact ih hn'.2 (result src v ell p m ws xs caller a) hb

def constant (c : ℕ) := endpoints.length*(NativeEndpointCharacterOriginalBudget.constant c+1)

theorem time_linear (c : ℕ) (order : Order) (v : Stage s) (parentRows ell p : ℕ)
    (hr : 0<parentRows/c) (hA : 0<s.axes) (hG : 0<s.guard)
    (hGK : s.guard+1≤s.chunk) (hpay : s.payload=1)
    (ho : ActivePrefixStageHeadersSchedule.Ordered order v) :
    endpoints.length*(NativeEndpointCharacterOriginal.cost (t:=t) c order v parentRows ell p+1)≤
      constant c*CompactNativeRoleTransferBudget.volume parentRows s ell p := by
  have h := NativeEndpointCharacterOriginalBudget.cost_linear (t:=t) c order v parentRows ell p hr hA hG hGK hpay ho
  have hparent : 0<parentRows := lt_of_lt_of_le hr (Nat.div_le_self parentRows c)
  have hV : 0<CompactNativeRoleTransferBudget.volume parentRows s ell p := by
    simpa only [CompactNativeRoleTransferBudget.volume] using
      Nat.mul_pos hparent (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have h1 : NativeEndpointCharacterOriginal.cost (t:=t) c order v parentRows ell p+1≤
      (NativeEndpointCharacterOriginalBudget.constant c+1)*CompactNativeRoleTransferBudget.volume parentRows s ell p := by nlinarith
  simpa only [constant,Nat.mul_assoc] using Nat.mul_le_mul_left endpoints.length h1

end
end IntegerMultBounds.Machine.NativeEndpointCharacterRoles
