import IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalOriginalBudget
import IntegerMultBounds.Machine.NativeEndpointCharacterRoles
import IntegerMultBounds.Machine.NativeEndpointCharacterTerminal
import IntegerMultBounds.Machine.CompactComplexScalarCountLifecycle

/-! Fixed finite role traversal for actual source/sink endpoint characters.
Each physical role is visited once, all original descriptors and complementary
roles remain framed, and each iteration releases the entire private67 bank. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalRoles
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ButterflyStreamData (Coefficient)
open Networks
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {t : ℕ}
attribute [local irreducible] NativeEndpointCharacterCanonicalOriginal.program NativeEndpointCharacterCanonicalOriginal.cost

abbrev Endpoint := NativeEndpointCharacterRoles.Endpoint
abbrev arity := NativeEndpointCharacterRoles.arity
abbrev fixedWeights := NativeEndpointCharacterRoles.fixedWeights
abbrev endpoints := NativeEndpointCharacterRoles.endpoints
abbrev weights_length := NativeEndpointCharacterRoles.weights_length
abbrev endpoints_nodup := NativeEndpointCharacterRoles.endpoints_nodup
abbrev endpoints_complete := NativeEndpointCharacterRoles.endpoints_complete

def one (focus : Fin 15 → Fin t) (src : Endpoint → Fin t) (c : ℕ)
    (m : ℕ) (ws : Endpoint → List (ZMod 4)) (b : Endpoint) :=
  NativeEndpointCharacterCanonicalOriginal.program focus (src b) c m (ws b)

def program (focus : Fin 15 → Fin t) (src : Endpoint → Fin t) (c : ℕ) (m : ℕ) (ws : Endpoint → List (ZMod 4)) :
    List Endpoint → Σ q,Program (t+67) q 2
  | [] => ⟨1,skip (t+67) 2 (by omega)⟩
  | b::bs => ⟨_,seq (one focus src c m ws b) (program focus src c m ws bs).2⟩

def actualProgram (focus : Fin 15 → Fin t) (src : Endpoint → Fin t) :=
  program focus src CompactComplexScalarCountLifecycle.roleDivisor arity fixedWeights endpoints

private theorem one_runs (focus : Fin 15 → Fin t) (src : Endpoint → Fin t)
    (c : ℕ) (hc : 0<c) (v : Stage s) (parentRows ell p : ℕ)
    (m : ℕ) (hslots : v.slots=m) (ws : Endpoint → List (ZMod 4)) (b : Endpoint)
    (hlen : (ws b).length=m) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
 (hr : 0<parentRows/c)
    (xs : Endpoint → Fin (((parentRows/c)*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs b i).1.length=NativePolynomialStageShape.width s p ∧
      (xs b i).2.length=NativePolynomialStageShape.width s p) (caller : Tapes t 2)
    (hs : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words v parentRows ell p i))
    (hh : ∀ i,caller.head (focus i)=1)
    (hsource : caller.tape (src b)=putWord (fun _ => blank) 0
      (UnitPhaseFullStreamNormalized.serialized (xs b))) (hhead : caller.head (src b)=0) :
    HoareTime (one focus src c m ws b)
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(NativeEndpointCharacterRoles.result src v ell p m ws xs caller b).append (FixedHeaderBankCopy.empty 67))
      (NativeEndpointCharacterCanonicalOriginal.cost (t:=t) c v parentRows ell p) := by
  subst m
  exact NativeEndpointCharacterCanonicalOriginal.runs focus (src b) caller c hc v parentRows ell p
    hG hA hK hr (ws b) hlen.symm (xs b) hw hs hh hsource hhead

theorem runs (focus : Fin 15 → Fin t) (src : Endpoint → Fin t)
    (hinj : Function.Injective src) (houtside : ∀ b i,src b≠focus i)
    (c : ℕ) (hc : 0<c) (v : Stage s) (parentRows ell p : ℕ)
    (m : ℕ) (ws : Endpoint → List (ZMod 4)) (hlen : ∀ b,(ws b).length=m)
    (hslots : v.slots=m) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
 (hr : 0<parentRows/c)
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
    HoareTime (program focus src c m ws bs).2
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(NativeEndpointCharacterRoles.output src v ell p m ws xs caller bs).append (FixedHeaderBankCopy.empty 67))
      (bs.length*(NativeEndpointCharacterCanonicalOriginal.cost (t:=t) c v parentRows ell p+1)) := by
  induction bs generalizing caller with
  | nil =>
    simp only [program,NativeEndpointCharacterRoles.output,List.length_nil,zero_mul]
    exact skip_hoare (by omega) _
  | cons b bs ih =>
    have hnodup := List.nodup_cons.mp hn
    have h0 := one_runs focus src c hc v parentRows ell p m hslots ws b (hlen b)
      hG hA hK hr xs (hw b) caller hs hh (hsource b List.mem_cons_self) (hhead b List.mem_cons_self)
    have h1 := ih hnodup.2 (NativeEndpointCharacterRoles.result src v ell p m ws xs caller b)
      (by intro i; simpa only [NativeEndpointCharacterRoles.result,NativeEndpointCharacterLifecycle.resultCaller,setTape,
        Function.update_of_ne (houtside b i).symm] using hs i)
      (by intro i; simpa only [NativeEndpointCharacterRoles.result,NativeEndpointCharacterLifecycle.resultCaller,setTape,
        Function.update_of_ne (houtside b i).symm] using hh i)
      (by
        intro a ha
        have hne : src a≠src b := fun h => hnodup.1 ((hinj h).symm ▸ ha)
        simpa only [NativeEndpointCharacterRoles.result,NativeEndpointCharacterLifecycle.resultCaller,setTape,
          Function.update_of_ne hne] using hsource a (List.mem_cons_of_mem _ ha))
      (by
        intro a ha
        have hne : src a≠src b := fun h => hnodup.1 ((hinj h).symm ▸ ha)
        simpa only [NativeEndpointCharacterRoles.result,NativeEndpointCharacterLifecycle.resultCaller,setTape,
          Function.update_of_ne hne] using hhead a (List.mem_cons_of_mem _ ha))
    exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by simp only [List.length_cons]; nlinarith)

def constant (c : ℕ) := endpoints.length*(NativeEndpointCharacterCanonicalOriginalBudget.constant c+1)

theorem time_linear (c : ℕ) (v : Stage s) (parentRows ell p : ℕ)
    (hr : 0<parentRows/c) (hA : 0<s.axes) (hG : 0<s.guard)
    (hGK : s.guard+1≤s.chunk) (hpay : s.payload=1)
 :
    endpoints.length*(NativeEndpointCharacterCanonicalOriginal.cost (t:=t) c v parentRows ell p+1)≤
      constant c*CompactNativeRoleTransferBudget.volume parentRows s ell p := by
  have h := NativeEndpointCharacterCanonicalOriginalBudget.cost_linear (t:=t) c v parentRows ell p hr hA hG hGK hpay
  have hparent : 0<parentRows := lt_of_lt_of_le hr (Nat.div_le_self parentRows c)
  have hV : 0<CompactNativeRoleTransferBudget.volume parentRows s ell p := by
    simpa only [CompactNativeRoleTransferBudget.volume] using
      Nat.mul_pos hparent (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have h1 : NativeEndpointCharacterCanonicalOriginal.cost (t:=t) c v parentRows ell p+1≤
      (NativeEndpointCharacterCanonicalOriginalBudget.constant c+1)*CompactNativeRoleTransferBudget.volume parentRows s ell p := by nlinarith
  simpa only [constant,Nat.mul_assoc] using Nat.mul_le_mul_left endpoints.length h1

end
end IntegerMultBounds.Machine.NativeEndpointCharacterCanonicalRoles
