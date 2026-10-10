import IntegerMultBounds.Machine.NativeUniformPolynomialRotationOriginalBudget
import IntegerMultBounds.Machine.CompactComplexEndpointRoleExchange

/-! Actual finite endpoint traversal for runtime-column correction or fixed
negation. Each role uses the retained original headers, constructs its private
count and flags, and returns all67 borrowed tapes blank. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotationRoles
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ButterflyStreamData (Coefficient)
open CompactComplexScalarCountLifecycle (roleDivisor)
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {t : ℕ}
attribute [local irreducible] NativeUniformPolynomialRotationOriginal.program
  NativeUniformPolynomialRotationOriginal.cost roleDivisor CompactComplexRolePhaseSite.roleCount
abbrev Endpoint := CompactComplexEndpointRoleExchange.Address

def program (negative : Bool) (focus : Fin 15 → Fin t) (src : Endpoint → Fin t) :
    List Endpoint → Σ q,Program (t+67) q 2
  | [] => ⟨1,skip (t+67) 2 (by omega)⟩
  | b::bs => ⟨_,seq (NativeUniformPolynomialRotationOriginal.program focus (src b) negative)
      (program negative focus src bs).2⟩

def actualProgram (negative : Bool) (focus : Fin 15 → Fin t) (src : Endpoint → Fin t) :=
  program negative focus src CompactComplexEndpointRoleExchange.addresses

def result (negative : Bool) (src : Endpoint → Fin t) (v : Stage s) {N : ℕ}
    (xs : Endpoint → Fin N → Coefficient) (caller : Tapes t 2) (b : Endpoint) :=
  NativeUniformPolynomialRotationOriginal.resultCaller negative v caller (src b) (xs b)

def output (negative : Bool) (src : Endpoint → Fin t) (v : Stage s) {N : ℕ}
    (xs : Endpoint → Fin N → Coefficient) : Tapes t 2 → List Endpoint → Tapes t 2
  | caller,[] => caller
  | caller,b::bs => output negative src v xs (result negative src v xs caller b) bs

theorem runs (negative : Bool) (focus : Fin 15 → Fin t) (src : Endpoint → Fin t)
    (hinj : Function.Injective src) (houtside : ∀ b i,src b≠focus i)
    (v : Stage s) (parentRows ell p w : ℕ) (hr : 0<parentRows/roleDivisor)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (xs : Endpoint → Fin (((parentRows/roleDivisor)*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ b i,(xs b i).1.length=w ∧ (xs b i).2.length=w)
    (bs : List Endpoint) (hn : bs.Nodup) (caller : Tapes t 2)
    (hs : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words v parentRows ell p i))
    (hh : ∀ i,caller.head (focus i)=1)
    (hsource : ∀ b∈bs,caller.tape (src b)=putWord (fun _ => blank) 0
      (UnitPhaseFullStreamNormalized.serialized (xs b)))
    (hhead : ∀ b∈bs,caller.head (src b)=0) :
    HoareTime (program negative focus src bs).2
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(output negative src v xs caller bs).append (FixedHeaderBankCopy.empty 67))
      (bs.length*(NativeUniformPolynomialRotationOriginal.cost (t:=t) v parentRows ell p w+1)) := by
  induction bs generalizing caller with
  | nil =>
    simp only [program,output,List.length_nil,zero_mul]
    exact skip_hoare (by omega) _
  | cons b bs ih =>
    have hnodup := List.nodup_cons.mp hn
    have h0 := NativeUniformPolynomialRotationOriginal.runs negative focus (src b) caller
      v parentRows ell p w hr hG hA hK (xs b) (hw b) hs hh
      (hsource b List.mem_cons_self) (hhead b List.mem_cons_self)
    have h1 := ih hnodup.2 (result negative src v xs caller b)
      (by intro i; simpa only [result,NativeUniformPolynomialRotationOriginal.resultCaller,setTape,
        Function.update_of_ne (houtside b i).symm] using hs i)
      (by intro i; simpa only [result,NativeUniformPolynomialRotationOriginal.resultCaller,setTape,
        Function.update_of_ne (houtside b i).symm] using hh i)
      (by
        intro a ha
        have hne : src a≠src b := fun h => hnodup.1 ((hinj h).symm ▸ ha)
        simpa only [result,NativeUniformPolynomialRotationOriginal.resultCaller,setTape,
          Function.update_of_ne hne] using hsource a (List.mem_cons_of_mem _ ha))
      (by
        intro a ha
        have hne : src a≠src b := fun h => hnodup.1 ((hinj h).symm ▸ ha)
        simpa only [result,NativeUniformPolynomialRotationOriginal.resultCaller,setTape,
          Function.update_of_ne hne] using hhead a (List.mem_cons_of_mem _ ha))
    exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h)
      (by simp only [List.length_cons]; nlinarith)

theorem output_frame (negative : Bool) (src : Endpoint → Fin t) (v : Stage s) {N : ℕ}
    (xs : Endpoint → Fin N → Coefficient) (bs : List Endpoint) (caller : Tapes t 2)
    (i : Fin t) (hi : ∀ b∈bs,src b≠i) :
    (output negative src v xs caller bs).head i=caller.head i ∧
      (output negative src v xs caller bs).tape i=caller.tape i := by
  induction bs generalizing caller with
  | nil => exact ⟨rfl,rfl⟩
  | cons b bs ih =>
    have h := ih (result negative src v xs caller b) (fun a ha => hi a (List.mem_cons_of_mem _ ha))
    simpa only [output,result,NativeUniformPolynomialRotationOriginal.resultCaller,setTape,
      Function.update_of_ne (hi b List.mem_cons_self).symm] using h

theorem output_role (negative : Bool) (src : Endpoint → Fin t) (hinj : Function.Injective src)
    (v : Stage s) {N : ℕ} (xs : Endpoint → Fin N → Coefficient)
    (bs : List Endpoint) (hn : bs.Nodup) (caller : Tapes t 2) (b : Endpoint) (hb : b∈bs) :
    (output negative src v xs caller bs).head (src b)=0 ∧
      (output negative src v xs caller bs).tape (src b)=putWord (fun _ => blank) 0
        (UnitPhaseFullStreamNormalized.serialized
          (UnitPhasePolynomialArray.result (NativeUniformPolynomialRotationOriginal.exponent negative v) (xs b))) := by
  induction bs generalizing caller with
  | nil => exact (List.not_mem_nil hb).elim
  | cons a bs ih =>
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hb with rfl | hb
    · have h := output_frame negative src v xs bs (result negative src v xs caller b) (src b)
        (by intro a ha; exact fun he => hn'.1 (hinj he ▸ ha))
      constructor
      · exact h.1.trans (by simp only [result,NativeUniformPolynomialRotationOriginal.resultCaller,setTape,Function.update_self])
      · exact h.2.trans (by simp only [result,NativeUniformPolynomialRotationOriginal.resultCaller,setTape,Function.update_self])
    · exact ih hn'.2 (result negative src v xs caller a) hb

def constant := CompactComplexEndpointRoleExchange.addresses.length*
  (NativeUniformPolynomialRotationOriginalBudget.constant+1)

theorem time_linear (v : Stage s) (parentRows ell p : ℕ)
    (hr : 0<parentRows/roleDivisor) (hA : 0<s.axes) (hG : 0<s.guard)
    (hK : 0<s.chunk) (hpay : s.payload=1) :
    CompactComplexEndpointRoleExchange.addresses.length*
      (NativeUniformPolynomialRotationOriginal.cost (t:=t) v parentRows ell p
        (CompactNativeRoleHeaders.recordWidth s p)+1)≤
      constant*CompactNativeRoleTransferBudget.volume parentRows s ell p := by
  have h := NativeUniformPolynomialRotationOriginalBudget.cost_linear (t:=t)
    v parentRows ell p hr hA hG hK hpay
  have hparent : 0<parentRows := lt_of_lt_of_le hr (Nat.div_le_self parentRows roleDivisor)
  have hV : 0<CompactNativeRoleTransferBudget.volume parentRows s ell p := by
    simpa only [CompactNativeRoleTransferBudget.volume] using
      Nat.mul_pos hparent (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have h1 : NativeUniformPolynomialRotationOriginal.cost (t:=t) v parentRows ell p
      (CompactNativeRoleHeaders.recordWidth s p)+1≤
      (NativeUniformPolynomialRotationOriginalBudget.constant+1)*
        CompactNativeRoleTransferBudget.volume parentRows s ell p := by nlinarith
  simpa only [constant,Nat.mul_assoc] using
    Nat.mul_le_mul_left CompactComplexEndpointRoleExchange.addresses.length h1

end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotationRoles
