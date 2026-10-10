import IntegerMultBounds.Machine.NativeUniformPolynomialRotationPlacement

/-! Original caller endpoint correction: physically copy retained raw numeric
headers, derive the actual role polynomial count, uniformly rotate or negate
the native role source, and reclaim all67 private tapes. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotationOriginal
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open ButterflyStreamData (Coefficient)
open SharedPlacementAlphabet (setTape sharedPlacement)
open CompactComplexScalarCountLifecycle (roleDivisor)
open NativeUniformPolynomialRotationHeaders (count)
open UnitPhaseFullStreamNormalized (serialized)
variable {s : Shape} {t : ℕ}
attribute [local irreducible] CompactComplexRolePhaseSite.roleCount roleDivisor

private theorem right_frame {n q k : ℕ} {M : Program n q 2} {x y : Tapes n 2}
    (h : HoareTime M (fun z => z=x) (fun z => z=y) k) (caller : Tapes t 2) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+t) ≃ Fin (t+n)))
      (fun z => z=caller.append x) (fun z => z=caller.append y) k := by
  have he (z : Tapes n 2) : Placement.combine finAddFlip z caller=caller.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x caller)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun z hz => hz.trans (he x).symm) _ le_rfl
  rintro z ⟨u,hu,rfl⟩
  subst u
  simpa only [Placement.replace,Placement.extra_combine] using he y

def setup := Placement.placed NativeUniformPolynomialRotationHeaders.program
  (finAddFlip : Fin (67+t) ≃ Fin (t+67))
def eraseCount := Placement.placed NativeUniformPolynomialRotationHeaders.eraseCount
  (finAddFlip : Fin (67+t) ≃ Fin (t+67))
def kernel (negative : Bool) : Σ q,Program 67 q 2 :=
  if negative then ⟨_,NativeUniformPolynomialRotationPlacement.negativeProgram⟩
  else ⟨_,NativeUniformPolynomialRotationPlacement.program⟩
def call (src : Fin t) (negative : Bool) := Placement.placed (kernel negative).2
  (sharedPlacement src (56 : Fin 67))
def program (focus : Fin 15 → Fin t) (src : Fin t) (negative : Bool) :=
  seq (NativeEndpointCharacterCopy.program focus) (seq setup
    (seq (call src negative) (seq eraseCount (NativeUniformPolynomialRotationHeaders.erase (t:=t)))))
def rotation (focus : Fin 15 → Fin t) (src : Fin t) := program focus src false
def negation (focus : Fin 15 → Fin t) (src : Fin t) := program focus src true

def exponent (negative : Bool) (v : Stage s) :=
  if negative then (2 : Fin 4) else NativeUniformPolynomialRotation.phase v.f
def resultCaller (negative : Bool) (v : Stage s) (caller : Tapes t 2) (src : Fin t)
    {N : ℕ} (xs : Fin N → Coefficient) :=
  setTape caller src (putWord (fun _ => blank) 0
    (serialized (UnitPhasePolynomialArray.result (exponent negative v) xs))) 0

theorem frame (negative : Bool) (v : Stage s) (caller : Tapes t 2) (src i : Fin t)
    {N : ℕ} (xs : Fin N → Coefficient) (hi : i≠src) :
    (resultCaller negative v caller src xs).head i=caller.head i ∧
      (resultCaller negative v caller src xs).tape i=caller.tape i := by
  simp [resultCaller,setTape,hi]

private theorem clear_source (v : Stage s) (parentRows ell p : ℕ) {N : ℕ}
    (xs : Fin N → Coefficient) :
    setTape (NativeUniformPolynomialRotationPlacement.input v parentRows ell p xs)
      56 (fun _ => blank) 0=count v parentRows ell p := by
  rw [NativeUniformPolynomialRotationPlacement.input,SharedPlacementAlphabet.setTape_setTape]
  exact SharedPlacementAlphabet.setTape_self _ _

private theorem call_runs (negative : Bool) (src : Fin t) (caller : Tapes t 2)
    (v : Stage s) (parentRows ell p w : ℕ) (hr : 0<parentRows/roleDivisor)
    (xs : Fin (((parentRows/roleDivisor)*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hs : caller.tape src=putWord (fun _ => blank) 0 (serialized xs)) (hh : caller.head src=0) :
    HoareTime (call src negative) (fun z => z=caller.append (count v parentRows ell p))
      (fun z => z=(resultCaller negative v caller src xs).append (count v parentRows ell p))
      (NativeUniformPolynomialRotationNormalized.cost
        (((parentRows/roleDivisor)*2^s.bits)*2^ell) w) := by
  have hlocal : HoareTime (kernel negative).2
      (fun z => z=NativeUniformPolynomialRotationPlacement.input v parentRows ell p xs)
      (fun z => z=NativeUniformPolynomialRotationPlacement.input v parentRows ell p
        (UnitPhasePolynomialArray.result (exponent negative v) xs))
      (NativeUniformPolynomialRotationNormalized.cost
        (((parentRows/roleDivisor)*2^s.bits)*2^ell) w) := by
    cases negative with
    | false => exact NativeUniformPolynomialRotationPlacement.runs v parentRows ell p w hr xs hw
    | true => exact NativeUniformPolynomialRotationPlacement.negative_runs v parentRows ell p w hr xs hw
  have h := SharedPlacementAlphabet.shared_hoare hlocal caller src (56 : Fin 67)
    (fun _ => blank) 0 hs hh
  rw [clear_source,clear_source] at h
  exact h

def cost (v : Stage s) (parentRows ell p w : ℕ) :=
  FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 15) (NativeEndpointCharacterCopy.words v parentRows ell p)+1+
    (NativeUniformPolynomialRotationHeaders.cost v parentRows ell p+1+
      (NativeUniformPolynomialRotationNormalized.cost (((parentRows/roleDivisor)*2^s.bits)*2^ell) w+1+
        (8*(((parentRows/roleDivisor)*2^s.bits)*2^ell)+1+
          FixedHeaderBankCopy.cleanupCost (t:=t) (NativeEndpointCharacterCopy.words v parentRows ell p))))

/-- Every numeric/count/phase header is physically constructed or copied
from original inputs. The whole caller bank is preserved except its chosen
native source; the private bank returns entirely blank and normalized. -/
theorem runs (negative : Bool) (focus : Fin 15 → Fin t) (src : Fin t) (caller : Tapes t 2)
    (v : Stage s) (parentRows ell p w : ℕ) (hr : 0<parentRows/roleDivisor)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (xs : Fin (((parentRows/roleDivisor)*2^s.bits)*2^ell) → Coefficient)
    (hw : ∀ i,(xs i).1.length=w ∧ (xs i).2.length=w)
    (hs : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words v parentRows ell p i))
    (hh : ∀ i,caller.head (focus i)=1)
    (hsource : caller.tape src=putWord (fun _ => blank) 0 (serialized xs))
    (hhead : caller.head src=0) :
    HoareTime (program focus src negative)
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(resultCaller negative v caller src xs).append (FixedHeaderBankCopy.empty 67))
      (cost (t:=t) v parentRows ell p w) := by
  have hcopy := NativeEndpointCharacterCopy.runs focus caller v parentRows ell p hs hh
  have hsetup := right_frame (NativeUniformPolynomialRotationHeaders.runs v parentRows ell p hG hA hK) caller
  have hcall := call_runs negative src caller v parentRows ell p w hr xs hw hsource hhead
  have hcount := right_frame (NativeUniformPolynomialRotationHeaders.erase_count_runs v parentRows ell p hr)
    (resultCaller negative v caller src xs)
  have herase := NativeUniformPolynomialRotationHeaders.erase_runs (resultCaller negative v caller src xs)
    v parentRows ell p
  exact hcopy.seq (hsetup.seq (hcall.seq (hcount.seq herase)))

end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotationOriginal
