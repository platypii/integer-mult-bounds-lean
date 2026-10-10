import IntegerMultBounds.Machine.NativeUniformPolynomialRotationOriginal
import IntegerMultBounds.Machine.NativePolynomialStageHeaderBudget

/-! Every original-header copy, actual role-count construction, native stream
rewind/overwrite, count/header cleanup and connecting transition is paid by
the real original parent native polynomial volume. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotationOriginalBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexScalarCountLifecycle (roleDivisor)
variable {s : Shape} {t : ℕ}
attribute [local irreducible] volume roleDivisor CompactComplexRolePhaseSite.roleCount

def constant := CompactComplexScalarCountBudget.roleConstant roleDivisor+5262

private theorem scalar_words (v : Stage s) (rows ell p : ℕ) :
    ∀ i,Counter.value (NativeEndpointCharacterCopy.words v rows ell p i)≤
      CompactSpectatorLeafSetupBudget.scalar s rows ell p v.rho v.left v.f v.slots v.right
        v.source.val v.target.val := by
  intro i
  rw [NativeEndpointCharacterCopy.words,RecursiveChildQuotientsConstant.bits_value]
  fin_cases i <;> simp [NativeEndpointCharacterCopy.index,NativeEndpointCharacterPrepare.raw,
    CompactSpectatorLeafSetup.raw]
  all_goals unfold CompactSpectatorLeafSetupBudget.scalar; omega

 theorem cost_linear (v : Stage s) (parentRows ell p : ℕ)
    (hr : 0<parentRows/roleDivisor) (hA : 0<s.axes) (hG : 0<s.guard)
    (hK : 0<s.chunk) (hpay : s.payload=1) :
    NativeUniformPolynomialRotationOriginal.cost (t:=t) v parentRows ell p
      (CompactNativeRoleHeaders.recordWidth s p)≤constant*volume parentRows s ell p := by
  have hparent : 0<parentRows := lt_of_lt_of_le hr (Nat.div_le_self parentRows roleDivisor)
  have hV : 0<volume parentRows s ell p := by
    simpa only [volume] using Nat.mul_pos hparent (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have hs := NativePolynomialStageHeaderBudget.scalar_le v parentRows ell p hparent hA hG hK hpay
  have hc := FixedHeaderBankCopy.cost_linear (NativeEndpointCharacterCopy.words v parentRows ell p)
    (18*volume parentRows s ell p) (by positivity)
    (fun _ => RecursiveChildQuotientsConstant.bits_canonical _)
    (fun i => (scalar_words v parentRows ell p i).trans hs)
  have he := FixedHeaderBankCopy.cleanup_cost_linear (t:=t)
    (NativeEndpointCharacterCopy.words v parentRows ell p) (18*volume parentRows s ell p) (by positivity)
    (fun _ => RecursiveChildQuotientsConstant.bits_canonical _)
    (fun i => (scalar_words v parentRows ell p i).trans hs)
  have hsetup := NativeUniformPolynomialRotationHeaders.cost_linear v parentRows ell p hparent hG hA hK
  have hcount : (parentRows/roleDivisor)*2^s.bits*2^ell≤parentRows*2^s.bits*2^ell :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.div_le_self parentRows roleDivisor))
  have hparentcount : parentRows*2^s.bits*2^ell≤volume parentRows s ell p := by
    unfold volume CompactNativeRoleOriginal.symbols CompactNativeRoleOriginal.inner
    have hW : 1≤2*(CompactNativeRoleHeaders.recordWidth s p+1) := by omega
    have h := Nat.mul_le_mul_right (parentRows*2^s.bits*2^ell) hW
    simpa only [one_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
  have hn : 0<(parentRows/roleDivisor)*2^s.bits*2^ell := by positivity
  have hphase := NativeUniformPolynomialRotationNormalized.cost_linear
    ((parentRows/roleDivisor)*2^s.bits*2^ell) (CompactNativeRoleHeaders.recordWidth s p) hn
  have hrolevolume : ((parentRows/roleDivisor)*2^s.bits*2^ell)*
      (2*(CompactNativeRoleHeaders.recordWidth s p+1))≤volume parentRows s ell p := by
    have h := Nat.mul_le_mul_right (2*(CompactNativeRoleHeaders.recordWidth s p+1)) hcount
    convert h using 1; unfold volume CompactNativeRoleOriginal.symbols CompactNativeRoleOriginal.inner; ring
  have hphase' := hphase.trans (Nat.mul_le_mul_left 120 hrolevolume)
  have hsetup' := hsetup.trans (Nat.mul_le_mul_left _ hparentcount)
  have hcleanup : 8*((parentRows/roleDivisor)*2^s.bits*2^ell)≤8*volume parentRows s ell p :=
    Nat.mul_le_mul_left 8 (hcount.trans hparentcount)
  unfold NativeUniformPolynomialRotationOriginal.cost constant
  nlinarith only [hc,he,hphase',hsetup',hcleanup,hV]

theorem runs_linear (negative : Bool) (focus : Fin 15 → Fin t) (src : Fin t) (caller : Tapes t 2)
    (v : Stage s) (parentRows ell p : ℕ) (hr : 0<parentRows/roleDivisor)
    (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk) (hpay : s.payload=1)
    (xs : Fin (((parentRows/roleDivisor)*2^s.bits)*2^ell) → ButterflyStreamData.Coefficient)
    (hw : ∀ i,(xs i).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (xs i).2.length=CompactNativeRoleHeaders.recordWidth s p)
    (hs : ∀ i,caller.tape (focus i)=RadixZeroFill.encodedBinary
      (NativeEndpointCharacterCopy.words v parentRows ell p i))
    (hh : ∀ i,caller.head (focus i)=1)
    (hsource : caller.tape src=putWord (fun _ => blank) 0 (UnitPhaseFullStreamNormalized.serialized xs))
    (hhead : caller.head src=0) :
    HoareTime (NativeUniformPolynomialRotationOriginal.program focus src negative)
      (fun z => z=caller.append (FixedHeaderBankCopy.empty 67))
      (fun z => z=(NativeUniformPolynomialRotationOriginal.resultCaller negative v caller src xs).append
        (FixedHeaderBankCopy.empty 67))
      (constant*volume parentRows s ell p) :=
  (NativeUniformPolynomialRotationOriginal.runs negative focus src caller v parentRows ell p
    (CompactNativeRoleHeaders.recordWidth s p) hr hG hA hK xs hw hs hh hsource hhead).consequence
      (fun _ h => h) (fun _ h => h) (cost_linear v parentRows ell p hr hA hG hK hpay)

end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotationOriginalBudget
