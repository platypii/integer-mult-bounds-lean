import IntegerMultBounds.Machine.CompactComplexRootPieceBudget
import IntegerMultBounds.Machine.CompactComplexScalarPathGuard
import IntegerMultBounds.Machine.NativePolynomialStageShape

/-! Every genuine root queue and metadata operation is absorbed by the original
native volume. Recursive callback costs remain their actual indexed sum. -/
namespace IntegerMultBounds.Machine.CompactComplexRootPieceVolume
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexRootPieceBudget (overhead callbacks)

def constant := 111000*(arity+1)^2+4*(arity+2)+100*(arity+6)+71

private theorem cubic_allowance (r A : ℕ) :
    2*A+67+101000*(A+r+1)^2*A+
      4*(r+2)*A+100*(2*A+r*(A+1)+4)+
      (10000*(r+1)^2+2)*A*(A+1) ≤
    (111000*(r+1)^2+4*(r+2)+100*(r+6)+71)*(A+1)^3 := by
  have hscale : A+r+1≤(r+1)*(A+1) := by nlinarith
  have hsq := Nat.mul_le_mul hscale hscale
  have hmain := Nat.mul_le_mul hsq (Nat.le_succ A)
  have hpoly : A+1≤(A+1)^3 := by nlinarith [sq_nonneg (A:ℤ)]
  have hquadratic : A*(A+1)≤(A+1)^3 := by nlinarith
  have hmeta : 2*A+r*(A+1)+4≤(r+6)*(A+1) := by nlinarith
  have hp := Nat.mul_le_mul_left 101000 hmain
  have hq := Nat.mul_le_mul_left (10000*(r+1)^2+2) hquadratic
  have hm := Nat.mul_le_mul_left 100 (hmeta.trans (Nat.mul_le_mul_left (r+6) hpoly))
  have hf := Nat.mul_le_mul_left (4*(r+2)) ((Nat.le_succ A).trans hpoly)
  have he : 2*A+67≤69*(A+1)^3 := by nlinarith
  nlinarith

/-- The fully explicit root overhead has one fixed cubic envelope. -/
theorem overhead_cubic (active : ℕ) : overhead active≤constant*(active+1)^3 :=
  cubic_allowance arity active

private theorem successor_le_power (A : ℕ) : A+1≤2^A := by
  induction A with
  | zero => decide
  | succ A ih =>
    rw [pow_succ]
    nlinarith

/-- The original chunk reserve pays the root's entire polynomial setup,
queue, enumeration and cleanup allowance. -/
theorem overhead_address (sh : Shape) (hchunk : 3≤sh.chunk) :
    overhead sh.active≤constant*2^sh.bits := by
  have hcube := Nat.pow_le_pow_left (successor_le_power sh.active) 3
  have hbits : sh.active*3≤sh.bits := by
    have hm := Nat.mul_le_mul_left sh.active hchunk
    unfold Shape.bits
    omega
  have hexp := Nat.pow_le_pow_right (by decide : 0<2) hbits
  have hpow : (2^sh.active)^3=2^(sh.active*3) := by rw [pow_mul]
  rw [hpow] at hcube
  exact (overhead_cubic sh.active).trans
    (Nat.mul_le_mul_left constant (hcube.trans hexp))

private theorem address_le_volume (sh : Shape) (rows : ℕ) (hr : 0<rows) (hp : 0<sh.payload) :
    2^sh.bits≤rows*sh.recordWidth := by
  have hm : 1≤rows*sh.payload := Nat.mul_pos hr hp
  have h := Nat.mul_le_mul_left (2^sh.bits) hm
  simpa only [Nat.mul_one,Nat.one_mul,Shape.recordWidth,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

/-- Positive original records absorb every concrete root control cost. -/
theorem overhead_volume (sh : Shape) (rows : ℕ)
    (hchunk : 3≤sh.chunk) (hr : 0<rows) (hp : 0<sh.payload) :
    overhead sh.active≤constant*(rows*sh.recordWidth) :=
  (overhead_address sh hchunk).trans (Nat.mul_le_mul_left constant (address_le_volume sh rows hr hp))

/-- Actual expanded polynomial records have positive payload without a
caller-supplied serialization or metadata-cost allowance. -/
theorem overhead_native (sh : Shape) (rows ell p : ℕ)
    (hchunk : 3≤sh.chunk) (hr : 0<rows) :
    overhead sh.active≤constant*(rows*(NativePolynomialStageShape.shape sh ell p).recordWidth) := by
  have hp := NativePolynomialStageShape.payload_fits sh ell p
  exact overhead_volume (NativePolynomialStageShape.shape sh ell p) rows hchunk hr (by
    change 0<NativePolynomialStageShape.payload sh ell p
    omega)

/-- The same allowance is linear in the actual symbol-triple serialized input. -/
theorem overhead_serialized (sh : Shape) (rows ell p : ℕ)
    (hchunk : 3≤sh.chunk) (hr : 0<rows) :
    overhead sh.active≤(3*constant)*
      (rows*2^sh.bits*ActivePrefixStageNativePolynomial.symbols (2^ell)
        (NativePolynomialStageShape.width sh p)) := by
  have h := overhead_native sh rows ell p hchunk hr
  rw [NativePolynomialStageShape.volume] at h
  simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

/-- The original multiplier chunk eventually supplies this fixed reserve. -/
theorem eventually_chunk : ∀ᶠ n : ℕ in Filter.atTop,3≤Sizes.K n :=
  CompactComplexScalarPathGuard.eventually_chunk_room 3


/-- The complete fixed root machine pays its real queue, descriptor and
cleanup lifecycle from original volume, plus the true recursive callback sum. -/
theorem runs_volume {a t q : ℕ} (sh : Shape) (rows : ℕ)
    (hchunk : 3≤sh.chunk) (hr : 0<rows) (hp : 0<sh.payload)
    (src : Fin t) (callback : Program (43+(1+t)) q a)
    (native : ℕ → Tapes t a) (callCost : ℕ → ℕ → ℕ)
    (ht : (native 0).tape src=RadixZeroFill.encodedBinary
      (RecursiveChildQuotientsConstant.bits sh.active))
    (hh : (native 0).head src=1)
    (hc : CompactComplexRootPieceRun.CallbackSpec callback sh.active native callCost) :
    HoareTime (CompactComplexRootPieceRun.program src callback).2
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 (native 0))
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 (native (CompactComplexRootPiecePrefixes.count (Nat.digits arity sh.active))))
      (constant*(rows*sh.recordWidth)+callbacks sh.active callCost) :=
  (CompactComplexRootPieceBudget.runs src callback sh.active native callCost ht hh hc).consequence
    (fun _ h => h) (fun _ h => h)
    (Nat.add_le_add_right (overhead_volume sh rows hchunk hr hp) _)

/-- Real polynomial metadata supplies the positive native volume used for
root overhead, with no prepared queue or control-cost contract. -/
theorem runs_native {a t q : ℕ} (sh : Shape) (rows ell p : ℕ)
    (hchunk : 3≤sh.chunk) (hr : 0<rows)
    (src : Fin t) (callback : Program (43+(1+t)) q a)
    (native : ℕ → Tapes t a) (callCost : ℕ → ℕ → ℕ)
    (ht : (native 0).tape src=RadixZeroFill.encodedBinary
      (RecursiveChildQuotientsConstant.bits sh.active))
    (hh : (native 0).head src=1)
    (hc : CompactComplexRootPieceRun.CallbackSpec callback sh.active native callCost) :
    HoareTime (CompactComplexRootPieceRun.program src callback).2
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 (native 0))
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 (native (CompactComplexRootPiecePrefixes.count (Nat.digits arity sh.active))))
      (constant*(rows*(NativePolynomialStageShape.shape sh ell p).recordWidth)+
        callbacks sh.active callCost) :=
  (CompactComplexRootPieceBudget.runs src callback sh.active native callCost ht hh hc).consequence
    (fun _ h => h) (fun _ h => h)
    (Nat.add_le_add_right (overhead_native sh rows ell p hchunk hr) _)

/-- The serialized-symbol expression is the same paid native input volume. -/
theorem runs_serialized {a t q : ℕ} (sh : Shape) (rows ell p : ℕ)
    (hchunk : 3≤sh.chunk) (hr : 0<rows)
    (src : Fin t) (callback : Program (43+(1+t)) q a)
    (native : ℕ → Tapes t a) (callCost : ℕ → ℕ → ℕ)
    (ht : (native 0).tape src=RadixZeroFill.encodedBinary
      (RecursiveChildQuotientsConstant.bits sh.active))
    (hh : (native 0).head src=1)
    (hc : CompactComplexRootPieceRun.CallbackSpec callback sh.active native callCost) :
    HoareTime (CompactComplexRootPieceRun.program src callback).2
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 (native 0))
      (fun v => v=CompactComplexRootPieceDigit.input CompactComplexRootDigitsFromHeader.emptyState
        (fun _ => blank) 0 (native (CompactComplexRootPiecePrefixes.count (Nat.digits arity sh.active))))
      ((3*constant)*(rows*2^sh.bits*ActivePrefixStageNativePolynomial.symbols (2^ell)
        (NativePolynomialStageShape.width sh p))+callbacks sh.active callCost) :=
  (CompactComplexRootPieceBudget.runs src callback sh.active native callCost ht hh hc).consequence
    (fun _ h => h) (fun _ h => h)
    (Nat.add_le_add_right (overhead_serialized sh rows ell p hchunk hr) _)

end
end IntegerMultBounds.Machine.CompactComplexRootPieceVolume
