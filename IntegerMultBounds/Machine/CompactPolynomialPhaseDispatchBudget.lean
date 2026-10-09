import IntegerMultBounds.Machine.CompactPolynomialPhaseDispatch
import IntegerMultBounds.Machine.UnitPhasePolynomialNativeBudget

/-! Actual finite edge selection contributes a fixed constant, while the
complete polynomial phase body has its proved linear-volume cost. -/
namespace IntegerMultBounds.Machine.CompactPolynomialPhaseDispatchBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open Networks Networks.ComplexPhaseRowSchedule
open CompactPolynomialPhaseDispatch (count edge)
variable {s : Shape}

noncomputable def constant := (2*FixedBasePowerDescriptor.constant 2+14000)+(2*count+3)

theorem add_volume_bound (C d N P R w B : ℕ)
    (hB : B≤N*(C*P+34*R*w)) (hunit : 1≤N*P) :
    d+B≤N*((C+d)*P+34*R*w) := by
  have hd : d≤d*(N*P) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left d hunit
  nlinarith

theorem overhead_bound (d m : ℕ) (hd : 0<m) (order : Order)
    (v : Stage s) (rows : ℕ) (hr : 0<rows) (axis : Fin v.f) (ell w : ℕ)
    (hslots : m≤v.slots)
    (hspan : SparsePhaseHeadersData.offset v axis m+(m-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) (hR : 2^ell≤s.payload) :
    d+UnitPhasePolynomialNative.cost order v rows axis m ell w≤
      (rows*2^s.bits)*(((2*FixedBasePowerDescriptor.constant 2+14000)+d)*s.payload+34*2^ell*w) := by
  have hc := UnitPhasePolynomialNativeBudget.cost_bound order v rows hr axis
    m ell w hd hslots hspan hrecord hR
  have hn : 1≤rows*2^s.bits := Nat.mul_pos hr (by positivity)
  have hp : 1≤s.payload := by omega
  have hnp : 1≤(rows*2^s.bits)*s.payload := Nat.mul_pos (by omega) (by omega)
  exact add_volume_bound (2*FixedBasePowerDescriptor.constant 2+14000) d
    (rows*2^s.bits) s.payload (2^ell) w
    (UnitPhasePolynomialNative.cost order v rows axis m ell w) hc hnp

theorem call_bound (pc : Fin count) (hd : 0<dimension (edge pc)) (order : Order)
    (v : Stage s) (rows : ℕ) (hr : 0<rows) (axis : Fin v.f) (ell w : ℕ)
    (hslots : dimension (edge pc)≤v.slots)
    (hspan : SparsePhaseHeadersData.offset v axis (dimension (edge pc))+
      (dimension (edge pc)-1)*(v.f*s.chunk)<s.bits)
    (hrecord : s.bits+1≤s.payload) (hR : 2^ell≤s.payload) :
    2*count+3+UnitPhasePolynomialNative.cost order v rows axis (dimension (edge pc)) ell w≤
      (rows*2^s.bits)*(((2*FixedBasePowerDescriptor.constant 2+14000)+(2*count+3))*s.payload+34*2^ell*w) :=
  overhead_bound (2*count+3) (dimension (edge pc)) hd order v rows hr axis ell w
    hslots hspan hrecord hR

end IntegerMultBounds.Machine.CompactPolynomialPhaseDispatchBudget
