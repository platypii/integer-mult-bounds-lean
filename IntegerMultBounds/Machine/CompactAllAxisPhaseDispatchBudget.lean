import IntegerMultBounds.Machine.CompactAllAxisPhaseDispatch
import IntegerMultBounds.Machine.AllAxisPolynomialNativeBudget

/-! Actual finite edge selection contributes a fixed constant, while the
complete polynomial phase body has its proved linear-volume cost. -/
namespace IntegerMultBounds.Machine.CompactAllAxisPhaseDispatchBudget
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open Networks Networks.ComplexPhaseRowSchedule
open CompactAllAxisPhaseDispatch (count edge)
variable {s : Shape}

noncomputable def constant := (2*FixedBasePowerDescriptor.constant 2+15000)+(2*count+3)

theorem add_volume_bound (C d N P R w B : ℕ)
    (hB : B≤N*(C*P+34*R*w)) (hunit : 1≤N*P) :
    d+B≤N*((C+d)*P+34*R*w) := by
  have hd : d≤d*(N*P) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left d hunit
  nlinarith

theorem overhead_bound (d m : ℕ) (hd : 0<m) (order : Order)
    (v : Stage s) (rows : ℕ) (hr : 0<rows)  (ell w : ℕ)
    (hslots : m≤v.slots)
    (hspan : AllAxisPhaseHeadersData.offset v m+(m*v.f-1)*s.chunk<s.bits)
    (hrecord : s.bits+1≤s.payload) (hR : 2^ell≤s.payload) :
    d+AllAxisPolynomialNative.cost order v rows m ell w≤
      (rows*2^s.bits)*(((2*FixedBasePowerDescriptor.constant 2+15000)+d)*s.payload+34*2^ell*w) := by
  have hc := AllAxisPolynomialNativeBudget.cost_bound order v rows hr
    m ell w hd hslots hspan hrecord hR
  have hn : 1≤rows*2^s.bits := Nat.mul_pos hr (by positivity)
  have hp : 1≤s.payload := by omega
  have hnp : 1≤(rows*2^s.bits)*s.payload := Nat.mul_pos (by omega) (by omega)
  exact add_volume_bound (2*FixedBasePowerDescriptor.constant 2+15000) d
    (rows*2^s.bits) s.payload (2^ell) w
    (AllAxisPolynomialNative.cost order v rows m ell w) hc hnp

theorem call_bound (pc : Fin count) (hd : 0<dimension (edge pc)) (order : Order)
    (v : Stage s) (rows : ℕ) (hr : 0<rows)  (ell w : ℕ)
    (hslots : dimension (edge pc)≤v.slots)
    (hspan : AllAxisPhaseHeadersData.offset v (dimension (edge pc))+
      (dimension (edge pc)*v.f-1)*s.chunk<s.bits)
    (hrecord : s.bits+1≤s.payload) (hR : 2^ell≤s.payload) :
    2*count+3+AllAxisPolynomialNative.cost order v rows (dimension (edge pc)) ell w≤
      (rows*2^s.bits)*(((2*FixedBasePowerDescriptor.constant 2+15000)+(2*count+3))*s.payload+34*2^ell*w) :=
  overhead_bound (2*count+3) (dimension (edge pc)) hd order v rows hr ell w
    hslots hspan hrecord hR

end IntegerMultBounds.Machine.CompactAllAxisPhaseDispatchBudget
