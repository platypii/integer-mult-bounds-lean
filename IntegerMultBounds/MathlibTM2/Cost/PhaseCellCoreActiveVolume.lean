module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryGeometryFast
public import IntegerMultBounds.NLogN.PhaseCellCoreBoundaryVolume

/-! Executed active coupling rows are counted by sparse halo overlap. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open scoped BigOperators

/-- Ambient phase cuts are charged six times, while artificial endpoint work
is charged only to the short guard of each distinct core. -/
theorem coreHalo_activeRows_sum_le {s t : ℕ} [NeZero s] (hst : s < t)
    (width band n : ℕ) (hw : 0 < width) (hr : n*band ≤ width) (boundary : Bool) :
    (∑ k ∈ (coreIndices s width).toFinset,
      let a := (coreHaloEndpoints s width k band n).1
      let b := (coreHaloEndpoints s width k band n).2
      retainedCouplingActiveRows boundary s t band a b a (b-a)) ≤
      6*(Finset.univ \ interiorSet s t (2*band)).card+8*band*(coreIndices s width).length := by
  let K := (coreIndices s width).toFinset
  have hboundary := coreHalo_boundary_volume_le (s := s) t width band n (2*band) hw hr
  have hlocal (k : ℕ) :
      retainedCouplingActiveRows boundary s t band
        (coreHaloEndpoints s width k band n).1 (coreHaloEndpoints s width k band n).2
        (coreHaloEndpoints s width k band n).1
        ((coreHaloEndpoints s width k band n).2-(coreHaloEndpoints s width k band n).1) ≤
      (haloBoundary s t (2*band) (coreHaloEndpoints s width k band n).1
        (coreHaloEndpoints s width k band n).2).card+4*band := by
    have hb := coreHaloEndpoints_bounds s width k band n
    exact retainedCouplingActiveRows_le_boundary hst boundary band _ _ _ _ hb.2 (by omega)
  have hs : (∑ k ∈ K,
      let a := (coreHaloEndpoints s width k band n).1
      let b := (coreHaloEndpoints s width k band n).2
      retainedCouplingActiveRows boundary s t band a b a (b-a)) ≤
      (∑ k ∈ K, (haloBoundary s t (2*band) (coreHaloEndpoints s width k band n).1
        (coreHaloEndpoints s width k band n).2).card)+4*band*(coreIndices s width).length := by
    calc
      _ ≤ ∑ k ∈ K, ((haloBoundary s t (2*band) (coreHaloEndpoints s width k band n).1
          (coreHaloEndpoints s width k band n).2).card+4*band) := Finset.sum_le_sum (fun k _ => hlocal k)
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,K,
          List.toFinset_card_of_nodup (coreIndices_nodup s width)]
        ring
  nlinarith only [hs,hboundary]

/-- Including the stencil width, sparse numerical/page work has one global
gap-volume bill plus a quadratic-band guard bill per core. -/
theorem coreHalo_activeWork_sum_le {s t : ℕ} [NeZero s] (hst : s < t)
    (width band n : ℕ) (hw : 0 < width) (hr : n*band ≤ width) (hband : 1 ≤ band)
    (boundary : Bool) :
    (∑ k ∈ (coreIndices s width).toFinset,
      let a := (coreHaloEndpoints s width k band n).1
      let b := (coreHaloEndpoints s width k band n).2
      retainedCouplingActiveRows boundary s t band a b a (b-a)*(2*band+1)) ≤
      144*(t-s)*band^2+24*(coreIndices s width).length*band^2 := by
  let K := (coreIndices s width).toFinset
  let rows := fun k => retainedCouplingActiveRows boundary s t band
    (coreHaloEndpoints s width k band n).1 (coreHaloEndpoints s width k band n).2
    (coreHaloEndpoints s width k band n).1
    ((coreHaloEndpoints s width k band n).2-(coreHaloEndpoints s width k band n).1)
  have hs := coreHalo_activeRows_sum_le hst width band n hw hr boundary
  have hc := boundary_card s t hst (2*band) (interiorSet s t (2*band))
    (fun j => mem_interiorSet (2*band) j)
  have hg : 1 ≤ t-s := by omega
  have hcount : (∑ k ∈ K, rows k) ≤ 48*band*(t-s)+8*band*(coreIndices s width).length := by
    change (∑ k ∈ K, rows k) ≤ _ at hs
    have hh : band ≤ band*(t-s) := Nat.le_mul_of_pos_right _ hg
    nlinarith only [hs,hc,hh]
  have hwidth : 2*band+1 ≤ 3*band := by omega
  calc
    _ = (∑ k ∈ K, rows k)*(2*band+1) := by rw [Finset.sum_mul]
    _ ≤ (48*band*(t-s)+8*band*(coreIndices s width).length)*(3*band) :=
      Nat.mul_le_mul hcount hwidth
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
