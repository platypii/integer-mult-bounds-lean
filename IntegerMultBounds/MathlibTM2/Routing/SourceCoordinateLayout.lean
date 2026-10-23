module

public import IntegerMultBounds.MathlibTM2.Routing.SourceOuterRecord
public import IntegerMultBounds.MathlibTM2.Routing.SourceSegmentRecord
public import IntegerMultBounds.MathlibTM2.Routing.SourceRegionDispatch

/-! One abstract workspace for every coordinate-to-record branch. The maps
share coordinate fields and scratch, and differ only at the region-base input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {T : ℕ}

def sourceCoordinateOuter (rg : Fin 21 → Fin T) (high : Bool) : Fin 9 → Fin T :=
  ![rg 0, rg (if high then 2 else 4), rg 6, rg 7, rg 5, rg 13, rg 14, rg 15, rg 16]

def sourceCoordinateSegment (rg : Fin 21 → Fin T) : Fin 13 → Fin T :=
  ![rg 0, rg 1, rg 3, rg 8, rg 9, rg 6, rg 10, rg 11, rg 12, rg 13, rg 14, rg 15, rg 16]

def sourceCoordinateRegion (rg : Fin 21 → Fin T) : Fin 7 → Fin T :=
  ![rg 0, rg 1, rg 2, rg 13, rg 14, rg 15, rg 16]

theorem sourceCoordinateOuter_injective (rg : Fin 21 → Fin T) (hrg : Function.Injective rg)
    (high : Bool) : Function.Injective (sourceCoordinateOuter rg high) := by
  intro i j h
  cases high <;> fin_cases i <;> fin_cases j <;> simp_all [sourceCoordinateOuter, hrg.eq_iff]

theorem sourceCoordinateSegment_injective (rg : Fin 21 → Fin T) (hrg : Function.Injective rg) :
    Function.Injective (sourceCoordinateSegment rg) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [sourceCoordinateSegment, hrg.eq_iff]

theorem sourceCoordinateRegion_injective (rg : Fin 21 → Fin T) (hrg : Function.Injective rg) :
    Function.Injective (sourceCoordinateRegion rg) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [sourceCoordinateRegion, hrg.eq_iff]

end IntegerMultBounds.MathlibTM2.Routing
