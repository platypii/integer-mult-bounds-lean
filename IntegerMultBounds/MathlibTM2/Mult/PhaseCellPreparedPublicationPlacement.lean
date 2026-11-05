module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationPlan

/-! Place a prepared publication plan through an injective tape embedding.
The standard plan uses the existing publication bank's two data ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def PreparedPublicationPlan.map {T V : ℕ} {src dst : Fin T}
    (plan : PreparedPublicationPlan T src dst) (rg : Fin T → Fin V)
    (hinj : Function.Injective rg) : PreparedPublicationPlan V (rg src) (rg dst) where
  count := rg plan.count
  savedControl := rg plan.savedControl
  advances := rg plan.advances
  savedAdvances := rg plan.savedAdvances
  counter := rg plan.counter
  window := rg plan.window
  zero := rg plan.zero
  acc := rg plan.acc
  control := rg plan.control
  trash := rg plan.trash
  tmp := rg plan.tmp
  padRows := rg plan.padRows
  wordWidth := rg plan.wordWidth
  retireCount := rg plan.retireCount
  gap := rg plan.gap
  hreg := by simpa only [List.map_cons,List.map_nil] using plan.hreg.map hinj

def standardSeamPublicationPlan : PreparedPublicationPlan 117 95 96 where
  count := 0
  savedControl := 1
  advances := 2
  savedAdvances := 3
  counter := 4
  window := 5
  zero := 6
  acc := 7
  control := 8
  trash := 9
  tmp := 10
  padRows := 11
  wordWidth := 12
  retireCount := 13
  gap := 14
  hreg := by decide +kernel

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
