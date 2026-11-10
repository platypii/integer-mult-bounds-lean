module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicComplexCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRecoveryLayout
import Mathlib.Tactic.FinCases

/-! One physical allocation shares the selector's RHS and row ruler directly
with the cyclic numerical caller. Separation is structural over role sums. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
noncomputable section

abbrev Role := Fin LocalRecoveryLayout.tapes ⊕ (Fin 909 ⊕ (Fin 392 ⊕ (Fin 392 ⊕ Fin 8)))
def tapes : ℕ := Fintype.card Role
def port : Role → Fin tapes := Fintype.equivFin Role
theorem port_injective : Function.Injective port := (Fintype.equivFin Role).injective

def selector (i : Fin LocalRecoveryLayout.tapes) : Fin tapes := port (.inl i)
def numeric (i : Fin 909) : Fin tapes := port (.inr (.inl i))
def seedL (i : Fin 392) : Fin tapes := port (.inr (.inr (.inl i)))
def seedR (i : Fin 392) : Fin tapes := port (.inr (.inr (.inr (.inl i))))
def aux (i : Fin 8) : Fin tapes := port (.inr (.inr (.inr (.inr i))))
def geometry (i : Fin 117) : Fin tapes := selector (LocalRecoveryLayout.geometry i)

theorem selector_injective : Function.Injective selector := by
  intro i j h; exact Sum.inl.inj (port_injective h)
theorem numeric_injective : Function.Injective numeric := by
  intro i j h; exact Sum.inl.inj (Sum.inr.inj (port_injective h))

theorem selector_ne_aux (i : Fin LocalRecoveryLayout.tapes) (j : Fin 8) : selector i ≠ aux j := by
  simp [selector,aux,port_injective.eq_iff]
theorem selector_ne_numeric (i : Fin LocalRecoveryLayout.tapes) (j : Fin 909) : selector i ≠ numeric j := by
  simp [selector,numeric,port_injective.eq_iff]
theorem selector_ne_seedL (i : Fin LocalRecoveryLayout.tapes) (j : Fin 392) : selector i ≠ seedL j := by
  simp [selector,seedL,port_injective.eq_iff]
theorem selector_ne_seedR (i : Fin LocalRecoveryLayout.tapes) (j : Fin 392) : selector i ≠ seedR j := by
  simp [selector,seedR,port_injective.eq_iff]

def controls : Fin 3 → Fin tapes := ![geometry 94,aux 0,aux 1]

def caller : CyclicComplexCallerLayout tapes where
  bank := numeric
  injective := numeric_injective
  seedL := seedL
  seedR := seedR
  controls := controls
  count := aux 2
  archive := selector LocalRecoveryLayout.source
  saved := aux 3
  span := selector LocalRecoveryLayout.rowCount
  tmp := aux 4
  move := by simp [aux,selector,numeric,port_injective.eq_iff]
  seedOff := by intro i j; simp [seedL,seedR,numeric,port_injective.eq_iff]
  seedTmp := by intro i; simp [seedL,seedR,aux,port_injective.eq_iff]
  seedArchive := by intro i; simp [seedL,seedR,selector,port_injective.eq_iff]
  controlOff := by
    intro i j
    fin_cases i <;> simp [controls,geometry,selector,aux,numeric,port_injective.eq_iff]
  controlTmp := by
    intro i
    fin_cases i <;> simp [controls,geometry,selector,aux,port_injective.eq_iff]
  controlArchive := by
    intro i
    fin_cases i <;> simp [controls,geometry,selector,aux,port_injective.eq_iff,
      LocalRecoveryLayout.source,LocalRecoveryLayout.geometry,LocalRecoveryLayout.port_injective.eq_iff]
  spanOff := by intro i; simp [selector,numeric,port_injective.eq_iff]
  spanTmp := by simp [selector,aux,port_injective.eq_iff]
  spanArchive := by
    simp [selector,port_injective.eq_iff,LocalRecoveryLayout.source,LocalRecoveryLayout.rowCount,
      LocalRecoveryLayout.geometry,LocalRecoveryLayout.port_injective.eq_iff]
  tmpOff := by intro i; simp [numeric,aux,port_injective.eq_iff]
  archiveOff := by intro i; simp [selector,numeric,port_injective.eq_iff]

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
