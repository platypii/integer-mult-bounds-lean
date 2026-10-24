module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirBankPrepare
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirClassLocalTable

/-! Place the generated converter inputs into the existing class/local bank.
The original matching table is left blank for its separate executed producer. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {A : ℕ}

def reservoirBankPhysicalSlot : Fin 29 → Fin 78 :=
  ![57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,11,75,76,77,0,25,26,43,46,47,14]

theorem reservoirBankPhysicalSlot_injective : Function.Injective reservoirBankPhysicalSlot := by
  decide +kernel

def reservoirConverterSlot : Fin 57 → Fin 78 := Fin.castLE (by decide)

theorem reservoirConverterSlot_injective : Function.Injective reservoirConverterSlot := by
  decide +kernel

theorem reservoirBankPrepared_classLocal
    (R : Fin 78 → List (Fin (A + 4))) (n H : ℕ) (hfit : 9 * H ≤ n)
    (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ) (mate : Fin n → Fin n)
    (hblank : ∀ j : Fin 78, j.val < 57 → R j = []) :
    (fun j => reservoirBankPrepared R reservoirBankPhysicalSlot n H hfit w hw k L
      (reservoirConverterSlot j)) =
      Function.update (reservoirClassLocalBank n H hfit w hw k L mate) 52 [] := by
  funext j
  fin_cases j <;>
    simp [reservoirBankPrepared, reservoirScalarOutputs, reservoirBankPhysicalSlot,
      reservoirBankScalarSlot, reservoirConverterSlot, reservoirClassLocalBank,
      reservoirMiddleProductionBank, reservoirMiddleLookupBank, hblank]

/-- When the original matching table is present, every converter input is ready. -/
theorem reservoirBankPrepared_classLocal_table
    (R : Fin 78 → List (Fin (A + 4))) (n H : ℕ) (hfit : 9 * H ≤ n)
    (w : ℕ) (hw : w ≤ H) (k : Fin 3) (L : ℕ) (mate : Fin n → Fin n)
    (hblank : ∀ j : Fin 78, j.val < 57 → j ≠ 52 → R j = [])
    (htable : R 52 = matchingEntryWords L (matchingTableEntries n (matchingMateCoordinate mate))) :
    (fun j => reservoirBankPrepared R reservoirBankPhysicalSlot n H hfit w hw k L
      (reservoirConverterSlot j)) = reservoirClassLocalBank n H hfit w hw k L mate := by
  funext j
  fin_cases j <;>
    simp [reservoirBankPrepared, reservoirScalarOutputs, reservoirBankPhysicalSlot,
      reservoirBankScalarSlot, reservoirConverterSlot, reservoirClassLocalBank,
      reservoirMiddleProductionBank, reservoirMiddleLookupBank, hblank, htable]

end IntegerMultBounds.MathlibTM2.Routing
