module

public import IntegerMultBounds.MathlibTM2.Routing.CounterSourceLoopFrame

/-! Closed count, archive and index contents after direct counter source generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

theorem counterSourceTrace_count (R : Fin T → List (Fin (A + 4))) (rg : Fin 5 → Fin T)
    (count saved dst : Fin T) (hcs : count ≠ saved) (hcd : count ≠ dst) (hci : count ≠ rg 0)
    (L i : ℕ) (input : List (Fin (A + 4))) (hc : R count = input) :
    counterSourceTraceBank R rg count saved dst L i input count = [] := by
  induction input generalizing R i with
  | nil => exact hc
  | cons x rest ih =>
    apply ih
    simp [counterSourceReverseStepBank, hcs, hcd, hci]

theorem counterSourceTrace_saved (R : Fin T → List (Fin (A + 4))) (rg : Fin 5 → Fin T)
    (count saved dst : Fin T) (_hsc : saved ≠ count) (hsd : saved ≠ dst) (hsi : saved ≠ rg 0)
    (L i : ℕ) (input : List (Fin (A + 4))) :
    counterSourceTraceBank R rg count saved dst L i input saved = input.reverse ++ R saved := by
  induction input generalizing R i with
  | nil => simp [counterSourceTraceBank]
  | cons x rest ih =>
    rw [counterSourceTraceBank, ih]
    simp [counterSourceReverseStepBank, hsd, hsi, List.reverse_cons, List.append_assoc]

theorem counterSourceTrace_index (R : Fin T → List (Fin (A + 4))) (rg : Fin 5 → Fin T)
    (count saved dst : Fin T) (L i : ℕ) (input : List (Fin (A + 4)))
    (hi : R (rg 0) = binSyms L i) :
    counterSourceTraceBank R rg count saved dst L i input (rg 0) = binSyms L (i + input.length) := by
  induction input generalizing R i with
  | nil => simpa [counterSourceTraceBank] using hi
  | cons x rest ih =>
    have hh := ih
      (counterSourceReverseStepBank (Function.update (Function.update R count rest) saved (x :: R saved))
        rg dst L i) (i + 1) (by simp [counterSourceReverseStepBank])
    simpa only [counterSourceTraceBank, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hh

def counterSourceClosedBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 5 → Fin T) (count saved dst : Fin T)
    (L i : ℕ) (input : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update (Function.update R count []) saved (input.reverse ++ R saved))
    dst ((counterSourceWord L i input.length).reverse ++ R dst)) (rg 0) (binSyms L (i + input.length))

theorem counterSourceTrace_closed (R : Fin T → List (Fin (A + 4))) (rg : Fin 5 → Fin T)
    (count saved dst : Fin T) (hcs : count ≠ saved) (hcd : count ≠ dst) (hsd : saved ≠ dst)
    (hci : count ≠ rg 0) (hsi : saved ≠ rg 0) (hdi : dst ≠ rg 0)
    (L i : ℕ) (input : List (Fin (A + 4)))
    (hc : R count = input) (hi : R (rg 0) = binSyms L i) :
    counterSourceTraceBank R rg count saved dst L i input =
      counterSourceClosedBank R rg count saved dst L i input := by
  funext j
  by_cases hj : j = rg 0
  · subst j
    simp only [counterSourceClosedBank, Function.update_self]
    exact counterSourceTrace_index R rg count saved dst L i input hi
  · by_cases hd : j = dst
    · subst j
      simp only [counterSourceClosedBank, Function.update_of_ne hdi, Function.update_self]
      exact counterSourceTrace_output R rg count saved dst hcd.symm hsd.symm hdi L i input
    · by_cases hs : j = saved
      · subst j
        simp only [counterSourceClosedBank, Function.update_of_ne hsi, Function.update_of_ne hsd, Function.update_self]
        exact counterSourceTrace_saved R rg count saved dst hcs.symm hsd hsi L i input
      · by_cases hcj : j = count
        · subst j
          simp only [counterSourceClosedBank, Function.update_of_ne hci, Function.update_of_ne hcd, Function.update_of_ne hcs, Function.update_self]
          exact counterSourceTrace_count R rg count saved dst hcs hcd hci L i input hc
        · simp only [counterSourceClosedBank, Function.update_of_ne hj, Function.update_of_ne hd,
            Function.update_of_ne hs, Function.update_of_ne hcj]
          exact counterSourceTrace_keep R rg count saved dst L i input j hcj hs hd hj

end IntegerMultBounds.MathlibTM2.Routing
