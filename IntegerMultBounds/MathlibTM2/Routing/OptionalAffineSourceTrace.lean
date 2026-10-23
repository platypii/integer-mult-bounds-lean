module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceLoopFrame

/-! Closed count, archive and index contents after affine source generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

theorem optionalAffineSourceTrace_count (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (src saved dst : Fin T) (hcs : src ≠ saved) (hcd : src ≠ dst) (hci : src ≠ rg 0)
    (Li Lk i k o : ℕ) (input : List Bool) (hc : R src = input.map bitSymbol) :
    optionalAffineSourceTraceBank R rg src saved dst Li Lk i k o input src = [] := by
  induction input generalizing R i with
  | nil => exact hc
  | cons x rest ih =>
    apply ih
    simp [optionalAffineSourceReverseStepBank, hcs, hcd, hci]

theorem optionalAffineSourceTrace_saved (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (src saved dst : Fin T) (_hsc : saved ≠ src) (hsd : saved ≠ dst) (hsi : saved ≠ rg 0)
    (Li Lk i k o : ℕ) (input : List Bool) :
    optionalAffineSourceTraceBank R rg src saved dst Li Lk i k o input saved = (input.map bitSymbol).reverse ++ R saved := by
  induction input generalizing R i with
  | nil => simp [optionalAffineSourceTraceBank]
  | cons x rest ih =>
    rw [optionalAffineSourceTraceBank, ih]
    simp [optionalAffineSourceReverseStepBank, hsd, hsi, List.reverse_cons, List.append_assoc]

theorem optionalAffineSourceTrace_index (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (src saved dst : Fin T) (Li Lk i k o : ℕ) (input : List Bool)
    (hi : R (rg 0) = binSyms Li i) :
    optionalAffineSourceTraceBank R rg src saved dst Li Lk i k o input (rg 0) = binSyms Li (i + input.length) := by
  induction input generalizing R i with
  | nil => simpa [optionalAffineSourceTraceBank] using hi
  | cons x rest ih =>
    have hh := ih
      (optionalAffineSourceReverseStepBank R rg src saved dst Li Lk i k o x (rest.map bitSymbol)) (i + 1) (by simp [optionalAffineSourceReverseStepBank])
    simpa only [optionalAffineSourceTraceBank, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hh

def optionalAffineSourceClosedBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T) (src saved dst : Fin T)
    (Li Lk i k o : ℕ) (input : List Bool) :=
  Function.update (Function.update (Function.update (Function.update R src []) saved ((input.map bitSymbol).reverse ++ R saved))
    dst ((optionalAffineSourceWord Li Lk i k o input).reverse ++ R dst)) (rg 0) (binSyms Li (i + input.length))

theorem optionalAffineSourceTrace_closed (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (src saved dst : Fin T) (hcs : src ≠ saved) (hcd : src ≠ dst) (hsd : saved ≠ dst)
    (hci : src ≠ rg 0) (hsi : saved ≠ rg 0) (hdi : dst ≠ rg 0)
    (Li Lk i k o : ℕ) (input : List Bool)
    (hc : R src = input.map bitSymbol) (hi : R (rg 0) = binSyms Li i) :
    optionalAffineSourceTraceBank R rg src saved dst Li Lk i k o input =
      optionalAffineSourceClosedBank R rg src saved dst Li Lk i k o input := by
  funext j
  by_cases hj : j = rg 0
  · subst j
    simp only [optionalAffineSourceClosedBank, Function.update_self]
    exact optionalAffineSourceTrace_index R rg src saved dst Li Lk i k o input hi
  · by_cases hd : j = dst
    · subst j
      simp only [optionalAffineSourceClosedBank, Function.update_of_ne hdi, Function.update_self]
      exact optionalAffineSourceTrace_output R rg src saved dst hcd.symm hsd.symm hdi Li Lk i k o input
    · by_cases hs : j = saved
      · subst j
        simp only [optionalAffineSourceClosedBank, Function.update_of_ne hsi, Function.update_of_ne hsd, Function.update_self]
        exact optionalAffineSourceTrace_saved R rg src saved dst hcs.symm hsd hsi Li Lk i k o input
      · by_cases hcj : j = src
        · subst j
          simp only [optionalAffineSourceClosedBank, Function.update_of_ne hci, Function.update_of_ne hcd, Function.update_of_ne hcs, Function.update_self]
          exact optionalAffineSourceTrace_count R rg src saved dst hcs hcd hci Li Lk i k o input hc
        · simp only [optionalAffineSourceClosedBank, Function.update_of_ne hj, Function.update_of_ne hd,
            Function.update_of_ne hs, Function.update_of_ne hcj]
          exact optionalAffineSourceTrace_keep R rg src saved dst Li Lk i k o input j hcj hs hd hj

end IntegerMultBounds.MathlibTM2.Routing
