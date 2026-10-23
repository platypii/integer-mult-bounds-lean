module

public import IntegerMultBounds.MathlibTM2.Routing.AffineSourceLoopFrame

/-! Closed count, archive and index contents after affine source generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

theorem affineSourceTrace_count (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (count saved dst : Fin T) (hcs : count ≠ saved) (hcd : count ≠ dst) (hci : count ≠ rg 0)
    (Li Lk i k o : ℕ) (input : List (Fin (A + 4))) (hc : R count = input) :
    affineSourceTraceBank R rg count saved dst Li Lk i k o input count = [] := by
  induction input generalizing R i with
  | nil => exact hc
  | cons x rest ih =>
    apply ih
    simp [affineSourceReverseStepBank, hcs, hcd, hci]

theorem affineSourceTrace_saved (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (count saved dst : Fin T) (_hsc : saved ≠ count) (hsd : saved ≠ dst) (hsi : saved ≠ rg 0)
    (Li Lk i k o : ℕ) (input : List (Fin (A + 4))) :
    affineSourceTraceBank R rg count saved dst Li Lk i k o input saved = input.reverse ++ R saved := by
  induction input generalizing R i with
  | nil => simp [affineSourceTraceBank]
  | cons x rest ih =>
    rw [affineSourceTraceBank, ih]
    simp [affineSourceReverseStepBank, hsd, hsi, List.reverse_cons, List.append_assoc]

theorem affineSourceTrace_index (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (count saved dst : Fin T) (Li Lk i k o : ℕ) (input : List (Fin (A + 4)))
    (hi : R (rg 0) = binSyms Li i) :
    affineSourceTraceBank R rg count saved dst Li Lk i k o input (rg 0) = binSyms Li (i + input.length) := by
  induction input generalizing R i with
  | nil => simpa [affineSourceTraceBank] using hi
  | cons x rest ih =>
    have hh := ih
      (affineSourceReverseStepBank (Function.update (Function.update R count rest) saved (x :: R saved))
        rg dst Li Lk i k o) (i + 1) (by simp [affineSourceReverseStepBank])
    simpa only [affineSourceTraceBank, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hh

def affineSourceClosedBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T) (count saved dst : Fin T)
    (Li Lk i k o : ℕ) (input : List (Fin (A + 4))) :=
  Function.update (Function.update (Function.update (Function.update R count []) saved (input.reverse ++ R saved))
    dst ((affineSourceWord Li Lk i k o input.length).reverse ++ R dst)) (rg 0) (binSyms Li (i + input.length))

theorem affineSourceTrace_closed (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T)
    (count saved dst : Fin T) (hcs : count ≠ saved) (hcd : count ≠ dst) (hsd : saved ≠ dst)
    (hci : count ≠ rg 0) (hsi : saved ≠ rg 0) (hdi : dst ≠ rg 0)
    (Li Lk i k o : ℕ) (input : List (Fin (A + 4)))
    (hc : R count = input) (hi : R (rg 0) = binSyms Li i) :
    affineSourceTraceBank R rg count saved dst Li Lk i k o input =
      affineSourceClosedBank R rg count saved dst Li Lk i k o input := by
  funext j
  by_cases hj : j = rg 0
  · subst j
    simp only [affineSourceClosedBank, Function.update_self]
    exact affineSourceTrace_index R rg count saved dst Li Lk i k o input hi
  · by_cases hd : j = dst
    · subst j
      simp only [affineSourceClosedBank, Function.update_of_ne hdi, Function.update_self]
      exact affineSourceTrace_output R rg count saved dst hcd.symm hsd.symm hdi Li Lk i k o input
    · by_cases hs : j = saved
      · subst j
        simp only [affineSourceClosedBank, Function.update_of_ne hsi, Function.update_of_ne hsd, Function.update_self]
        exact affineSourceTrace_saved R rg count saved dst hcs.symm hsd hsi Li Lk i k o input
      · by_cases hcj : j = count
        · subst j
          simp only [affineSourceClosedBank, Function.update_of_ne hci, Function.update_of_ne hcd, Function.update_of_ne hcs, Function.update_self]
          exact affineSourceTrace_count R rg count saved dst hcs hcd hci Li Lk i k o input hc
        · simp only [affineSourceClosedBank, Function.update_of_ne hj, Function.update_of_ne hd,
            Function.update_of_ne hs, Function.update_of_ne hcj]
          exact affineSourceTrace_keep R rg count saved dst Li Lk i k o input j hcj hs hd hj

end IntegerMultBounds.MathlibTM2.Routing
