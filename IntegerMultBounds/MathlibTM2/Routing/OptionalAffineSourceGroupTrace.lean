module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceGroupLoopFrame

/-! Closed count, archive and index contents after affine source generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

theorem optionalAffineSourceGroupTrace_count (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T) (rp : Fin 7 → Fin T)
    (src saved dst : Fin T) (hcs : src ≠ saved) (hcd : src ≠ dst) (hci : src ≠ rg 0)
    (Li Lk i k o g : ℕ) (input : List Bool) (hc : R src = input.map bitSymbol) :
    optionalAffineSourceGroupTraceBank R rg rp src saved dst Li Lk i k o g input src = [] := by
  induction input generalizing R i with
  | nil => exact hc
  | cons x rest ih =>
    apply ih
    simp [optionalAffineSourceGroupReverseBank, hcs, hcd, hci]

theorem optionalAffineSourceGroupTrace_saved (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T) (rp : Fin 7 → Fin T)
    (src saved dst : Fin T) (_hsc : saved ≠ src) (hsd : saved ≠ dst) (hsi : saved ≠ rg 0)
    (Li Lk i k o g : ℕ) (input : List Bool) :
    optionalAffineSourceGroupTraceBank R rg rp src saved dst Li Lk i k o g input saved = (input.map bitSymbol).reverse ++ R saved := by
  induction input generalizing R i with
  | nil => simp [optionalAffineSourceGroupTraceBank]
  | cons x rest ih =>
    rw [optionalAffineSourceGroupTraceBank, ih]
    simp [optionalAffineSourceGroupReverseBank, hsd, hsi, List.reverse_cons, List.append_assoc]

theorem optionalAffineSourceGroupTrace_index (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T) (rp : Fin 7 → Fin T)
    (src saved dst : Fin T) (Li Lk i k o g : ℕ) (input : List Bool)
    (hi : R (rg 0) = binSyms Li i) :
    optionalAffineSourceGroupTraceBank R rg rp src saved dst Li Lk i k o g input (rg 0) = binSyms Li (i + input.length) := by
  induction input generalizing R i with
  | nil => simpa [optionalAffineSourceGroupTraceBank] using hi
  | cons x rest ih =>
    have hh := ih
      (optionalAffineSourceGroupReverseBank R rg rp src saved dst Li Lk i k o g x (rest.map bitSymbol)) (i + 1) (by simp [optionalAffineSourceGroupReverseBank])
    simpa only [optionalAffineSourceGroupTraceBank, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hh

def optionalAffineSourceGroupClosedBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T) (_rp : Fin 7 → Fin T) (src saved dst : Fin T)
    (Li Lk i k o g : ℕ) (input : List Bool) :=
  Function.update (Function.update (Function.update (Function.update R src []) saved ((input.map bitSymbol).reverse ++ R saved))
    dst ((optionalAffineSourceGroupWord Li Lk i k o g input).reverse ++ R dst)) (rg 0) (binSyms Li (i + input.length))

theorem optionalAffineSourceGroupTrace_closed (R : Fin T → List (Fin (A + 4))) (rg : Fin 12 → Fin T) (rp : Fin 7 → Fin T)
    (src saved dst : Fin T) (hcs : src ≠ saved) (hcd : src ≠ dst) (hsd : saved ≠ dst)
    (hci : src ≠ rg 0) (hsi : saved ≠ rg 0) (hdi : dst ≠ rg 0)
    (Li Lk i k o g : ℕ) (input : List Bool)
    (hc : R src = input.map bitSymbol) (hi : R (rg 0) = binSyms Li i) :
    optionalAffineSourceGroupTraceBank R rg rp src saved dst Li Lk i k o g input =
      optionalAffineSourceGroupClosedBank R rg rp src saved dst Li Lk i k o g input := by
  funext j
  by_cases hj : j = rg 0
  · subst j
    simp only [optionalAffineSourceGroupClosedBank, Function.update_self]
    exact optionalAffineSourceGroupTrace_index R rg rp src saved dst Li Lk i k o g input hi
  · by_cases hd : j = dst
    · subst j
      simp only [optionalAffineSourceGroupClosedBank, Function.update_of_ne hdi, Function.update_self]
      exact optionalAffineSourceGroupTrace_output R rg rp src saved dst hcd.symm hsd.symm hdi Li Lk i k o g input
    · by_cases hs : j = saved
      · subst j
        simp only [optionalAffineSourceGroupClosedBank, Function.update_of_ne hsi, Function.update_of_ne hsd, Function.update_self]
        exact optionalAffineSourceGroupTrace_saved R rg rp src saved dst hcs.symm hsd hsi Li Lk i k o g input
      · by_cases hcj : j = src
        · subst j
          simp only [optionalAffineSourceGroupClosedBank, Function.update_of_ne hci, Function.update_of_ne hcd, Function.update_of_ne hcs, Function.update_self]
          exact optionalAffineSourceGroupTrace_count R rg rp src saved dst hcs hcd hci Li Lk i k o g input hc
        · simp only [optionalAffineSourceGroupClosedBank, Function.update_of_ne hj, Function.update_of_ne hd,
            Function.update_of_ne hs, Function.update_of_ne hcj]
          exact optionalAffineSourceGroupTrace_keep R rg rp src saved dst Li Lk i k o g input j hcj hs hd hj

end IntegerMultBounds.MathlibTM2.Routing
