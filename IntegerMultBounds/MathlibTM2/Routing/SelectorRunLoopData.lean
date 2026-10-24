module

public import IntegerMultBounds.MathlibTM2.Routing.SelectorRunStep
public import IntegerMultBounds.MathlibTM2.Routing.SparseSelectorRuns

/-! Input, price and bank composition for the fixed sparse selector loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Host

variable {T A W : ℕ}

def selectorRunFrames (Lg L : ℕ) : List (SparseSelectorRun W) → List (Fin (A + 4))
  | [] => []
  | run :: runs => binSyms Lg run.gap ++ separator ::
      (binSyms L run.selector.val ++ separator :: selectorRunFrames Lg L runs)

def selectorRunLoopCost (Lg L : ℕ) : List (SparseSelectorRun W) → ℕ
  | [] => 1
  | run :: runs => ((4 * Lg + 4 * L + 12) + (6 * L + 8) +
      binaryWordRepeatCost Lg run.gap (L + 1) + (2 * Lg + 2 * L + 5)) +
      selectorRunLoopCost Lg L runs + 2

/-- The sparse loop pays once per entry and once per skipped coordinate. -/
theorem selectorRunLoopCost_eq (Lg L : ℕ) (runs : List (SparseSelectorRun W)) :
    selectorRunLoopCost Lg L runs =
      runs.length * (17 * Lg + 12 * L + 39) +
        (runs.map (fun run => run.gap)).sum * (4 * Lg + 6 * L + 21) + 1 := by
  induction runs with
  | nil => simp [selectorRunLoopCost]
  | cons run runs ih =>
      simp only [selectorRunLoopCost, ih, List.length_cons, List.map_cons, List.sum_cons,
        binaryWordRepeatCost]
      ring

theorem selectorRunLoopCost_reverse (Lg L : ℕ) (runs : List (SparseSelectorRun W)) :
    selectorRunLoopCost Lg L runs.reverse = selectorRunLoopCost Lg L runs := by
  simp [selectorRunLoopCost_eq, List.map_reverse]

def selectorRunLoopBank (R : Fin T → List (Fin (A + 4))) (rg : SelectorRunReg → Fin T)
    (Lg L : ℕ) (runs : List (SparseSelectorRun W)) :=
  Function.update (Function.update (Function.update R (rg .src) [])
    (rg .archive) ((selectorRunFrames Lg L runs).reverse ++ R (rg .archive)))
    (rg .dst) (descriptorSelectorFrames L (SparseSelectorRun.expand runs.reverse) ++ R (rg .dst))

theorem selectorRunFrames_cons_ne_nil (Lg L : ℕ) (run : SparseSelectorRun W) (runs : List (SparseSelectorRun W)) :
    selectorRunFrames (A := A) Lg L (run :: runs) ≠ [] := by
  intro he
  have hl := congrArg List.length he
  simp [selectorRunFrames] at hl

theorem selectorRunLoopBank_nil (R : Fin T → List (Fin (A + 4))) (rg : SelectorRunReg → Fin T)
    (hrg : Function.Injective rg) (Lg L : ℕ) (hsrc : R (rg .src) = []) :
    selectorRunLoopBank R rg Lg L ([] : List (SparseSelectorRun W)) = R := by
  funext j
  by_cases hs : j = rg .src
  · subst j; simp [selectorRunLoopBank, selectorRunFrames, SparseSelectorRun.expand, descriptorSelectorFrames, hrg.eq_iff, hsrc]
  · by_cases ha : j = rg .archive
    · subst j; simp [selectorRunLoopBank, selectorRunFrames, SparseSelectorRun.expand, descriptorSelectorFrames, hrg.eq_iff]
    · by_cases hd : j = rg .dst
      · subst j; simp [selectorRunLoopBank, selectorRunFrames, SparseSelectorRun.expand, descriptorSelectorFrames]
      · simp [selectorRunLoopBank, hs, ha, hd]

theorem selectorRunLoopBank_step (R : Fin T → List (Fin (A + 4))) (rg : SelectorRunReg → Fin T)
    (hrg : Function.Injective rg) (Lg L : ℕ) (run : SparseSelectorRun W) (runs : List (SparseSelectorRun W)) :
    selectorRunLoopBank (selectorRunStepBank R rg Lg L run.gap run.selector (selectorRunFrames Lg L runs)) rg Lg L runs =
      selectorRunLoopBank R rg Lg L (run :: runs) := by
  funext j
  by_cases hd : j = rg .dst
  · subst j
    simp [selectorRunLoopBank, selectorRunStepBank, List.reverse_cons, SparseSelectorRun.expand_append,
      SparseSelectorRun.expand, SparseSelectorRun.indices, descriptorSelectorFrames_append, List.append_assoc]
  · by_cases ha : j = rg .archive
    · subst j
      simp [selectorRunLoopBank, selectorRunStepBank, selectorRunFrames, hrg.eq_iff,
        List.reverse_append, List.append_assoc]
    · by_cases hs : j = rg .src
      · subst j; simp [selectorRunLoopBank, selectorRunStepBank, hrg.eq_iff]
      · simp [selectorRunLoopBank, selectorRunStepBank, hd, ha, hs]

end IntegerMultBounds.MathlibTM2.Routing
