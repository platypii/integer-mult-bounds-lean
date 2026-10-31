module

public import IntegerMultBounds.Machine.HoareWithinPlacement
public import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! A bounded run shares one caller tape physically, retaining all other
caller tapes and the cleared private source at their exact endpoints. -/
@[expose] public section
namespace IntegerMultBounds.Machine.SharedPlacementAlphabet
variable {a l r states cost : ℕ} {M : Program r states a} {w w' : Tapes r a} {lo hi : ℤ}

theorem shared_within
    (h : HoareWithin M (· = w) (· = w') cost (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi))
    (v : Tapes l a) (i : Fin l) (j : Fin r) (spare : ℤ → Fin (a+4)) (spareHead : ℤ)
    (hf : v.tape i = w.tape j) (hp : v.head i = w.head j)
    (hwhole : ∀ k, lo ≤ (v.append (setTape w j spare spareHead)).head k ∧
      (v.append (setTape w j spare spareHead)).head k ≤ hi) :
    HoareWithin (Placement.placed M (sharedPlacement i j))
      (· = v.append (setTape w j spare spareHead))
      (· = (setTape v i (w'.tape j) (w'.head j)).append (setTape w' j spare spareHead)) cost
      (fun z => ∀ k, lo ≤ z.head k ∧ z.head k ≤ hi) := by
  have ha : Placement.active (sharedPlacement i j) (v.append (setTape w j spare spareHead)) = w := by
    rw [active_shared,hf,hp,setTape_setTape,setTape_self]
  have hh := HoareWithin.placed_heads_at h (sharedPlacement i j) _ ha (by
    intro k
    exact hwhole (sharedPlacement i j (Fin.natAdd r k)))
  apply hh.consequence (fun _ h => h) _ le_rfl (fun _ h => h)
  rintro x ⟨y,rfl,rfl⟩
  rw [replace_shared]
  simp only [setTape,Function.update_self]

end IntegerMultBounds.Machine.SharedPlacementAlphabet
