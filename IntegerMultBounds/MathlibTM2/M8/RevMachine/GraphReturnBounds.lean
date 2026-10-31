module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
public import IntegerMultBounds.Machine.RunInvariant

/-! Every reachable return-pop configuration has constant-code-width head
bounds. At halt, the actual stored address determines the controller edge. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
open IntegerMultBounds.Machine Graph SharedBankStageInput SharedPlacementAlphabet
noncomputable section
variable {Seg Call : Type} {t a k : ℕ} (pieces : List (Piece Seg Call))
  (capacity : Fintype.card (PC pieces.length) ≤ 2^k) (stack : Fin t) (ht : 0 < t)
  (impl : Implementation t a k Seg Call)

theorem pop_reachable_post (pc : PC pieces.length) (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hs : v.tape stack = FiniteReturnStack.wordPart f p
      (FiniteReturnStack.address capacity (encoding pieces pc)) k le_rfl)
    (hh : v.head stack = p+k) (hf : ∀ j < k, f (p+j) = blank)
    {c : Config (tapeCount pieces capacity stack ht impl)
      (states pieces capacity stack ht impl (encoding pieces .pop)) a}
    (hc : RunInvariant (family pieces capacity stack ht impl (encoding pieces .pop))
      (· = raw v (tapeCount pieces capacity stack ht impl)) c)
    (hhalt : Machine.step (family pieces capacity stack ht impl (encoding pieces .pop)) c = none) :
    c.tapes = raw (setTape v stack f p) (tapeCount pieces capacity stack ht impl) ∧
      next pieces capacity stack ht impl (encoding pieces .pop) c.state = some (encoding pieces pc) := by
  apply RunInvariant.post_config (post := fun z =>
    z.tapes = raw (setTape v stack f p) (tapeCount pieces capacity stack ht impl) ∧
      next pieces capacity stack ht impl (encoding pieces .pop) z.state = some (encoding pieces pc)) ?_ hc hhalt
  intro w hw
  subst w
  obtain ⟨z,hr,hz,htapes,hedge⟩ := pop_block pieces capacity stack ht impl pc v f p hs hh hf
  exact ⟨k+1,z,hr,hz,htapes,hedge⟩

theorem pop_reachable_heads (pc : PC pieces.length) (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hs : v.tape stack = FiniteReturnStack.wordPart f p
      (FiniteReturnStack.address capacity (encoding pieces pc)) k le_rfl)
    (hh : v.head stack = p+k) (hf : ∀ j < k, f (p+j) = blank)
    {c : Config (tapeCount pieces capacity stack ht impl)
      (states pieces capacity stack ht impl (encoding pieces .pop)) a}
    (hc : RunInvariant (family pieces capacity stack ht impl (encoding pieces .pop))
      (· = raw v (tapeCount pieces capacity stack ht impl)) c) :
    ∀ i, (raw v (tapeCount pieces capacity stack ht impl)).head i-(k+1 : ℕ) ≤ c.head i ∧
      c.head i ≤ (raw v (tapeCount pieces capacity stack ht impl)).head i+(k+1 : ℕ) := by
  have h : HoareTime (family pieces capacity stack ht impl (encoding pieces .pop))
      (· = raw v (tapeCount pieces capacity stack ht impl))
      (· = raw (setTape v stack f p) (tapeCount pieces capacity stack ht impl)) (k+1) := by
    intro w hw
    subst w
    obtain ⟨z,hr,hz,htapes,_⟩ := pop_block pieces capacity stack ht impl pc v f p hs hh hf
    exact ⟨k+1,z,le_rfl,hr,hz,htapes⟩
  exact hc.heads_eq h

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphRun
