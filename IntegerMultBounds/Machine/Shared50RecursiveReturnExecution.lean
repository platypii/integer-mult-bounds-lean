import IntegerMultBounds.Machine.Shared50RecursiveExecution

/-! Actual return-stack decoding in the uniformly padded recursive graph.
The erased frame and decoded finite state are both retained in the contract. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveReturnExecution
open Shared50RecursiveControl SharedBankFamilyExact SharedBankStageInput
open SharedPlacementAlphabet (setTape)
variable {t a k : ℕ}
noncomputable section

private theorem raw_self (v : Tapes t a) : raw v t = v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [dite_eq_left i.isLt]

/-- Placing the decoder preserves its exact terminal state as well as all
spectator tapes, while physically erasing the return frame. -/
theorem placed_pop (slot : Fin t) (code : FiniteReturnStack.Code k)
    (v : Tapes t a) (f : ℤ → Fin (a+4)) (p : ℤ)
    (hs : v.tape slot = FiniteReturnStack.wordPart f p code k le_rfl)
    (hh : v.head slot = p+k) (hf : ∀ j < k, f (p+j) = blank) :
    let M := Placement.placed (FiniteReturnStack.pop a k) (FiniteReturnStackAt.placement slot)
    let c := atState (setTape v slot f p) (FiniteReturnStack.encode k (.inr (0,code)))
    run M (k+1) (v.start M) = some c ∧ step M c = none := by
  obtain ⟨hr,hhalt⟩ := FiniteReturnStack.pop_exact code f p hf
  let e := FiniteReturnStackAt.placement slot
  let c := FiniteReturnStack.cfg (.inr (0,code)) f p
  have hr' : run (FiniteReturnStack.pop a k) (k+1)
      ((Placement.active e v).start (FiniteReturnStack.pop a k)) = some c := by
    rw [FiniteReturnStackAt.active_bank,hs,hh]
    exact hr
  have he : Placement.result e v c =
      atState (setTape v slot f p) (FiniteReturnStack.encode k (.inr (0,code))) := by
    have ht : (Placement.result e v c).tapes = setTape v slot f p :=
      FiniteReturnStackAt.replace_bank slot v f p
    have hh := congrArg Tapes.head ht
    have hf := congrArg Tapes.tape ht
    exact congrArg₂ (Config.mk (FiniteReturnStack.encode k (.inr (0,code)))) hh hf
  exact ⟨he ▸ Placement.placed_run _ e v hr',he ▸ Placement.placed_halt _ e v hhalt⟩

/-- The real padded pop block restores the older stack and selects the actual
encoded return address in exactly k+1 transitions. -/
theorem pop_block (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) (pc : PC) (v : Tapes t a)
    (f : ℤ → Fin (a+4)) (p : ℤ)
    (hs : v.tape stack = FiniteReturnStack.wordPart f p
      (FiniteReturnStack.address capacity (encoding pc)) k le_rfl)
    (hh : v.head stack = p+k) (hf : ∀ j < k, f (p+j) = blank) :
    ∃ c : Config (tapeCount capacity width stack impl)
      (states capacity width stack impl (encoding .pop)) a,
      run (family capacity width stack impl (encoding .pop)) (k+1)
        ((raw v (tapeCount capacity width stack impl)).start (family capacity width stack impl (encoding .pop))) = some c ∧
      step (family capacity width stack impl (encoding .pop)) c = none ∧
      c.tapes = raw (setTape v stack f p) (tapeCount capacity width stack impl) ∧
      next capacity width stack impl (encoding .pop) c.state = some (encoding pc) := by
  obtain ⟨hr,hhalt⟩ := placed_pop stack (FiniteReturnStack.address capacity (encoding pc)) v f p hs hh hf
  let finish := FiniteReturnStack.encode k (.inr (0,FiniteReturnStack.address capacity (encoding pc)))
  have hp := SharedBankFamilyExact.pad_exact
    (Placement.placed (FiniteReturnStack.pop a k) (FiniteReturnStackAt.placement stack))
    (SharedBankFamily.common_le_tapeCount (block capacity width stack impl)) (le_refl t)
    v (setTape v stack f p) (k+1) finish (by simpa only [raw_self] using hr)
    (by simpa only [raw_self] using hhalt)
  have he : encoding.symm (encoding PC.pop) = PC.pop := encoding.symm_apply_apply _
  unfold states family next tapeCount
  rw [he]
  refine ⟨atState (raw (setTape v stack f p) (tapeCount capacity width stack impl)) finish,
    hp.1,hp.2,rfl,?_⟩
  change ((FiniteReturnDispatch.select capacity finish).map encoding.symm).map encoding = _
  rw [FiniteReturnDispatch.select_return]
  simp only [Option.map_some,Equiv.symm_apply_apply]

/-- The pop and its real controller edge consume k+2 transitions. This applies
both to a child recovery address and to the root halt sentinel. -/
theorem pop_jump (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) (pc : PC) (v : Tapes t a)
    (f : ℤ → Fin (a+4)) (p : ℤ)
    (hs : v.tape stack = FiniteReturnStack.wordPart f p
      (FiniteReturnStack.address capacity (encoding pc)) k le_rfl)
    (hh : v.head stack = p+k) (hf : ∀ j < k, f (p+j) = blank) :
    run (program capacity width stack impl) (k+2)
      (((raw v (tapeCount capacity width stack impl)).start
        (family capacity width stack impl (encoding .pop))).mapState
          (FiniteFlow.embed (states capacity width stack impl) (encoding .pop))) =
      some (((raw (setTape v stack f p) (tapeCount capacity width stack impl)).start
        (family capacity width stack impl (encoding pc))).mapState
          (FiniteFlow.embed (states capacity width stack impl) (encoding pc))) := by
  obtain ⟨c,hr,hhalt,hbank,hedge⟩ := pop_block capacity width stack impl pc v f p hs hh hf
  have hj := FiniteFlow.block_then_jump (family capacity width stack impl) (next capacity width stack impl)
    (encoding .guard) (encoding .pop) (encoding pc)
    (raw v (tapeCount capacity width stack impl)) (k+1) c hr hhalt hedge
  rw [hbank] at hj
  exact hj

end
end IntegerMultBounds.Machine.Shared50RecursiveReturnExecution
