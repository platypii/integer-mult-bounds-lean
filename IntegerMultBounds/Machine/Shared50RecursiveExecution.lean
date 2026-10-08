import IntegerMultBounds.Machine.Shared50RecursiveControl
import IntegerMultBounds.Machine.SharedBankFamilyExact

/-! Actual entry transitions of the padded Shared50 cyclic machine. The width
guard's terminal finite state selects the next block without changing any tape.
The recursive and base implementations still require their own contracts. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveExecution
open Classical
open Shared50RecursiveControl SharedBankFamilyExact SharedBankStageInput
variable {t a k : ℕ}
noncomputable section

private theorem raw_self (v : Tapes t a) : raw v t = v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [dite_eq_left i.isLt]

def branch (width : ℕ) : PC := if width = 1 then .base else .split

/-- The actual padded guard preserves the full bank and exposes its selected
edge in the compiled finite table. -/
theorem guard_block (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) (v : Tapes t a) (bs : List Bool)
    (hh : v.head width = 1) (ht : v.tape width = BinaryDescriptorStack.descriptor bs)
    (hc : GrowingCounterData.Canonical bs) :
    ∃ steps ≤ 2, ∃ c : Config (tapeCount capacity width stack impl)
      (states capacity width stack impl (encoding .guard)) a,
      run (family capacity width stack impl (encoding .guard)) steps
        ((raw v (tapeCount capacity width stack impl)).start (family capacity width stack impl (encoding .guard))) = some c ∧
      step (family capacity width stack impl (encoding .guard)) c = none ∧
      c.tapes = raw v (tapeCount capacity width stack impl) ∧
      next capacity width stack impl (encoding .guard) c.state = some (encoding (branch (Counter.value bs))) := by
  obtain ⟨steps,hs,hr,hhalt⟩ := RecursiveWidthGuard.canonical_exact width v bs hh ht hc
  let finish : Fin 4 := if Counter.value bs = 1 then RecursiveWidthGuard.base else RecursiveWidthGuard.recurse
  have hp := SharedBankFamilyExact.pad_exact (RecursiveWidthGuard.program (a := a) width)
    (SharedBankFamily.common_le_tapeCount (block capacity width stack impl)) (le_refl t)
    v v steps finish (by simpa only [raw_self,atState,finish,RecursiveWidthGuard.cfg] using hr)
    (by simpa only [raw_self,atState,finish,RecursiveWidthGuard.cfg] using hhalt)
  have he : encoding.symm (encoding PC.guard) = PC.guard := encoding.symm_apply_apply _
  unfold states family next tapeCount
  rw [he]
  refine ⟨steps,hs,atState (raw v (tapeCount capacity width stack impl)) finish,hp.1,hp.2,rfl,?_⟩
  change (edge capacity width stack impl .guard finish).map encoding = _
  have hne : RecursiveWidthGuard.recurse ≠ RecursiveWidthGuard.base := by
    intro h
    have hv := congrArg Fin.val h
    change (3 : ℕ) = 2 at hv
    omega
  by_cases hb : Counter.value bs = 1 <;>
    simp only [edge,block,SharedBankFamily.ofProgram,finish,branch,hb,ite_true,ite_false,
      hne,Option.map_some]

/-- Guard execution and its actual finite-flow jump cost at most three
transitions, entering the selected real block on the unchanged padded bank. -/
theorem guard_jump (capacity : Fintype.card PC ≤ 2^k) (width stack : Fin t)
    (impl : Implementation t a k) (v : Tapes t a) (bs : List Bool)
    (hh : v.head width = 1) (ht : v.tape width = BinaryDescriptorStack.descriptor bs)
    (hc : GrowingCounterData.Canonical bs) :
    ∃ steps ≤ 3, run (program capacity width stack impl) steps
      ((raw v (tapeCount capacity width stack impl)).start (program capacity width stack impl)) =
      some (((raw v (tapeCount capacity width stack impl)).start
        (family capacity width stack impl (encoding (branch (Counter.value bs))))).mapState
        (FiniteFlow.embed (states capacity width stack impl) (encoding (branch (Counter.value bs))))) := by
  obtain ⟨steps,hs,c,hr,hhalt,hbank,hedge⟩ := guard_block capacity width stack impl v bs hh ht hc
  have hj := FiniteFlow.block_then_jump (family capacity width stack impl) (next capacity width stack impl)
    (encoding .guard) (encoding .guard) (encoding (branch (Counter.value bs)))
    (raw v (tapeCount capacity width stack impl)) steps c hr hhalt hedge
  rw [hbank] at hj
  exact ⟨steps+1,by omega,hj⟩

end
end IntegerMultBounds.Machine.Shared50RecursiveExecution
