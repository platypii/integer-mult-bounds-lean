import IntegerMultBounds.Machine.RecursiveChildSetupRoleBank
import IntegerMultBounds.Machine.RecursiveChildCallReturn
import IntegerMultBounds.Machine.RecursiveHeaderRestore

/-! Physical ancestor-header restoration and decoded PC return on permanent
role tapes. Exact continuation terminal states remain visible for finite flow. -/
namespace IntegerMultBounds.Machine.RecursiveChildReturnRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveShiftRoleBank (common)
open RecursiveChildCallSetup (savedStacks)
open RecursiveChildCallReturn (pending cost)
open SharedPlacementAlphabet (setTape)
open FiniteReturnStack (address)
variable {t u k N : ℕ}

abbrev TapeCount (t u : ℕ) := t+(7+(u+2))+40
abbrev restoreStates := (fun {t s a : ℕ} (_ : Program t s a) => s) (RecursiveChildCallReturn.program (q := prime))

def bank (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime) (st : Tapes 2 prime) :
    Tapes (TapeCount t u) prime := CleanSubbank.bank (common roles hs (aux.append st))

def pcSlot : Fin (TapeCount t u) :=
  Fin.castAdd 40 (Fin.natAdd t (Fin.natAdd 7 (Fin.natAdd u (1 : Fin 2))))

def restoreProgram : Program (TapeCount t u) restoreStates prime :=
  Placement.placed RecursiveChildCallReturn.program
    (CleanSubbank.placement RecursiveChildSetupRoleBank.ports RecursiveChildSetupRoleBank.commonPorts
      RecursiveChildSetupRoleBank.commonPorts_injective)

theorem restores (roles : Tapes t prime) (old hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (st : Tapes 2 prime) (code : FiniteReturnStack.Code k) (hd : RecursiveStackAllocation.Available 0 st) :
    HoareTime (restoreProgram (t := t) (u := u))
      (fun w => w = bank roles hs aux (savedStacks old st code))
      (fun w => w = bank roles old aux (pending st code)) (cost old hs) :=
  RecursiveChildSetupRoleBank.placed_hoare _ roles hs old aux _ _
    (RecursiveChildCallReturn.restores old hs st code hd)

private theorem setTape_append_right {l r a : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p = v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals rename_i z; intro h; have hz := z.isLt; omega

private theorem setTape_append_left {l r a : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin l)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.castAdd r i) f p = (setTape v i f p).append w := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals rename_i z; intro h; have hi := i.isLt; omega

theorem reset_pending (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (st : Tapes 2 prime) (code : FiniteReturnStack.Code k) :
    setTape (bank roles hs aux (pending st code)) pcSlot (st.tape 1) (st.head 1) = bank roles hs aux st := by
  unfold bank CleanSubbank.bank common pcSlot
  rw [setTape_append_left,setTape_append_right,setTape_append_right,setTape_append_right]
  unfold pending FiniteReturnStackAt.pushed
  rw [SharedPlacementAlphabet.setTape_setTape,SharedPlacementAlphabet.setTape_self]

private theorem pending_pc (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (st : Tapes 2 prime) (code : FiniteReturnStack.Code k) :
    (bank roles hs aux (pending st code)).head pcSlot = st.head 1+k ∧
    (bank roles hs aux (pending st code)).tape pcSlot = FiniteReturnStack.wordPart (st.tape 1) (st.head 1) code k le_rfl := by
  simp only [bank,CleanSubbank.bank,common,pcSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    pending,FiniteReturnStackAt.pushed,setTape,Function.update_self]
  trivial

def program (hN : N ≤ 2^k) (states : Fin N → ℕ)
    (family : ∀ pc, Program (TapeCount t u) (states pc) prime) :=
  seq restoreProgram (FiniteReturnStackAt.dispatchProgram hN pcSlot states family)

/-- Actual restoration and binary pop/dispatch, preserving the selected
continuation's terminal state for a later finite-controller edge. -/
theorem return_exact (hN : N ≤ 2^k) (states : Fin N → ℕ)
    (family : ∀ pc, Program (TapeCount t u) (states pc) prime) (pc : Fin N)
    (roles : Tapes t prime) (old hs : Fin 6 → List Bool) (aux : Tapes u prime) (st : Tapes 2 prime)
    (hd : RecursiveStackAllocation.Available 0 st)
    (hf : ∀ j < k, st.tape 1 (st.head 1+j) = blank)
    (steps : ℕ) (d : Config (TapeCount t u) (states pc) prime)
    (hr : run (family pc) steps ((bank roles old aux st).start (family pc)) = some d)
    (hh : step (family pc) d = none) :
    ∃ prefixSteps, prefixSteps ≤ cost old hs ∧
      run (program hN states family) (prefixSteps+1+(k+2+steps))
        ((bank roles hs aux (savedStacks old st (address hN pc))).start (program hN states family)) =
        some ((d.mapState (FiniteDispatch.right states pc)).mapState (Fin.natAdd restoreStates)) ∧
      step (program hN states family)
        ((d.mapState (FiniteDispatch.right states pc)).mapState (Fin.natAdd restoreStates)) = none := by
  obtain ⟨prefixSteps,c,hbound,hfirst,hhalt,hout⟩ := restores roles old hs aux st (address hN pc) hd _ rfl
  have hp := pending_pc roles old aux st (address hN pc)
  obtain ⟨hrun,hstop⟩ := FiniteReturnStackAt.dispatch_exact hN pcSlot states family pc
    (bank roles old aux (pending st (address hN pc))) (st.tape 1) (st.head 1) hp.2 hp.1 hf steps d
    (by simpa only [reset_pending] using hr) hh
  refine ⟨prefixSteps,hbound,?_,seq_halt_right _ _ hstop⟩
  have he : (bank roles old aux (pending st (address hN pc))).start
      (FiniteReturnStackAt.dispatchProgram hN pcSlot states family) =
      c.tapes.start (FiniteReturnStackAt.dispatchProgram hN pcSlot states family) := by rw [hout]
  rw [he] at hrun
  exact seq_run _ _ hfirst hhalt hrun

theorem return_hoare (hN : N ≤ 2^k) (states : Fin N → ℕ)
    (family : ∀ pc, Program (TapeCount t u) (states pc) prime) (pc : Fin N)
    (roles : Tapes t prime) (old hs : Fin 6 → List Bool) (aux : Tapes u prime) (st : Tapes 2 prime)
    (hd : RecursiveStackAllocation.Available 0 st)
    (hf : ∀ j < k, st.tape 1 (st.head 1+j) = blank) (B : ℕ) (post : TapePred (TapeCount t u) prime)
    (hc : HoareTime (family pc) (fun w => w = bank roles old aux st) post B) :
    HoareTime (program hN states family)
      (fun w => w = bank roles hs aux (savedStacks old st (address hN pc))) post (cost old hs+k+B+3) := by
  have hp := pending_pc roles old aux st (address hN pc)
  have hd' := FiniteReturnStackAt.dispatch_hoare hN pcSlot states family pc
    (bank roles old aux (pending st (address hN pc))) (st.tape 1) (st.head 1) B post hp.2 hp.1 hf
    (by simpa only [reset_pending] using hc)
  exact ((restores roles old hs aux st (address hN pc) hd).seq hd').consequence
    (fun _ h => h) (fun _ h => h) (by omega)

private def headerField (i : BinaryDescriptorFrames.Slot RecursiveChildCallSetup.descriptorStack) : Fin 6 :=
  ⟨min (i.val.val-3) 5,by omega⟩

private theorem headerField_header (j : Fin 6) : headerField (RecursiveChildCallSetup.header j) = j := by
  apply Fin.ext
  have hj := j.isLt
  simp [headerField,RecursiveChildCallSetup.header,Nat.min_eq_left (by omega : j.val ≤ 5)]

/-- Physical ancestor restoration has a bound in the active child's volume,
using actual canonical headers from two paths with the same root. -/
theorem cost_le_linear {roles m n d depth : ℕ}
    {root active ancestor : RecursiveInterchangeLayout.Descriptor}
    (current : RecursiveInterchangeVolume.Path prime roles m root n active)
    (older : RecursiveInterchangeVolume.Path prime roles m root d ancestor)
    (hr : 0 < roles) (hm : 2 ≤ m) (hw : root.width = m^depth) (hv : root.Positive)
    (old hs : Fin 6 → List Bool) (ho : RecursiveDimensionBank.Headers ancestor old)
    (hc : RecursiveDimensionBank.Headers active hs) :
    cost old hs ≤ (48*(Nat.log2 roles+2)+79)*RecursiveInterchangeLayout.volume prime active := by
  apply RecursiveHeaderRestore.six_field_cost current older Shared50ModularControl.prime_prime.two_le hr hm hw hv
    RecursiveChildCallSetup.descriptorStack RecursiveChildCallSetup.fields
    (by simp [RecursiveChildCallSetup.fields]) headerField old hs ho hc
    (RecursiveChildCallSetup.words old) (RecursiveChildCallSetup.words hs)
  · intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    rw [RecursiveChildCallSetup.words_header,headerField_header]
  · intro i hi
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    rw [RecursiveChildCallSetup.words_header,headerField_header]


theorem return_hoare_linear {roles m n d depth : ℕ}
    {root active ancestor : RecursiveInterchangeLayout.Descriptor}
    (current : RecursiveInterchangeVolume.Path prime roles m root n active)
    (older : RecursiveInterchangeVolume.Path prime roles m root d ancestor)
    (hr : 0 < roles) (hm : 2 ≤ m) (hw : root.width = m^depth) (hv : root.Positive)
    (hN : N ≤ 2^k) (states : Fin N → ℕ)
    (family : ∀ pc, Program (TapeCount t u) (states pc) prime) (pc : Fin N)
    (roleBank : Tapes t prime) (old hs : Fin 6 → List Bool) (aux : Tapes u prime) (st : Tapes 2 prime)
    (ho : RecursiveDimensionBank.Headers ancestor old) (hchild : RecursiveDimensionBank.Headers active hs)
    (hd : RecursiveStackAllocation.Available 0 st)
    (hf : ∀ j < k, st.tape 1 (st.head 1+j) = blank) (B : ℕ) (post : TapePred (TapeCount t u) prime)
    (hc : HoareTime (family pc) (fun w => w = bank roleBank old aux st) post B) :
    HoareTime (program hN states family)
      (fun w => w = bank roleBank hs aux (savedStacks old st (address hN pc))) post
      ((48*(Nat.log2 roles+2)+k+82)*RecursiveInterchangeLayout.volume prime active+B) := by
  apply (return_hoare hN states family pc roleBank old hs aux st hd hf B post hc).consequence
    (fun _ h => h) (fun _ h => h)
  have hcost := cost_le_linear current older hr hm hw hv old hs ho hchild
  have hV : 0 < RecursiveInterchangeLayout.volume prime active :=
    lt_of_lt_of_le (pow_pos Shared50ModularControl.prime_prime.pos _)
      (current.original_chunks Shared50ModularControl.prime_prime.pos hr hv)
  nlinarith


end
end IntegerMultBounds.Machine.RecursiveChildReturnRoleBank
