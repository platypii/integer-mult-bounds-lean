module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapMachine
public import IntegerMultBounds.MathlibTM2.Host.Foreign

/-! Execute the prepared coordinate swap on host stacks representing its tape bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (volume)
open M8.RevMachine
open SharedBankStageInput (raw)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos w).ne'⟩

/-- The swap supplier uses the same blank-backed binary word as the row machine. -/
theorem swap_source_word {v : RecursiveInterchangeLayout.Descriptor}
    (x : Fin (volume prime v) → ZMod 2) (pos : ℤ) :
    sourceWord x pos = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ x)) pos) := by
  rfl

/-- Read a role directly from the host representation, independently of the header and private tapes. -/
theorem swap_role_read {T N : ℕ} (roles : Tapes T prime)
    (view : RecursiveInterchangeLayout.Descriptor) (headers : Fin 22 → Option (List Bool))
    (S : Stacks N prime) (rep : RepT (raw (LabelCall.bank roles view headers) N) S.L S.R)
    (io : Fin T) (slot : Fin N) (leading : slot.val = io.val) (pos : ℤ) :
    readAt blank (S.L slot) (S.R slot) (pos-roles.head io) = roles.tape io pos := by
  have cell := rep slot pos
  have lt : slot.val < T+24 := leading ▸ (Fin.castAdd 24 io).isLt
  simp only [raw,dite_eq_left lt] at cell
  have eq : (⟨slot.val,lt⟩ : Fin (T+24)) = Fin.castAdd 24 io := Fin.ext leading
  rw [eq] at cell
  simp only [LabelCall.bank,Tapes.append,Fin.addCases_left] at cell
  exact cell.symm

theorem swapPayload_exec [M8.Machine.Net] {T d w W : ℕ} {P U : Type}
    (i j : Fin d) (h : i < j) (hw : 0 < w) (hW : 0 < W)
    (roles : Tapes T prime) (io : Fin T)
    (x : Fin (volume prime (payloadView prime d w W)) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x) :
    let view := payloadView prime d w W
    let headers := LabelPrepare.input view d i.val j.val w
    let block := LabelSwap.program io
    let cost := 3808274 * volume prime view + LeafCore.coreCost (volume prime view) w
    ∀ (body : P → Pr P block.tapes block.states prime U) (v : HS block.tapes block.states prime U)
      (S : Stacks block.tapes prime),
      RepT (raw (LabelCall.bank roles view headers) block.tapes) S.L S.R →
      ∃ (y : Fin (volume prime view) → ZMod 2), ∃ z F n, z.user = v.user ∧ n ≤ cost*(block.tapes+5)+6 ∧
        Exec body (foreign block.program) (mk v S) n (mk z F) ∧
        RepT (raw (LabelCall.bank (SharedPlacementAlphabet.setTape roles io (sourceWord (v := view) y) 0)
          view headers) block.tapes) F.L F.R ∧
        (∀ pos, readAt blank (F.L (block.slots (Fin.castAdd 24 io))) (F.R (block.slots (Fin.castAdd 24 io))) pos =
          RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ y)) pos)) ∧
        ∀ (coords : Fin d → ZMod (prime^w)) (k : Fin W),
          ext y (FlatCoordinateLayout.index (coords ∘ Equiv.swap i j) k).val =
            ext x (FlatCoordinateLayout.index coords k).val := by
  intro view headers block cost body v S ready
  obtain ⟨y,swap,effect⟩ := swapPayload_runs i j h hw hW roles io x hh hx
  obtain ⟨z,F,_,rfl,rep,user,_,_,_,n,time,run⟩ := foreign_exec body block.program swap v S _ rfl ready
  refine ⟨y,z,F,n,user,time,run,rep,?_,effect⟩
  intro pos
  have cell := swap_role_read _ view headers F rep io (block.slots (Fin.castAdd 24 io)) rfl pos
  simpa only [SharedPlacementAlphabet.setTape,Function.update_self,sub_zero,swap_source_word] using cell

end IntegerMultBounds.MathlibTM2.Cover.Fallback
