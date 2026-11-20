module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece

/-! Interpret the ordinary PR589 owner tapes at a common live label. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Matrix
open Shared50ModularControl (prime)
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open Cover LabelTraversal FlatCoordinateLayout

/-- All selected owners realize the compiled idle at the same packed address
for each live label, inherited block and spectator. -/
theorem ordinaryIdle_read {w R W parents : ℕ} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (block : Fin parents) (g : LabelPadding.Label 64 (w+1)) (live : IsUnit g)
    (count : parents*(prime^(w+1))^(64*64) = R) (spectator : Fin W)
    (before after : Fin 142081 → Fin (R*((prime^(w+1))^128*W)) → ZMod 2)
    (reads : ∀ k, OriginalPortReads R W parents (idleInterval i k.2) parent (port (idleRole i k).port.val)
      (before (idleTape i k)) (after (idleTape i k)))
    (off : ∀ j, (∀ k, j ≠ idleTape i k) → after j = before j) :
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let axes := Equiv.sumCongr stageAxis.symm stageAxis.symm
    let frame := fromBlocks (diagonal parent*g) 0 0 (M8.ReversedExchange.rev 64*g)
    let row : Fin R := (finProdFinEquiv (block,LabelAddress.address g)).cast count
    let pack := fun x => finProdFinEquiv (row,index ((frame.mulVec (x ∘ axes)) ∘ finSumFinEquiv.symm) spectator)
    readRoles (pack ∘ addressMod M) after =
      (Piece.remainder i.val).run (readRoles (pack ∘ addressMod M) before) := by
  intro M axes frame row pack
  apply idleCopies_modular_read (w+1) i pack before after _ off
  intro k e P x
  dsimp only [pack]
  rw [idleExchange_axes _ (port_checked _ (idleRole i k).port.isLt) e.1 e.2]
  exact (reads k).exchange units block g live count (x ∘ axes) spectator

end IntegerMultBounds.MathlibTM2.M6.BitNode
