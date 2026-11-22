module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece

/-! Interchange the label block and exterior digits between a sweep and an idle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)

theorem idleSize (w B K : ℕ) : volume prime (idleLayout w B K) =
    (prime^w)^128*(B*prime^(64*(w*64))*K) := by
  simp [volume,Nat.mul_assoc]

/-- In sweep order the label row follows the 16 active digits. In idle order
it follows all 128 digits. The offset within a trailing record is unchanged. -/
noncomputable def idleToSweep (w B K : ℕ) :
    Fin (volume prime (idleLayout w B K)) ≃
      Fin ((prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*K))) := by
  let split : Fin ((prime^w)^128) ≃ Fin ((prime^w)^16) × Fin ((prime^w)^112) :=
    (finCongr (by rw [← pow_add])).trans finProdFinEquiv.symm
  let rows := B*prime^(64*(w*64))
  let idle := (finCongr (idleSize w B K)).trans (finProdFinEquiv.symm.trans
    (split.prodCongr (@finProdFinEquiv rows K).symm))
  let sweep := (@finProdFinEquiv ((prime^w)^16) (rows*((prime^w)^112*K))).symm.trans ((Equiv.refl _).prodCongr
    (finProdFinEquiv.symm.trans ((Equiv.refl (Fin rows)).prodCongr (@finProdFinEquiv ((prime^w)^112) K).symm)))
  let shuffle : (Fin ((prime^w)^16) × Fin ((prime^w)^112)) × (Fin rows × Fin K) ≃
      Fin ((prime^w)^16) × Fin rows × Fin ((prime^w)^112) × Fin K :=
    ⟨fun ((a,e),l,t) => (a,l,e,t),fun (a,l,e,t) => ((a,e),l,t),fun _ => rfl,fun _ => rfl⟩
  exact (idle.trans shuffle).trans sweep.symm

local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩

/-- Form an idle index from the payload rank, block, matrix label and tail. -/
noncomputable def idleCellIndex {w B K} (g : LabelPadding.Label 64 w) (rank : Fin ((prime^w)^128))
    (b : Fin B) (t : Fin K) : Fin (volume prime (idleLayout w B K)) :=
  let row := (LabelAddress.address g).cast (show (prime^w)^(64*64) = prime^(64*(w*64)) by
    rw [← pow_mul]; congr 1; omega)
  (finProdFinEquiv (rank,finProdFinEquiv (finProdFinEquiv (b,row),t))).cast (idleSize w B K).symm

theorem idleDigitCell_read {w B K n} (width : n = 128) (digits : Fin n → ZMod (prime^w))
    (b : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w)
    (x : Fin (volume prime (idleLayout w B K)) → ZMod 2) :
    chartRead x g (idleDigitCell width digits b t) =
      x (idleCellIndex g ((FlatCoordinateLayout.rank digits).cast (congrArg ((prime^w)^·) width)) b t) := by
  let idx := idleCellIndex g ((FlatCoordinateLayout.rank digits).cast (congrArg ((prime^w)^·) width)) b t
  rw [← ext_apply x idx]
  apply congrArg (ext x)
  simp [idx,idleCellIndex,idleDigitCell,RecursiveInterchangeLayout.index,idleLayout,finProdFinEquiv]
  <;> ring

theorem idleToSweep_cell {w B K} (g : LabelPadding.Label 64 w)
    (a : Fin ((prime^w)^16)) (e : Fin ((prime^w)^112)) (b : Fin B) (t : Fin K) :
    let rank := (finProdFinEquiv (a,e)).cast (show (prime^w)^16*(prime^w)^112 = (prime^w)^128 by rw [← pow_add])
    let label := (LabelAddress.address g).cast (show (prime^w)^(64*64) = prime^(64*(w*64)) by
      rw [← pow_mul]; congr 1; omega)
    idleToSweep w B K (idleCellIndex g rank b t) =
      finProdFinEquiv (a,finProdFinEquiv (finProdFinEquiv (b,label),finProdFinEquiv (e,t))) := by
  simp [idleToSweep,idleCellIndex]

/-- The selected remainder carries its input bit to the swapped digit
address in sweep order, keeping the block, matrix label and tail offset. -/
theorem IdleTransport.sweepDigits {i : Fin 9} {k : (Fin 32 × Fin 5) × Fin 222} {w B K}
    {x y : Fin ((prime^w)^16*(B*prime^(64*(w*64))*((prime^w)^112*K))) → ZMod 2}
    (run : IdleTransport i k w B K (x ∘ idleToSweep w B K) (y ∘ idleToSweep w B K)) :
    let e := idleInterval i k.2
    ∀ (a b : Fin e.1 → ZMod (prime^w)) (h d : Fin (e.2-e.1) → ZMod (prime^w))
      (u v : Fin (64-e.2) → ZMod (prime^w)) (block : Fin B) (t : Fin K) (g : LabelPadding.Label 64 w),
      let digits := fun (h d : Fin (e.2-e.1) → ZMod (prime^w)) => Fin.addCases (Fin.addCases (Fin.addCases a h) u) (Fin.addCases (Fin.addCases b d) v)
      let width : (e.1+(e.2-e.1)+(64-e.2))+(e.1+(e.2-e.1)+(64-e.2)) = 128 := by
        obtain ⟨hl,hr,_⟩ := BitHosting.remainder_counts _ (idleInterval_mem i k.2)
        change e.1 ≤ e.2 at hl
        change e.2 ≤ 63 at hr
        omega
      let pos := fun h d => idleToSweep w B K (idleCellIndex g
        ((FlatCoordinateLayout.rank (digits h d)).cast (congrArg ((prime^w)^·) width)) block t)
      y (pos d h) = x (pos h d) := by
  intro e a b h d u v block t g digits width pos
  simpa only [idleDigitCell_read,Function.comp_apply] using run.digits a b h d u v block t g

end IntegerMultBounds.MathlibTM2.M6.BitNode
