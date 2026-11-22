module

public import IntegerMultBounds.MathlibTM2.M6.BitNineStageHandoff

/-! Logical reads from the collapsed PR589 sweep output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open Certificates.PR589 Certificates.PR589.Nine Swap.Modular
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- After the sweep releases its scratch owner, every inactive role still
carries the family exchange in the chart of its certified port. -/
theorem sweepEffect_inactive {n : Fin 9} {w B W : ℕ} {x y : OwnerArray w B W}
    (step : sweepEffect n w B W x y) (r : Role) (inactive : r.bank.val / 2 ≠ BitHosting.activePair n.val)
    (b : Fin B) (j : Fin W) :
    let tape := ((Fin.cast card_role) (Fintype.equivFin Role r)).castSucc
    let addr := fun s =>
      let digits := helperSlotField (port r.port.val) none w s
      finProdFinEquiv (FlatCoordinateLayout.rank (digits ∘ Fin.castAdd 112),
        finProdFinEquiv (b,finProdFinEquiv (FlatCoordinateLayout.rank (digits ∘ Fin.natAdd 16),j)))
    ∀ s, y tape (addr (M8.Exchange.exchange (reduce (prime^w) (familySum n r)) s)) = x tape (addr s) := by
  intro tape addr s
  obtain ⟨packed,out,⟨trace,restore⟩,rfl⟩ := step
  rw [Function.update_of_ne (Fin.castSucc_ne_last _)]
  let label := firstRowLabel w
  let K := (prime^w)^112*W
  let z : LabelEntry.Cell (copyLabelLayout w B K) B :=
    ⟨⟨0,pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _⟩,⟨0,Nat.zero_lt_one⟩,b,
      ⟨0,by simp [copyLabelLayout,ActualAffineScaling.modulus]⟩,⟨0,Nat.zero_lt_one⟩,
      ⟨0,by simp [copyLabelLayout,ActualAffineScaling.modulus]⟩,
      finProdFinEquiv (FlatCoordinateLayout.rank (helperSlotField (port r.port.val) none w s ∘ Fin.natAdd 16),j)⟩
  have read := restoredStage_inactiveRow n w B W label x packed out trace restore r inactive label z j s
  have supported := restoredStage_inactiveWord n w B W label x packed out trace restore r inactive
  dsimp only at read supported
  rw [supported,singleLabelBank_helperCell] at read
  simpa only [Fin.val_cast,ite_true] using read

/-- On the active copy the source undergoes its frame change and the target
receives the framed XOR, after collapsing the label rows. -/
theorem sweepEffect_active {n : Fin 9} {w B W : ℕ} {x y : OwnerArray w B W}
    (step : sweepEffect n w B W x y) (run : Fin 32 × Fin 5) (t : Fin 111)
    (z : LabelEntry.Cell (copyLabelLayout w B ((prime^w)^112*W)) B) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n run.1 run.2,ownerTape_injective ..⟩
    let j : Fin (B*((prime^w)^112*W)) := finProdFinEquiv (z.b,z.after)
    let initial := fun i => (selectedFrame w (Frames.initialRefs i)).symm (phaseRead owner x j i)
    phaseRead owner y j (111+t.val) =
      selectedFrame w (Frames.finalRefs (111+t.val)) (initial (111+t.val) + initial t.val) ∧
    phaseRead owner y j t.val = selectedFrame w (Frames.finalRefs t.val) (initial t.val) := by
  classical
  intro owner j initial
  obtain ⟨packed,out,⟨trace,restore⟩,rfl⟩ := step
  let label := firstRowLabel w
  let data := collapseLabelBank (w := w) (B := B) (K := (prime^w)^112*W) out
  have read (i : ℕ) (hi : i < 661) :
      phaseRead owner (Function.update data (Fin.last 142080) (fun _ => 0)) j i = phaseRead owner data j i := by
    funext s
    simp only [phaseRead,Copy.extendStored,dite_eq_left hi,
      Function.update_of_ne (show owner ⟨i,hi⟩ ≠ Fin.last 142080 from Fin.castSucc_ne_last _)]
  rw [read _ (by omega),read _ (by omega)]
  constructor
  · simpa only [data,owner,j,initial,collapse_singleLabelBank] using
      (restoredStage_active n run w B W _ packed out trace restore t z).1
  · have sum := collapseLabelBank_read out owner z (⟨t.val,by omega⟩ : Fin 661)
    change phaseRead owner data j t.val = _ at sum
    rw [sum]
    calc
      _ = ∑ g : LabelPadding.Label 64 w, if g = label then selectedFrame w (Frames.finalRefs t.val)
          (initial t.val) else 0 := Finset.sum_congr rfl fun g _ =>
            restoredStage_sourceLabel n run w B W label x packed out trace restore t z g
      _ = _ := by simp

end IntegerMultBounds.MathlibTM2.M6.BitNode
