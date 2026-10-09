import IntegerMultBounds.Machine.FixedHeaderSparseBankCopy
import IntegerMultBounds.Machine.SharedBank

/-! Structural sparse-header bank identities, with no tape operations hidden
in the equalities. Actual copying/erasure is supplied by SparseBankCopy. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersAppend
noncomputable section
open FixedHeaderSparseBankCopy
variable {a l r m n : ℕ}

def leftSlots (d : Fin m → Fin l) : Fin m → Fin (l+r) := fun i => Fin.castAdd r (d i)
def rightSlots (d : Fin n → Fin r) : Fin n → Fin (l+r) := fun i => Fin.natAdd l (d i)
def slots (d : Fin m → Fin l) (e : Fin n → Fin r) : Fin (m+n) → Fin (l+r) :=
  Fin.addCases (leftSlots d) (rightSlots e)

theorem left_injective (d : Fin m → Fin l) (hd : Function.Injective d) :
    Function.Injective (leftSlots (r := r) d) := fun _ _ h => hd (Fin.castAdd_injective _ _ h)
theorem right_injective (d : Fin n → Fin r) (hd : Function.Injective d) :
    Function.Injective (rightSlots (l := l) d) := fun _ _ h => hd (Fin.natAdd_injective _ _ h)

theorem slots_injective (d : Fin m → Fin l) (e : Fin n → Fin r)
    (hd : Function.Injective d) (he : Function.Injective e) : Function.Injective (slots d e) := by
  intro i j h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [slots,Fin.addCases_left] at h
      exact congrArg (Fin.castAdd n) (left_injective d hd h)
    | right j =>
      have hv := congrArg Fin.val h
      simp only [slots,leftSlots,rightSlots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
      have hi := (d i).isLt
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have hv := congrArg Fin.val h
      simp only [slots,leftSlots,rightSlots,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at hv
      have hj := (d j).isLt
      omega
    | right j =>
      simp only [slots,Fin.addCases_right] at h
      exact congrArg (Fin.natAdd m) (right_injective e he h)

theorem append_empty (d : Fin m → Fin l) (hd : Function.Injective d) (bs : Fin m → List Bool) :
    (headerBank (a := a) d bs).append (SharedBank.empty r a) = headerBank (leftSlots d) bs := by
  apply headerBank_eq _ (left_injective d hd)
  · intro i
    simpa only [leftSlots,Tapes.append,Fin.addCases_left] using headerBank_target (a := a) d hd bs i
  · intro j hj
    induction j using Fin.addCases with
    | left j =>
      have hh := headerBank_blank (a := a) d bs j (fun i he => hj i (congrArg (Fin.castAdd r) he))
      simpa only [Tapes.append,Fin.addCases_left] using hh
    | right j => simp [Tapes.append,SharedBank.empty]

theorem empty_append (d : Fin n → Fin r) (hd : Function.Injective d) (bs : Fin n → List Bool) :
    (SharedBank.empty l a).append (headerBank (a := a) d bs) = headerBank (rightSlots d) bs := by
  apply headerBank_eq _ (right_injective d hd)
  · intro i
    simpa only [rightSlots,Tapes.append,Fin.addCases_right] using headerBank_target (a := a) d hd bs i
  · intro j hj
    induction j using Fin.addCases with
    | left j => simp [Tapes.append,SharedBank.empty]
    | right j =>
      have hh := headerBank_blank (a := a) d bs j (fun i he => hj i (congrArg (Fin.natAdd l) he))
      simpa only [Tapes.append,Fin.addCases_right] using hh

theorem append (d : Fin m → Fin l) (e : Fin n → Fin r)
    (hd : Function.Injective d) (he : Function.Injective e)
    (bs : Fin m → List Bool) (cs : Fin n → List Bool) :
    (headerBank (a := a) d bs).append (headerBank e cs) =
      headerBank (slots d e) (Fin.addCases bs cs) := by
  apply headerBank_eq _ (slots_injective d e hd he)
  · intro i
    induction i using Fin.addCases with
    | left i =>
      simpa only [slots,leftSlots,Fin.addCases_left,Tapes.append] using headerBank_target (a := a) d hd bs i
    | right i =>
      simpa only [slots,rightSlots,Fin.addCases_right,Tapes.append] using headerBank_target (a := a) e he cs i
  · intro j hj
    induction j using Fin.addCases with
    | left j =>
      have hh := headerBank_blank (a := a) d bs j
        (fun i he => hj (Fin.castAdd n i) (by simpa only [slots,leftSlots,Fin.addCases_left] using congrArg (Fin.castAdd r) he))
      simpa only [Tapes.append,Fin.addCases_left] using hh
    | right j =>
      have hh := headerBank_blank (a := a) e cs j
        (fun i he => hj (Fin.natAdd m i) (by simpa only [slots,rightSlots,Fin.addCases_right] using congrArg (Fin.natAdd l) he))
      simpa only [Tapes.append,Fin.addCases_right] using hh

end
end IntegerMultBounds.Machine.ArbitraryWidthExecutionPrivateHeadersAppend
