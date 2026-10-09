import IntegerMultBounds.Machine.FixedHeaderBankCopy
import IntegerMultBounds.Machine.InjectivePlacement

/-! Place a fixed descriptor copy family into named slots of a larger blank
private bank. Unselected private tapes remain blank throughout the contract. -/
namespace IntegerMultBounds.Machine.FixedHeaderSparseBankCopy
noncomputable section
variable {t n u a : ℕ}

def slot (destination : Fin n → Fin u) : Fin (t+n) → Fin (t+u) :=
  Fin.addCases (Fin.castAdd u) (fun i => Fin.natAdd t (destination i))

theorem slot_injective (destination : Fin n → Fin u) (hd : Function.Injective destination) :
    Function.Injective (slot (t := t) destination) := by
  intro i j h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => simpa [slot,Fin.ext_iff] using h
    | right j =>
      have hv := congrArg Fin.val h
      simp [slot] at hv
      have hi := i.isLt
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have hv := congrArg Fin.val h
      simp [slot] at hv
      have hj := j.isLt
      omega
    | right j =>
      have he : destination i = destination j := by simpa [slot,Fin.ext_iff] using h
      exact congrArg (Fin.natAdd t) (hd he)

def placement (destination : Fin n → Fin u) (hd : Function.Injective destination) (hn : n ≤ u) :
    Fin ((t+n)+(u-n)) ≃ Fin (t+u) :=
  InjectivePlacement.placement (slot destination) (slot_injective destination hd) (by omega)

def optionalWords (destination : Fin n → Fin u) (bs : Fin n → List Bool) (j : Fin u) :
    Option (List Bool) := if h : ∃ i, destination i = j then some (bs h.choose) else none

def headerBank (destination : Fin n → Fin u) (bs : Fin n → List Bool) : Tapes u a :=
  FixedHeaderBankCopy.bank (optionalWords destination bs)

theorem optionalWords_target (destination : Fin n → Fin u) (hd : Function.Injective destination)
    (bs : Fin n → List Bool) (i : Fin n) : optionalWords destination bs (destination i) = some (bs i) := by
  have he : ∃ j, destination j = destination i := ⟨i,rfl⟩
  simp only [optionalWords,dite_eq_left he]
  rw [hd he.choose_spec]

theorem optionalWords_blank (destination : Fin n → Fin u) (bs : Fin n → List Bool)
    (j : Fin u) (hj : ∀ i, destination i ≠ j) : optionalWords destination bs j = none := by
  simp [optionalWords,not_exists.mpr hj]

theorem headerBank_target (destination : Fin n → Fin u) (hd : Function.Injective destination)
    (bs : Fin n → List Bool) (i : Fin n) :
    (headerBank (a := a) destination bs).head (destination i) = 1 ∧
    (headerBank (a := a) destination bs).tape (destination i) = RadixZeroFill.encodedBinary (bs i) := by
  simp [headerBank,FixedHeaderBankCopy.bank,optionalWords_target destination hd bs,
    RecursiveDimensionBank.head,RecursiveDimensionBank.tape]

theorem headerBank_blank (destination : Fin n → Fin u) (bs : Fin n → List Bool)
    (j : Fin u) (hj : ∀ i, destination i ≠ j) :
    (headerBank (a := a) destination bs).head j = 0 ∧
    (headerBank (a := a) destination bs).tape j = fun _ => blank := by
  simp [headerBank,FixedHeaderBankCopy.bank,optionalWords_blank destination bs j hj,
    RecursiveDimensionBank.head,RecursiveDimensionBank.tape]

theorem headerBank_eq (destination : Fin n → Fin u) (hd : Function.Injective destination)
    (bs : Fin n → List Bool) (v : Tapes u a)
    (ht : ∀ i, v.head (destination i) = 1 ∧
      v.tape (destination i) = RadixZeroFill.encodedBinary (bs i))
    (hb : ∀ j, (∀ i, destination i ≠ j) → v.head j = 0 ∧ v.tape j = fun _ => blank) :
    v = headerBank destination bs := by
  have he (j : Fin u) : v.head j = (headerBank (a := a) destination bs).head j ∧
      v.tape j = (headerBank (a := a) destination bs).tape j := by
    by_cases hj : ∃ i, destination i = j
    · obtain ⟨i,rfl⟩ := hj
      exact ⟨(ht i).1.trans (headerBank_target destination hd bs i).1.symm,
        (ht i).2.trans (headerBank_target destination hd bs i).2.symm⟩
    · have hn := not_exists.mp hj
      exact ⟨(hb j hn).1.trans (headerBank_blank destination bs j hn).1.symm,
        (hb j hn).2.trans (headerBank_blank destination bs j hn).2.symm⟩
  apply congrArg₂ Tapes.mk
  · funext j; exact (he j).1
  · funext j; exact (he j).2

def program (ht : 0 < t+n) (focus : Fin n → Fin t) (destination : Fin n → Fin u)
    (hd : Function.Injective destination) (hn : n ≤ u) :=
  Placement.placed (FixedHeaderBankCopy.program (a := a) ht focus) (placement destination hd hn)
def cleanup (ht : 0 < t+n) (destination : Fin n → Fin u)
    (hd : Function.Injective destination) (hn : n ≤ u) :=
  Placement.placed (FixedHeaderBankCopy.cleanup (a := a) ht) (placement destination hd hn)

theorem active_input (caller : Tapes t a) (destination : Fin n → Fin u)
    (hd : Function.Injective destination) (hn : n ≤ u) :
    Placement.active (placement destination hd hn) (caller.append (FixedHeaderBankCopy.empty u)) =
      caller.append (FixedHeaderBankCopy.empty n) := by
  rw [placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
    simp [slot,Tapes.append,FixedHeaderBankCopy.empty]

theorem active_output (caller : Tapes t a) (destination : Fin n → Fin u)
    (hd : Function.Injective destination) (hn : n ≤ u) (bs : Fin n → List Bool) :
    Placement.active (placement destination hd hn) (caller.append (headerBank destination bs)) =
      caller.append (FixedHeaderBankCopy.headerBank bs) := by
  rw [placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
    simp [slot,Tapes.append,headerBank,FixedHeaderBankCopy.headerBank,FixedHeaderBankCopy.bank,
      optionalWords_target destination hd bs]

private theorem extra_ne_slot (destination : Fin n → Fin u)
    (hd : Function.Injective destination) (hn : n ≤ u) (i : Fin (u-n)) (j : Fin (t+n)) :
    placement (t := t) destination hd hn (Fin.natAdd (t+n) i) ≠ slot destination j := by
  rw [← InjectivePlacement.active_slot (slot destination) (slot_injective destination hd)
    (by omega : (t+n)+(u-n)=t+u) j]
  intro h
  have he := (placement destination hd hn).injective h
  have hv := congrArg Fin.val he
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  have hj := j.isLt
  omega

private theorem frame_at (caller : Tapes t a) (destination : Fin n → Fin u)
    (bs : Fin n → List Bool) (j : Fin (t+u)) (hj : ∀ i, j ≠ slot destination i) :
    (caller.append (FixedHeaderBankCopy.empty u)).head j =
      (caller.append (headerBank destination bs)).head j ∧
    (caller.append (FixedHeaderBankCopy.empty u)).tape j =
      (caller.append (headerBank destination bs)).tape j := by
  induction j using Fin.addCases with
  | left j => exact (hj (Fin.castAdd n j) (by simp [slot])).elim
  | right j =>
    have he : ∀ i, destination i ≠ j := by
      intro i h
      apply hj (Fin.natAdd t i)
      simp [slot,h]
    simp [Tapes.append,headerBank,FixedHeaderBankCopy.empty,FixedHeaderBankCopy.bank,
      optionalWords_blank destination bs j he,RecursiveDimensionBank.head,RecursiveDimensionBank.tape]

theorem extra_frame (caller : Tapes t a) (destination : Fin n → Fin u)
    (hd : Function.Injective destination) (hn : n ≤ u) (bs : Fin n → List Bool) :
    Placement.extra (placement destination hd hn) (caller.append (FixedHeaderBankCopy.empty u)) =
      Placement.extra (placement destination hd hn) (caller.append (headerBank destination bs)) := by
  apply congrArg₂ Tapes.mk
  · funext i
    exact (frame_at caller destination bs _ (extra_ne_slot destination hd hn i)).1
  · funext i
    exact (frame_at caller destination bs _ (extra_ne_slot destination hd hn i)).2

theorem constructs (ht : 0 < t+n) (focus : Fin n → Fin t) (destination : Fin n → Fin u)
    (hd : Function.Injective destination) (hn : n ≤ u) (caller : Tapes t a)
    (bs : Fin n → List Bool)
    (hs : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (bs i))
    (hh : ∀ i, caller.head (focus i) = 1) :
    HoareTime (program ht focus destination hd hn)
      (fun z => z = caller.append (FixedHeaderBankCopy.empty u))
      (fun z => z = caller.append (headerBank destination bs))
      (FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops n) bs) := by
  have h := Placement.hoare_at (FixedHeaderBankCopy.constructs ht focus bs caller hs hh)
    (placement destination hd hn) _ (active_input caller destination hd hn)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨w,rfl,rfl⟩
  rw [Placement.replace,extra_frame,← active_output]
  exact Placement.view _ _

theorem constructs_linear (ht : 0 < t+n) (focus : Fin n → Fin t) (destination : Fin n → Fin u)
    (hd : Function.Injective destination) (hn : n ≤ u) (caller : Tapes t a)
    (bs : Fin n → List Bool)
    (hs : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (bs i))
    (hh : ∀ i, caller.head (focus i) = 1) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (bs i)) (hv : ∀ i, Counter.value (bs i) ≤ V) :
    HoareTime (program ht focus destination hd hn)
      (fun z => z = caller.append (FixedHeaderBankCopy.empty u))
      (fun z => z = caller.append (headerBank destination bs)) (10*n*V) :=
  (constructs ht focus destination hd hn caller bs hs hh).consequence
    (fun _ h => h) (fun _ h => h) (FixedHeaderBankCopy.cost_linear bs V hV hc hv)

theorem cleans (ht : 0 < t+n) (destination : Fin n → Fin u)
    (hd : Function.Injective destination) (hn : n ≤ u) (caller : Tapes t a)
    (bs : Fin n → List Bool) :
    HoareTime (cleanup ht destination hd hn)
      (fun z => z = caller.append (headerBank destination bs))
      (fun z => z = caller.append (FixedHeaderBankCopy.empty u))
      (FixedHeaderBankCopy.cleanupCost (t := t) bs) := by
  have h := Placement.hoare_at (FixedHeaderBankCopy.cleans ht caller bs)
    (placement destination hd hn) _ (active_output caller destination hd hn bs)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨w,rfl,rfl⟩
  rw [Placement.replace,← extra_frame,← active_input]
  exact Placement.view _ _

theorem cleans_linear (ht : 0 < t+n) (destination : Fin n → Fin u)
    (hd : Function.Injective destination) (hn : n ≤ u) (caller : Tapes t a)
    (bs : Fin n → List Bool) (V : ℕ) (hV : 0 < V)
    (hc : ∀ i, GrowingCounterData.Canonical (bs i)) (hv : ∀ i, Counter.value (bs i) ≤ V) :
    HoareTime (cleanup ht destination hd hn)
      (fun z => z = caller.append (headerBank destination bs))
      (fun z => z = caller.append (FixedHeaderBankCopy.empty u)) (9*n*V) :=
  (cleans ht destination hd hn caller bs).consequence
    (fun _ h => h) (fun _ h => h) (FixedHeaderBankCopy.cleanup_cost_linear bs V hV hc hv)

end
end IntegerMultBounds.Machine.FixedHeaderSparseBankCopy
