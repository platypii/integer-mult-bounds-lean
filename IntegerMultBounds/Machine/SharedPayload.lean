import IntegerMultBounds.Machine.InjectivePlacement
import IntegerMultBounds.Machine.SharedPlacementAlphabet

/-! One pair of permanent payload tapes shared with a stage's private metadata.
The stage's own source/output slots are physically blank unused frames; only
metadata is retained there. No payload copy or head reset is assumed. -/
namespace IntegerMultBounds.Machine.SharedPayload
variable {t q a : ℕ}
open SharedPlacementAlphabet (setTape)

def slot (source dest : Fin t) (i : Fin t) : Fin (2+t) :=
  if i = source then Fin.castAdd t (0 : Fin 2)
  else if i = dest then Fin.castAdd t (1 : Fin 2) else Fin.natAdd 2 i

theorem slot_injective (source dest : Fin t) (hne : source ≠ dest) : Function.Injective (slot source dest) := by
  let recover : Fin (2+t) → Fin t := Fin.addCases (fun i : Fin 2 => if i = 0 then source else dest) id
  have hr (i : Fin t) : recover (slot source dest i) = i := by
    by_cases hs : i = source
    · subst i; simp [slot,recover]
    by_cases hd : i = dest
    · subst i; simp [slot,recover,Ne.symm hne]
    · simp [slot,recover,hs,hd]
  intro i j hij
  exact (hr i).symm.trans ((congrArg recover hij).trans (hr j))

noncomputable def placement (source dest : Fin t) (hne : source ≠ dest) : Fin (t+2) ≃ Fin (2+t) :=
  InjectivePlacement.placement (slot source dest) (slot_injective source dest hne) (by omega)

@[simp] theorem placement_active (source dest : Fin t) (hne : source ≠ dest) (i : Fin t) :
    placement source dest hne (Fin.castAdd 2 i) = slot source dest i :=
  InjectivePlacement.active_slot _ _ _ _

def payload (v : Tapes t a) (source dest : Fin t) : Tapes 2 a :=
  ⟨![v.head source,v.head dest],![v.tape source,v.tape dest]⟩

def strip (v : Tapes t a) (source dest : Fin t) : Tapes t a :=
  setTape (setTape v source (fun _ => blank) 0) dest (fun _ => blank) 0

def bank (v : Tapes t a) (source dest : Fin t) : Tapes (2+t) a :=
  (payload v source dest).append (strip v source dest)

theorem active_bank (v : Tapes t a) (source dest : Fin t) (hne : source ≠ dest) :
    Placement.active (placement source dest hne) (bank v source dest) = v := by
  unfold placement
  rw [InjectivePlacement.active_bank]
  unfold bank payload strip setTape
  congr 1 <;> funext i <;>
    by_cases hs : i = source <;> by_cases hd : i = dest <;>
    simp [slot,Tapes.append,hs,hd,Ne.symm hne]

private theorem unselected (source dest : Fin t) (hne : source ≠ dest) (x : Fin (2+t))
    (hx : ∀ i, x ≠ slot source dest i) : x = Fin.natAdd 2 source ∨ x = Fin.natAdd 2 dest := by
  induction x using Fin.addCases with
  | left x =>
    fin_cases x
    · exact False.elim (hx source (by simp [slot]))
    · exact False.elim (hx dest (by simp [slot,Ne.symm hne]))
  | right x =>
    by_cases hs : x = source
    · exact Or.inl (by subst x; rfl)
    by_cases hd : x = dest
    · exact Or.inr (by subst x; rfl)
    exact False.elim (hx x (by simp [slot,hs,hd]))

/-- Both unused private payload slots are literal blank, stationary frame. -/
theorem extra_bank (v : Tapes t a) (source dest : Fin t) (hne : source ≠ dest) :
    Placement.extra (placement source dest hne) (bank v source dest) =
      (⟨fun _ => 0,fun _ _ => blank⟩ : Tapes 2 a) := by
  have hx (j : Fin 2) : ∀ i, placement source dest hne (Fin.natAdd t j) ≠ slot source dest i := by
    intro i he
    rw [← placement_active source dest hne i] at he
    have hi := (placement source dest hne).injective he
    have hv := congrArg Fin.val hi
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  unfold Placement.extra
  congr 1 <;> funext j <;>
    rcases unselected source dest hne _ (hx j) with hj | hj <;>
    rw [hj] <;> simp [bank,strip,setTape,Tapes.append,hne]

/-- A complete actual stage executes against the permanent payload pair while
its own payload slots remain blank and all private metadata is retained. -/
theorem stage_hoare {M : Program t q a} {v w : Tapes t a} {cost : ℕ}
    (h : HoareTime M (fun x => x = v) (fun x => x = w) cost)
    (source dest : Fin t) (hne : source ≠ dest) :
    HoareTime (Placement.placed M (placement source dest hne))
      (fun x => x = bank v source dest) (fun x => x = bank w source dest) cost := by
  have hh := Placement.hoare_at h (placement source dest hne) (bank v source dest) (active_bank _ _ _ _)
  apply hh.consequence (fun _ h => h) ?_ le_rfl
  rintro x ⟨small,hsmall,rfl⟩
  subst small
  rw [Placement.replace,extra_bank,← extra_bank w source dest hne]
  have hv := Placement.view (placement source dest hne) (bank w source dest)
  simpa only [active_bank] using hv

end IntegerMultBounds.Machine.SharedPayload
