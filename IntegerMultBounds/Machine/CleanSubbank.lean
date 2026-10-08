import IntegerMultBounds.Machine.SharedBankStage

/-! Place a clean small-bank machine at arbitrary selected permanent tapes,
using blank private workspace and preserving every unselected permanent tape.
The placement is fixed and adds no copying, head reset, or transition cost. -/
namespace IntegerMultBounds.Machine.CleanSubbank
noncomputable section
variable {c s k q a : ℕ}

def slot (ports : Fin c → Fin s) (common : Fin c → Fin k) (i : Fin s) : Fin (k+s) :=
  if h : ∃ j, ports j = i then Fin.castAdd s (common h.choose) else Fin.natAdd k i

theorem slot_selected (ports : Fin c → Fin s) (common : Fin c → Fin k)
    (hl : Function.Injective ports) (j : Fin c) :
    slot ports common (ports j) = Fin.castAdd s (common j) := by
  unfold slot
  split_ifs with h
  · rw [hl h.choose_spec]
  · exact (h ⟨j,rfl⟩).elim

theorem slot_injective (ports : Fin c → Fin s) (common : Fin c → Fin k)
    (hc : Function.Injective common) : Function.Injective (slot ports common) := by
  intro i j hij
  unfold slot at hij
  split_ifs at hij with hi hj hj
  · have he := hc (Fin.castAdd_injective _ _ hij)
    exact hi.choose_spec.symm.trans ((congrArg ports he).trans hj.choose_spec)
  · have he := congrArg Fin.val hij
    simp only [Fin.val_castAdd,Fin.val_natAdd] at he
    omega
  · have he := congrArg Fin.val hij
    simp only [Fin.val_castAdd,Fin.val_natAdd] at he
    omega
  · exact Fin.natAdd_injective _ _ hij

def placement (ports : Fin c → Fin s) (common : Fin c → Fin k)
    (hc : Function.Injective common) : Fin (s+k) ≃ Fin (k+s) :=
  InjectivePlacement.placement (slot ports common) (slot_injective ports common hc) (Nat.add_comm s k)

@[simp] theorem placement_active (ports : Fin c → Fin s) (common : Fin c → Fin k)
    (hc : Function.Injective common) (i : Fin s) :
    placement ports common hc (Fin.castAdd k i) = slot ports common i :=
  InjectivePlacement.active_slot _ _ _ i

def bank (v : Tapes k a) : Tapes (k+s) a := v.append (SharedBank.empty s a)

/-- The active local view consists of selected permanent tapes and physically
blank private slots. The statement covers arbitrary positions and tape heads. -/
theorem active_bank (ports : Fin c → Fin s) (common : Fin c → Fin k)
    (hl : Function.Injective ports) (hc : Function.Injective common)
    (v : Tapes k a) (small : Tapes s a)
    (hp : SharedBank.payload small ports = SharedBank.payload v common)
    (hs : SharedBank.strip small ports = SharedBank.empty s a) :
    Placement.active (placement ports common hc) (bank v) = small := by
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j, ports j = i
    · obtain ⟨j,rfl⟩ := hi
      have he := congrFun (congrArg Tapes.head hp) j
      simpa only [Placement.active,placement_active,slot_selected ports common hl,bank,
        Tapes.append,Fin.addCases_left,SharedBank.payload] using he.symm
    · have he := congrFun (congrArg Tapes.head hs) i
      simpa only [Placement.active,placement_active,slot,hi,↓reduceDIte,bank,Tapes.append,
        Fin.addCases_right,SharedBank.empty,SharedBank.strip,↓reduceIte] using he.symm
  · funext i
    by_cases hi : ∃ j, ports j = i
    · obtain ⟨j,rfl⟩ := hi
      have he := congrFun (congrArg Tapes.tape hp) j
      simpa only [Placement.active,placement_active,slot_selected ports common hl,bank,
        Tapes.append,Fin.addCases_left,SharedBank.payload] using he.symm
    · have he := congrFun (congrArg Tapes.tape hs) i
      simpa only [Placement.active,placement_active,slot,hi,↓reduceDIte,bank,Tapes.append,
        Fin.addCases_right,SharedBank.empty,SharedBank.strip,↓reduceIte] using he.symm

private theorem extra_eq (ports : Fin c → Fin s) (common : Fin c → Fin k)
    (hl : Function.Injective ports) (hc : Function.Injective common) (v w : Tapes k a)
    (hframe : SharedBank.strip v common = SharedBank.strip w common) :
    Placement.extra (placement ports common hc) (bank v) =
      Placement.extra (placement ports common hc) (bank w) := by
  have hpoint (i : Fin k) (hi : ¬∃ j, common j = i) :
      v.head i = w.head i ∧ v.tape i = w.tape i := by
    constructor
    · have h := congrFun (congrArg Tapes.head hframe) i
      simpa only [SharedBank.strip,hi,↓reduceIte] using h
    · have h := congrFun (congrArg Tapes.tape hframe) i
      simpa only [SharedBank.strip,hi,↓reduceIte] using h
  have hslot (j : Fin k) (i : Fin c) :
      placement ports common hc (Fin.natAdd s j) ≠ Fin.castAdd s (common i) := by
    rw [← slot_selected ports common hl,← placement_active ports common hc]
    intro h
    have he := congrArg Fin.val ((placement ports common hc).injective h)
    simp only [Fin.val_natAdd,Fin.val_castAdd] at he
    omega
  have heq (j : Fin k) :
      (bank (s := s) v).head (placement ports common hc (Fin.natAdd s j)) =
        (bank (s := s) w).head (placement ports common hc (Fin.natAdd s j)) ∧
      (bank (s := s) v).tape (placement ports common hc (Fin.natAdd s j)) =
        (bank (s := s) w).tape (placement ports common hc (Fin.natAdd s j)) := by
    generalize hx : placement ports common hc (Fin.natAdd s j) = x
    induction x using Fin.addCases with
    | left i =>
      have hi : ¬∃ z, common z = i := by
        rintro ⟨z,rfl⟩
        exact hslot j z hx
      simpa only [bank,Tapes.append,Fin.addCases_left] using hpoint i hi
    | right i => simp only [bank,Tapes.append,Fin.addCases_right,and_self]
  apply congrArg₂ Tapes.mk
  · funext j; exact (heq j).1
  · funext j; exact (heq j).2

/-- Exact clean-to-clean physical lift. Selected permanent tapes may change;
every other permanent tape and every private tape is restored literally. -/
theorem realizes (M : Program s q a) (ports : Fin c → Fin s) (common : Fin c → Fin k)
    (hl : Function.Injective ports) (hc : Function.Injective common)
    (v w : Tapes k a) (input output : Tapes s a) (cost : ℕ)
    (hi : SharedBank.payload input ports = SharedBank.payload v common)
    (ho : SharedBank.payload output ports = SharedBank.payload w common)
    (hci : SharedBank.strip input ports = SharedBank.empty s a)
    (hco : SharedBank.strip output ports = SharedBank.empty s a)
    (hframe : SharedBank.strip v common = SharedBank.strip w common)
    (h : HoareTime M (fun x => x = input) (fun x => x = output) cost) :
    HoareTime (Placement.placed M (placement ports common hc))
      (fun x => x = bank v) (fun x => x = bank w) cost := by
  have hh := Placement.hoare_at h (placement ports common hc) (bank v)
    (active_bank ports common hl hc v input hi hci)
  apply hh.consequence (fun _ h => h) ?_ le_rfl
  intro x hx
  obtain ⟨small,hs,hx⟩ := hx
  subst small
  subst x
  rw [Placement.replace,extra_eq ports common hl hc v w hframe,
    ← active_bank ports common hl hc w output ho hco,Placement.view]

@[simp] theorem payload_bank (v : Tapes k a) :
    SharedBank.payload (bank (s := s) v) (Fin.castAdd s) = v := by
  cases v
  simp only [SharedBank.payload,bank,Tapes.append,Fin.addCases_left]

theorem strip_bank (v : Tapes k a) :
    SharedBank.strip (bank (s := s) v) (Fin.castAdd s) = SharedBank.empty (k+s) a := by
  have he (i : Fin (k+s)) :
      (SharedBank.strip (bank (s := s) v) (Fin.castAdd s)).head i = 0 ∧
      (SharedBank.strip (bank (s := s) v) (Fin.castAdd s)).tape i = fun _ => blank := by
    induction i using Fin.addCases with
    | left i => simp [SharedBank.strip]
    | right i =>
      have hn : ¬∃ j : Fin k, Fin.castAdd s j = Fin.natAdd k i := by
        rintro ⟨j,hj⟩
        have hv := congrArg Fin.val hj
        simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
        omega
      simp only [SharedBank.strip,hn,↓reduceIte,bank,Tapes.append,Fin.addCases_right,
        SharedBank.empty,and_self]
  apply congrArg₂ Tapes.mk
  · funext i; exact (he i).1
  · funext i; exact (he i).2

/-- A clean local implementation becomes an actual stage on the full permanent
bank, suitable for the existing finite physical sequence compiler. -/
def stage {X : Type*} (commonBank : X → Tapes k a) (M : Program s q a)
    (ports : Fin c → Fin s) (common : Fin c → Fin k)
    (hl : Function.Injective ports) (hc : Function.Injective common)
    (transform : X → X) (input output : X → Tapes s a) (cost : ℕ)
    (hi : ∀ x, SharedBank.payload (input x) ports = SharedBank.payload (commonBank x) common)
    (ho : ∀ x, SharedBank.payload (output x) ports = SharedBank.payload (commonBank (transform x)) common)
    (hci : ∀ x, SharedBank.strip (input x) ports = SharedBank.empty s a)
    (hco : ∀ x, SharedBank.strip (output x) ports = SharedBank.empty s a)
    (hf : ∀ x, SharedBank.strip (commonBank x) common = SharedBank.strip (commonBank (transform x)) common)
    (hh : ∀ x, HoareTime M (fun v => v = input x) (fun v => v = output x) cost) :
    SharedBankStage.Stage X k a commonBank where
  tapes := k+s
  states := q
  program := Placement.placed M (placement ports common hc)
  transform := transform
  input := fun x => bank (commonBank x)
  output := fun x => bank (commonBank (transform x))
  slots := Fin.castAdd s
  slots_injective := Fin.castAdd_injective _ _
  metadata := SharedBank.empty (k+s) a
  cost := cost
  input_payload := fun x => payload_bank (commonBank x)
  output_payload := fun x => payload_bank (commonBank (transform x))
  strip_input := fun x => strip_bank (commonBank x)
  realizes := fun x => realizes M ports common hl hc (commonBank x) (commonBank (transform x))
    (input x) (output x) cost (hi x) (ho x) (hci x) (hco x) (hf x) (hh x)

end
end IntegerMultBounds.Machine.CleanSubbank
