module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Switch
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.ShearSem
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSegment

/-!
# The atomwise shears on the core's bank

A shear of the top view `u` of `n` atoms of `w` digits runs in three pieces (`program`): a
straight-line routine sets the segment's counters, `n` atoms and the loop count `n - 1`, from the
width header and the atom width (`setList`); the segment's chain runs on the role data
(`NodeSegment.place`); the counters are erased (`cleanList`). `shear_phase`: on the core's bank the
shear moves the array by the atomwise shear `d ← s h d` of `Stage2Wrapper`, within
`C (n + 1) V`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.ShearRun

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open SharedBankStageInput (raw)
open SharedBankFamily (padProgram)
open FlatCoordinateSchedule (bits)
open Stage2Wrapper (Moves shear)
open RevMachine
open RevMachine.AtomRoleSegment (SOp chain chainData chainConst bankSize tapesOf)
open CommonBank (count)
open Core (Phase)
open Place (memo Slot sel)
open Straight (Instr State words execs Pres costs)
open Switch (B placed)

local instance (w : ℕ) : NeZero (prime ^ w) :=
  ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

local instance (w : ℕ) : NeZero (modulus w) :=
  ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

abbrev tR := NodeBank.tapes rev97m

/-- The I/O role. -/
abbrev io : Fin tR := NodeBank.io rev97m

/-! ### The counters -/

/-- The segment's counters: `n` atoms on counter `5` and the loop count on counter `8`. -/
def segC (w n : ℕ) : Fin CommonBank.K → Option ℕ :=
  Function.update (Function.update (Prepare.rest w 529) 5 (some n)) 8 (some (n - 1))

theorem segCounters (w n : ℕ) : NodeSegment.SegCounters (segC w n) w n where
  c0 := rfl
  c1 := rfl
  c2 := rfl
  c3 := rfl
  c4 := rfl
  c5 := rfl
  c6 := rfl
  c7 := rfl
  c8 := rfl

/-- From the width `e` at slot `3`, the atom width `w` at `4` and one at `5`: `e / w` and
`e / w - 1` at slots `6, 7`, the segment's counters. -/
def setList : List Instr := [.div 3 4 6 8 (by decide), .erase 8, .diff 6 5 7 (by decide)]

def setRoute : Fin 22 → Option Slot :=
  ![none, none, none, some (.header 3), some (.aux 0), some (.aux 15), some (.aux 5), some (.aux 8),
    none, none, none, none, none, none, none, none, none, none, none, none, none, none]

theorem setRoute_inj : Function.Injective (sel setRoute) := by decide

def setIn (e w : ℕ) : State :=
  ![none, none, none, some e, some w, some 1, none, none,
    none, none, none, none, none, none, none, none, none, none, none, none, none, none]

def setOut (e w : ℕ) : State :=
  ![none, none, none, some e, some w, some 1, some (e / w), some (e / w - 1),
    none, none, none, none, none, none, none, none, none, none, none, none, none, none]

theorem set_exec (e w : ℕ) : execs prime setList (setIn e w) = setOut e w := by
  funext i
  fin_cases i <;> simp [execs, Straight.exec1, Straight.val, setList, setIn, setOut]

theorem set_pres {e w : ℕ} (hw : 0 < w) (hn : 1 ≤ e / w) : Pres prime setList (setIn e w) := by
  simp [Pres, Straight.Pre, Straight.exec1, Straight.val, setList, setIn, hw, hn]

/-- Erase the segment's counters. -/
def cleanList : List Instr := [.erase 6, .erase 7]

def cleanRoute : Fin 22 → Option Slot :=
  ![none, none, none, none, none, none, some (.aux 5), some (.aux 8),
    none, none, none, none, none, none, none, none, none, none, none, none, none, none]

theorem cleanRoute_inj : Function.Injective (sel cleanRoute) := by decide

def cleanIn (n : ℕ) : State :=
  ![none, none, none, none, none, none, some n, some (n - 1),
    none, none, none, none, none, none, none, none, none, none, none, none, none, none]

theorem clean_exec (n : ℕ) : execs prime cleanList (cleanIn n) = fun _ => none := by
  funext i
  fin_cases i <;> simp [execs, Straight.exec1, cleanList, cleanIn]

theorem clean_pres (n : ℕ) : Pres prime cleanList (cleanIn n) := by
  simp [Pres, Straight.Pre, Straight.exec1, cleanList, cleanIn]

/-! ### The pieces on the common bank -/

variable {f : ℤ → Fin (prime+4)} {p : ℤ} {node : Tapes 1 prime} {E : ℕ} {st : Tapes 2 prime}

theorem set_runs (roles : Tapes tR prime) (u : Descriptor) {w n : ℕ} (hw : 0 < w) (hwn : u.width = n * w)
    (hn : 1 ≤ n) :
    HoareTime (placed setList setRoute setRoute_inj).program
      (fun z => z = raw (CommonBank.bank roles (Routines.hdr u) f p node (memo E) (Prepare.rest w 529) st)
        (count tR + 22))
      (fun z => z = raw (CommonBank.bank roles (Routines.hdr u) f p node (memo E) (segC w n) st) (count tR + 22))
      (costs prime setList (setIn u.width w)) := by
  have hdiv : u.width / w = n := by rw [hwn, Nat.mul_div_cancel _ hw]
  refine Place.memo_runs setRoute setRoute_inj
    (Straight.runs (Nat.Prime.two_le Networks.Shared50ModularControl.prime_prime) _ _ (set_pres hw (hdiv ▸ hn)))
    (Routines.hdr u) (segC w n) (fun i => ?_) (fun i => ?_) (fun _ _ => rfl) (fun j hj => ?_)
  · fin_cases i <;> simp [words, setIn, sel, setRoute, Slot.value, Routines.hdr, RecursiveDimensionBank.values,
      CommonBank.word, Prepare.rest]
  · rw [set_exec]
    fin_cases i <;> simp [words, setOut, sel, setRoute, Slot.value, Routines.hdr, RecursiveDimensionBank.values,
      CommonBank.word, Prepare.rest, segC, hdiv]
  · have h5 : j ≠ 5 := fun h => hj 6 (by rw [h]; rfl)
    have h8 : j ≠ 8 := fun h => hj 7 (by rw [h]; rfl)
    simp [segC, Function.update_of_ne h5, Function.update_of_ne h8]

theorem clean_runs (roles : Tapes tR prime) (hs : Fin 6 → List Bool) (w n : ℕ) :
    HoareTime (placed cleanList cleanRoute cleanRoute_inj).program
      (fun z => z = raw (CommonBank.bank roles hs f p node (memo E) (segC w n) st) (count tR + 22))
      (fun z => z = raw (CommonBank.bank roles hs f p node (memo E) (Prepare.rest w 529) st) (count tR + 22))
      (costs prime cleanList (cleanIn n)) := by
  refine Place.memo_runs cleanRoute cleanRoute_inj
    (Straight.runs (Nat.Prime.two_le Networks.Shared50ModularControl.prime_prime) _ _ (clean_pres n))
    hs (Prepare.rest w 529) (fun i => ?_) (fun i => ?_) (fun _ _ => rfl) (fun j hj => ?_)
  · fin_cases i <;> simp [words, cleanIn, sel, cleanRoute, Slot.value, CommonBank.word, segC]
  · rw [clean_exec]
    fin_cases i <;> simp [words, sel, cleanRoute, Slot.value, CommonBank.word, Prepare.rest]
  · have h5 : j ≠ 5 := fun h => hj 6 (by rw [h]; rfl)
    have h8 : j ≠ 8 := fun h => hj 7 (by rw [h]; rfl)
    simp [segC, Function.update_of_ne h5, Function.update_of_ne h8]

/-! ### The chain -/

/-- The segments' common tape count. -/
def T' : ℕ := tR + 15 + (bankSize io ShearSem.ops₁ + bankSize io ShearSem.ops₂ + bankSize io ShearSem.ops₃)

theorem T'_ge : tR + 15 ≤ T' := by unfold T'; omega

theorem fits₁ : ∀ s ∈ ShearSem.ops₁, tapesOf io s ≤ T' :=
  fun s hs => (AtomRoleSegment.bankSize_ge io _ s hs).trans (by unfold T'; omega)

theorem fits₂ : ∀ s ∈ ShearSem.ops₂, tapesOf io s ≤ T' :=
  fun s hs => (AtomRoleSegment.bankSize_ge io _ s hs).trans (by unfold T'; omega)

theorem fits₃ : ∀ s ∈ ShearSem.ops₃, tapesOf io s ≤ T' :=
  fun s hs => (AtomRoleSegment.bankSize_ge io _ s hs).trans (by unfold T'; omega)

/-- The chain of a segment placed on the common bank. -/
def chainP (l : List (SOp 1)) (hl : ∀ s ∈ l, tapesOf io s ≤ T') :=
  NodeSegment.place (chain T' io l hl).2 T'_ge

/-- The role data holding the array `X` on the I/O role. -/
def data₀ (u : Descriptor) (X : ℕ → ZMod 2) : RecursiveViewedAction.Data tR u :=
  Function.update (fun _ _ => blank) io (Shared50RecursiveNodeSemantics.encoded (fun i : Fin (volume prime u) => X i))

theorem roles_io {u : Descriptor} (data : RecursiveViewedAction.Data tR u) (h : ∀ i, i ≠ io → data i = fun _ => blank) :
    RecursiveRoleSerialization.roles data = NodePark.childRoles rev97m (RecursiveShiftRoleBank.source (data io)) := by
  apply NodePark.childRoles_unique
  · intro i hi
    refine ⟨rfl, ?_⟩
    change RecursiveShiftRoleBank.source (data i) = _
    rw [h i hi]
    exact RecursiveRowsSerialization.source_blank u
  · exact ⟨rfl, rfl⟩

theorem rolesAt_data₀ (u : Descriptor) (X : ℕ → ZMod 2) :
    FamilyStep.rolesAt u X = RecursiveRoleSerialization.roles (data₀ u X) := by
  rw [roles_io _ (fun i hi => by simp [data₀, hi])]
  simp [data₀]
  rfl

/-- **One shear.** -/
def program {N : ℕ} (hN₁ : count tR + 22 ≤ N) (hN₂ : count tR + (T' + 2) ≤ N) (l : List (SOp 1))
    (hl : ∀ s ∈ l, tapesOf io s ≤ T') :=
  seq (seq (padProgram (placed setList setRoute setRoute_inj).program hN₁) (padProgram (chainP l hl).program hN₂))
    (padProgram (placed cleanList cleanRoute cleanRoute_inj).program hN₁)

/-- The cost of one shear. -/
def cost (l : List (SOp 1)) (u : Descriptor) (w n : ℕ) : ℕ :=
  costs prime setList (setIn u.width w) + 1 + chainConst io l * n * volume prime u + 1 +
    costs prime cleanList (cleanIn n)

/-- **A shear on the core's bank.** A segment changing the tail atoms to `g h d`, with `g` lifting
to the atomwise `s`, moves the array of the view `u` of `n ≥ 1` atoms of `w` digits by the atomwise
shear `d ← s h d`. -/
theorem shear_phase {N : ℕ} (hN₁ : count tR + 22 ≤ N) (hN₂ : count tR + (T' + 2) ≤ N)
    {u : Descriptor} {w n : ℕ} (hp : u.Positive) (hw : 0 < w) (hwn : u.width = n * w) (hn : 1 ≤ n)
    (l : List (SOp 1)) (hl : ∀ s ∈ l, tapesOf io s ≤ T')
    {g : ZMod (modulus w) → ZMod (modulus w) → ZMod (modulus w)} (hlin : ShearSem.Lin (f := n) (b := w) l g)
    {s : Stage2Wrapper.Atoms (prime ^ w) n → Stage2Wrapper.Atoms (prime ^ w) n → Stage2Wrapper.Atoms (prime ^ w) n}
    (hs : ∀ h d, ShearSem.lift g n h d = s (Stage2Wrapper.dec (prime ^ w) n h) (Stage2Wrapper.dec (prime ^ w) n d)) :
    Phase (program hN₁ hN₂ l hl) (B f p node E (Prepare.rest w 529) st N) u u
      (Moves prime u (shear (prime ^ w) n s)) (cost l u w n) := by
  intro X
  have hf : 0 < n := hn
  have hw' : u.width = (1*n)*w := by rw [one_mul]; exact hwn
  set data := data₀ u X
  have hch := AtomRoleSegment.chain_hoare hw T' hf io u hw' hp (Routines.hdr u) (Routines.hdr_headers u) l hl data
  have hseg := NodeSegment.seg_runs (fs := f) (p := p) (node := node) (scalar := memo E) (st := st) T'_ge
    (Routines.hdr u) (segCounters w n)
    (hch.consequence (fun _ h => h) (fun _ h => h) (AtomRoleSegment.chainCost_le hw hf io u hw' hp l))
  have hbits := SegmentBits.chain_bits hf io u hw' l data (fun i => ⟨X i, by simp [data, data₀,
    Shared50RecursiveNodeSemantics.encoded]⟩)
  choose y hy using hbits
  have hroles : RecursiveRoleSerialization.roles (chainData hf io u hw' l data) =
      FamilyStep.rolesAt u (FamilyRoot.ext y) := by
    rw [roles_io _ (fun i hi => by rw [AtomRoleSegment.chain_other hf io u hw' i hi]; simp [data, data₀, hi]),
      FamilyStep.rolesAt_ext]
    unfold FamilyRoot.rolesOf
    congr 2
    funext i
    exact hy i
  have h₁ := SharedBankFamily.pad_realizes hN₁ (Nat.le_add_right _ _) _ _ _
    (set_runs (f := f) (p := p) (node := node) (E := E) (st := st) (RecursiveRoleSerialization.roles data) u hw hwn hn)
  have h₂ := SharedBankFamily.pad_realizes hN₂ (Nat.le_add_right _ _) _ _ _ hseg
  have h₃ := SharedBankFamily.pad_realizes hN₁ (Nat.le_add_right _ _) _ _ _
    (clean_runs (f := f) (p := p) (node := node) (E := E) (st := st) (RecursiveRoleSerialization.roles
      (chainData hf io u hw' l data)) (Routines.hdr u) w n)
  refine ((h₁.seq h₂).seq h₃).consequence (fun z hz => ?_) (fun z hz => ⟨FamilyRoot.ext y, ?_, ?_⟩) le_rfl
  · rw [hz, B, Leaf.leafBank, rolesAt_data₀]
  · exact ShearSem.chain_moves hlin hs hf hw' io data X (fun i => by simp [data, data₀,
      Shared50RecursiveNodeSemantics.encoded]) y hy
  · rw [hz, B, Leaf.leafBank, hroles]

/-- Generated counters and their erasure are linear in active volume. -/
theorem boundary_costs {u : Descriptor} {w n : ℕ} (hp : u.Positive) (hw : 0 < w)
    (hwn : u.width = n*w) (hn : 1 ≤ n) :
    costs prime setList (setIn u.width w)+costs prime cleanList (cleanIn n)+2 ≤
      200000*volume prime u := by
  have hV := RecursiveAffinePrepare.volume_positive (Nat.Prime.two_le Networks.Shared50ModularControl.prime_prime) u hp
  have he := Switch.width_le hp
  have hwe : w ≤ u.width := by rw [hwn]; exact Nat.le_mul_of_pos_left w hn
  have hne : n ≤ u.width := by rw [hwn]; exact Nat.le_mul_of_pos_right n hw
  have h₁ := Switch.costs_le (l := setList) (M := volume prime u) (s := setIn u.width w) (by
      intro i x hx
      fin_cases i <;> simp [setIn] at hx <;> subst hx
      · exact he
      · exact hwe.trans he
      · exact hV)
    (by simp [Straight.OkAll, Straight.Ok, setList, setIn])
  have h₃ := Switch.costs_le (l := cleanList) (M := volume prime u) (s := cleanIn n) (by
      intro i x hx
      fin_cases i <;> simp [cleanIn] at hx <;> subst hx
      · exact hne.trans he
      · exact (Nat.sub_le _ _).trans (hne.trans he))
    (by simp [Straight.OkAll, Straight.Ok, cleanList, cleanIn])
  rw [show setList.length = 3 from rfl] at h₁
  rw [show cleanList.length = 2 from rfl] at h₃
  nlinarith

/-- The cost of a shear is linear in the atoms. -/
theorem cost_le (l : List (SOp 1)) {u : Descriptor} {w n : ℕ} (hp : u.Positive) (hw : 0 < w)
    (hwn : u.width = n*w) (hn : 1 ≤ n) :
    cost l u w n ≤ (chainConst io l+200000)*(n+1)*volume prime u := by
  have h := boundary_costs hp hw hwn hn
  unfold cost
  nlinarith only [h]

/-! ### The three shears -/

theorem hs₁ (w n h d : ℕ) : ShearSem.lift (Q := modulus w) (fun h d => d - h) n h d =
    (fun h d => d - h) (Stage2Wrapper.dec (prime ^ w) n h) (Stage2Wrapper.dec (prime ^ w) n d) :=
  ShearSem.lift_sub n h d

theorem hs₂ (w n h d : ℕ) : ShearSem.lift (Q := modulus w) (fun h d => d + h) n h d =
    (fun h d => d + h) (Stage2Wrapper.dec (prime ^ w) n h) (Stage2Wrapper.dec (prime ^ w) n d) :=
  ShearSem.lift_add n h d

theorem hs₃ (w n h d : ℕ) : ShearSem.lift (Q := modulus w) (fun h d => h - d) n h d =
    (fun h d => h - d) (Stage2Wrapper.dec (prime ^ w) n h) (Stage2Wrapper.dec (prime ^ w) n d) :=
  ShearSem.lift_rsub n h d

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.ShearRun
