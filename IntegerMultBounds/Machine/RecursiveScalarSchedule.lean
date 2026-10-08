import IntegerMultBounds.Machine.RecursiveScalarTransport

/-! Fixed finite varying-view scalar schedules on one permanent role bank.
Every scalar stage physically saves, constructs and restores its descriptor
view, so successive operations start with the identical original headers. -/
namespace IntegerMultBounds.Machine.RecursiveScalarSchedule
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveScalarCoordinates (Address index field)
open RecursiveScalarSelection (compile)
open RecursiveViewedAction (Data)
open RecursiveViewFrameRoleBank (count bank)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
variable {m b t u : ℕ} {v : Descriptor}
local instance : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩

abbrev Op (m : ℕ) := FlatCoordinateSchedule.Op (m+m)

def step (wire : Fin t) (op : Op m) : SharedBankSkeleton.Skeleton (count t u) prime :=
  RecursiveViewedAction.machine (compile wire op).selection (compile wire op).action

def stepCoefficient (wire : Fin t) (op : Op m) : ℕ :=
  RecursiveViewRoleBank.constant (compile wire op).selection+RecursiveViewedAction.coefficient (compile wire op).action+202

def transform (wire : Fin t) (op : Op m) (hw : v.width=m*b) (data : Data t v) : Data t v :=
  RecursiveViewedAction.array (compile wire op).selection (compile wire op).action b v hw data

/-- All transition tables depend only on the fixed scalar list and role number. -/
def machine (wire : Fin t) (ops : List (Op m)) : SharedBankSkeleton.Skeleton (count t u) prime :=
  SharedBankSkeleton.compile (count t u) prime (by unfold count; omega) (ops.map (step (u := u) wire))

def run (wire : Fin t) (ops : List (Op m)) (hw : v.width=m*b) (data : Data t v) : Data t v :=
  ops.foldl (fun data op => transform wire op hw data) data

def coefficient (wire : Fin t) (ops : List (Op m)) : ℕ :=
  (ops.map (stepCoefficient wire)).sum+ops.length

theorem machine_slots (wire : Fin t) (ops : List (Op m)) (i : Fin (count t u)) :
    ((machine (u := u) wire ops).slots i).val = i.val := by
  cases ops <;> rfl

/-- Every real sequential join is charged, and every stage returns its private
work and descriptor stack blank before the next selected view is constructed. -/
theorem realizes_exact (wire : Fin t) (ops : List (Op m)) (hw : v.width=m*b)
    (hp : v.Positive) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (aux : Tapes u prime) (data : Data t v) :
    HoareTime (machine (u := u) wire ops).program
      (fun w => w = raw (bank (roles data) hs (SharedBank.empty 1 prime) aux) (machine (u := u) wire ops).tapes)
      (fun w => w = raw (bank (roles (run wire ops hw data)) hs (SharedBank.empty 1 prime) aux)
        (machine (u := u) wire ops).tapes)
      ((ops.map (stepCoefficient wire)).sum*volume prime v+ops.length) := by
  induction ops generalizing data with
  | nil =>
    convert skip_hoare (t := count t u) (a := prime) (by unfold count; omega)
      (raw (bank (roles data) hs (SharedBank.empty 1 prime) aux) (count t u)) using 1 <;>
      first | rfl | simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons op ops ih =>
    have hh := SharedBankRawCompose.realizes (step (u := u) wire op) (machine (u := u) wire ops)
      (fun _ => rfl) (machine_slots wire ops) _ _ _ _ _
      (RecursiveViewedAction.realizes_array (compile wire op).selection (compile wire op).action b v hw hp hs hv aux data)
      (ih (transform wire op hw data))
    convert hh using 1 <;> first | rfl |
      (simp only [List.map_cons,List.sum_cons,List.length_cons,stepCoefficient]; ring)

/-- The complete fixed varying-view program has linear cost in the original
stream volume, including header construction, stack operations and all joins. -/
theorem realizes (wire : Fin t) (ops : List (Op m)) (hw : v.width=m*b)
    (hp : v.Positive) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (aux : Tapes u prime) (data : Data t v) :
    HoareTime (machine (u := u) wire ops).program
      (fun w => w = raw (bank (roles data) hs (SharedBank.empty 1 prime) aux) (machine (u := u) wire ops).tapes)
      (fun w => w = raw (bank (roles (run wire ops hw data)) hs (SharedBank.empty 1 prime) aux)
        (machine (u := u) wire ops).tapes)
      (coefficient wire ops*volume prime v) := by
  apply (realizes_exact wire ops hw hp hs hv aux data).consequence (fun _ h => h) (fun _ h => h)
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  unfold coefficient
  nlinarith

/-- Scalar address execution in the same order as the actual fixed list. -/
def execute (ops : List (Op m)) (x : Address m b v) : Address m b v :=
  ops.foldl (fun x op => RecursiveScalarTransport.execute (op.action b) x) x

/-- Final selected-wire array has the original ordered scalar-list semantics. -/
theorem run_entry (wire : Fin t) (ops : List (Op m)) (hw : v.width=m*b)
    (data : Data t v) (x : Address m b v) :
    run wire ops hw data wire (index hw (execute ops x)) = data wire (index hw x) := by
  induction ops generalizing data x with
  | nil => rfl
  | cons op ops ih =>
    change run wire ops hw (transform wire op hw data) wire
      (index hw (execute ops (RecursiveScalarTransport.execute (op.action b) x))) = _
    rw [ih]
    exact RecursiveScalarTransport.compile_entry wire op hw data x

/-- No non-selected role changes anywhere in the entire scalar segment. -/
theorem run_other (wire : Fin t) (ops : List (Op m)) (hw : v.width=m*b)
    (data : Data t v) (other : Fin t) (hne : other ≠ wire) :
    run wire ops hw data other = data other := by
  induction ops generalizing data with
  | nil => rfl
  | cons op ops ih =>
    change run wire ops hw (transform wire op hw data) other = _
    rw [ih]
    exact RecursiveScalarTransport.compile_other wire op hw data other hne

/-- Its coordinate state is exactly the original ordered-affine run. -/
theorem field_execute (ops : List (Op m)) (x : Address m b v) :
    field (execute ops x) = OrderedAffine.run (ops.map (fun op => op.action b)) (field x) := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    change field (execute ops (RecursiveScalarTransport.execute (op.action b) x)) = _
    rw [ih,RecursiveScalarTransport.field_execute]
    rfl

/-- Install a scalar coordinate state while preserving every heterogeneous
spectator and row. This is semantic notation, not a free tape operation. -/
def replaceFields (x : Address m b v) (f : Fin (m+m) → ZMod (modulus b)) : Address m b v :=
  {x with h := fun i => f (AffineFieldCoordinates.hIndex i)
          d := fun i => f (AffineFieldCoordinates.dIndex i)}

theorem replaceFields_field (x : Address m b v) : replaceFields x (field x) = x := by
  simp only [replaceFields,RecursiveScalarCoordinates.field_h,RecursiveScalarCoordinates.field_d]

/-- Full address equality includes preservation of all five spectator fields. -/
theorem execute_eq (ops : List (Op m)) (x : Address m b v) :
    execute ops x = replaceFields x (OrderedAffine.run (ops.map (fun op => op.action b)) (field x)) := by
  induction ops generalizing x with
  | nil => exact (replaceFields_field x).symm
  | cons op ops ih =>
    change execute ops (RecursiveScalarTransport.execute (op.action b) x) = _
    rw [ih,RecursiveScalarTransport.field_execute]
    cases op <;> rfl

end
end IntegerMultBounds.Machine.RecursiveScalarSchedule
