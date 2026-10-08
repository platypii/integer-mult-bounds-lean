import IntegerMultBounds.Machine.RecursiveScalingRoleBank
import IntegerMultBounds.Machine.RecursiveRoleSerialization
import IntegerMultBounds.Machine.CleanSubbankCompile

/-! One fixed physical mixed shift/scaling/XOR sequence on the permanent role
bank. Six layout headers and the XOR volume descriptor are supplied and remain
unchanged throughout this block. Applying different coordinate views requires
separate paid header-regrouping code; recursive calls are not supplied here. -/
namespace IntegerMultBounds.Machine.RecursiveMixedSchedule
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (Target)
open RecursiveRoleSerialization (roles encode)
variable {t u : ℕ}

inductive Op (t : ℕ) where
  | shift (wire : Fin t) (r : ℚ) (denominator : r.den < prime)
  | scale (wire : Fin t) (r : ℚ) (occurs : Shared50AffineCoefficients.ScaleOccurs r) (target : Target)
  | xor (gate : PointwiseRoleGate.Gate t)

abbrev commonCount (t u : ℕ) := t+(7+(2+u))
abbrev Data (t : ℕ) (v : Descriptor) := Fin t → Fin (volume prime v) → Fin 4

def commonBank {v : Descriptor} (hs : Fin 6 → List Bool) (bs : List Bool) (aux : Tapes u prime)
    (data : Data t v) : Tapes (commonCount t u) prime :=
  RecursiveShiftRoleBank.common (roles data) hs ((RecursiveXorRoleBank.controls bs).append aux)

structure Block (k : ℕ) where
  work : ℕ
  states : ℕ
  program : Program (k+work) states prime

/-- Actual machines selected entirely before any runtime layout is supplied. -/
def block (op : Op t) : Block (commonCount t u) := match op with
  | .shift wire r _ => ⟨68,_,RecursiveShiftRoleBank.program (u := 2+u) r wire⟩
  | .scale wire r hr target => ⟨RecursiveInterchangeScalingConstruct.TapeCount r+
      RecursiveInterchangeScalingConstruct.TapeCount r,_,RecursiveScalingRoleBank.program (u := 2+u) hr target wire⟩
  | .xor g => ⟨4,_,RecursiveXorRoleBank.program (u := u) g⟩

def transform {v : Descriptor} : Op t → Data t v → Data t v
  | .shift wire r _, data => Function.update data wire (RecursiveInterchangeShift.array r (data wire))
  | .scale wire _ hr target, data => Function.update data wire (RecursiveInterchangeScaling.array hr (data wire) target)
  | .xor g, data => Function.update data g.dst
      (fun i => PointwiseBinary.xorSymbol (data g.src i) (data g.dst i))

def cost (v : Descriptor) (bs : List Bool) : Op t → ℕ
  | .shift _ _ _ => 221536*volume prime v+32370
  | .scale _ r _ _ => RecursiveInterchangeScalingClean.bound r (volume prime v)
  | .xor _ => 14*volume prime v+14*bs.length+33

private theorem single_hoare {v : Descriptor} (op : Op t) (hs : Fin 6 → List Bool)
    (bs : List Bool) (aux : Tapes u prime) (hv : RecursiveDimensionBank.Headers v hs)
    (hpos : v.Positive) (hn : Counter.value bs = volume prime v) (data : Data t v) :
    HoareTime (block (u := u) op).program
      (fun w => w = CleanSubbank.bank (s := (block (u := u) op).work) (commonBank hs bs aux data))
      (fun w => w = CleanSubbank.bank (s := (block (u := u) op).work)
        (commonBank hs bs aux (transform op data))) (cost v bs op) := by
  cases op with
  | shift wire r hd =>
    simpa only [block,commonBank,transform,cost,RecursiveRoleSerialization.roles_update] using
      RecursiveShiftRoleBank.realizes r wire (roles data) hs ((RecursiveXorRoleBank.controls bs).append aux)
        (data wire) rfl rfl hv hpos
  | scale wire r hr target =>
    simpa only [block,commonBank,transform,cost,RecursiveRoleSerialization.roles_update] using
      RecursiveScalingRoleBank.realizes hr target wire (roles data) hs ((RecursiveXorRoleBank.controls bs).append aux)
        (data wire) rfl rfl hv hpos
  | xor g =>
    simpa only [block,commonBank,transform,cost,RecursiveRoleSerialization.roles_xor] using
      RecursiveXorRoleBank.realizes g (roles data) hs bs aux
        (fun i => encode (data g.src i)) (fun i => encode (data g.dst i)) rfl rfl
        (RecursiveRoleSerialization.source_eq_word _) (RecursiveRoleSerialization.source_eq_word _) hn

/-- The proof-carrying semantic stage erases to `block op` exactly. -/
def stage {v : Descriptor} (hs : Fin 6 → List Bool) (bs : List Bool) (aux : Tapes u prime)
    (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive)
    (hn : Counter.value bs = volume prime v) (op : Op t) :
    SharedBankStage.Stage (Data t v) (commonCount t u) prime (commonBank hs bs aux) where
  tapes := commonCount t u+(block (u := u) op).work
  states := (block (u := u) op).states
  program := (block (u := u) op).program
  transform := transform op
  input := fun data => CleanSubbank.bank (commonBank hs bs aux data)
  output := fun data => CleanSubbank.bank (commonBank hs bs aux (transform op data))
  slots := Fin.castAdd (block (u := u) op).work
  slots_injective := Fin.castAdd_injective _ _
  metadata := SharedBank.empty _ prime
  cost := cost v bs op
  input_payload := fun _ => CleanSubbank.payload_bank _
  output_payload := fun _ => CleanSubbank.payload_bank _
  strip_input := fun _ => CleanSubbank.strip_bank _
  realizes := single_hoare op hs bs aux hv hpos hn

def skeleton (op : Op t) : SharedBankSkeleton.Skeleton (commonCount t u) prime where
  tapes := commonCount t u+(block (u := u) op).work
  states := (block (u := u) op).states
  program := (block (u := u) op).program
  slots := Fin.castAdd (block (u := u) op).work
  slots_injective := Fin.castAdd_injective _ _

/-- Machine, state count, tape count and placements erase all runtime parameters. -/
theorem stage_skeleton {v : Descriptor} (hs : Fin 6 → List Bool) (bs : List Bool) (aux : Tapes u prime)
    (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive)
    (hn : Counter.value bs = volume prime v) (op : Op t) :
    SharedBankSkeleton.ofStage (stage hs bs aux hv hpos hn op) = skeleton (u := u) op := rfl

def machine (ops : List (Op t)) : SharedBankSkeleton.Skeleton (commonCount t u) prime :=
  SharedBankSkeleton.compile (commonCount t u) prime (by unfold commonCount; omega) (ops.map (skeleton (u := u)))

def run {v : Descriptor} (ops : List (Op t)) (data : Data t v) : Data t v :=
  ops.foldl (fun data op => transform op data) data

private theorem execute_stages {v : Descriptor} (hs : Fin 6 → List Bool) (bs : List Bool)
    (aux : Tapes u prime) (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive)
    (hn : Counter.value bs = volume prime v) (ops : List (Op t)) (data : Data t v) :
    SharedBankStage.execute (ops.map (stage hs bs aux hv hpos hn)) data = run ops data := by
  induction ops generalizing data with
  | nil => rfl
  | cons op ops ih => exact ih (transform op data)

private theorem compiled_skeleton {v : Descriptor} (hs : Fin 6 → List Bool) (bs : List Bool)
    (aux : Tapes u prime) (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive)
    (hn : Counter.value bs = volume prime v) (ops : List (Op t)) :
    SharedBankSkeleton.ofStage (SharedBankStage.compile (commonBank hs bs aux) (by unfold commonCount; omega)
      (ops.map (stage hs bs aux hv hpos hn))) = machine (u := u) ops := by
  rw [SharedBankSkeleton.ofStage_compile,List.map_map]
  rfl

private theorem fixed_clean {X : Type*} {k : ℕ} {common : X → Tapes k prime}
    (hk : 0 < k) (ss : List (SharedBankStage.Stage X k prime common))
    (hi : ∀ s ∈ ss, s.metadata = SharedBank.empty s.tapes prime)
    (hc : ∀ s ∈ ss, CleanSubbankCompile.Clean s)
    (sk : SharedBankSkeleton.Skeleton k prime)
    (hsk : SharedBankSkeleton.ofStage (SharedBankStage.compile common hk ss) = sk) (x : X) :
    HoareTime sk.program (fun w => w = SharedBankStageInput.raw (common x) sk.tapes)
      (fun w => w = SharedBankStageInput.raw (common (SharedBankStage.execute ss x)) sk.tapes)
      ((ss.map SharedBankStage.Stage.cost).sum+ss.length) := by
  subst sk
  exact CleanSubbankCompile.realizes hk ss hi hc x

/-- The previously chosen one fixed machine executes the entire mixed list at
all runtime layouts, retaining supplied headers and returning blank work tapes.
The exact bound pays every actual stage and every physical sequential join. -/
theorem realizes {v : Descriptor} (ops : List (Op t)) (hs : Fin 6 → List Bool)
    (bs : List Bool) (aux : Tapes u prime) (hv : RecursiveDimensionBank.Headers v hs)
    (hpos : v.Positive) (hn : Counter.value bs = volume prime v) (data : Data t v) :
    HoareTime (machine (u := u) ops).program
      (fun w => w = SharedBankStageInput.raw (commonBank hs bs aux data) (machine (u := u) ops).tapes)
      (fun w => w = SharedBankStageInput.raw (commonBank hs bs aux (run ops data)) (machine (u := u) ops).tapes)
      ((ops.map (cost v bs)).sum+ops.length) := by
  have hh := fixed_clean (by unfold commonCount; omega : 0 < commonCount t u)
    (ops.map (stage hs bs aux hv hpos hn))
    (by intro s hs; obtain ⟨op,_,rfl⟩ := List.mem_map.mp hs; rfl)
    (by intro s hs; obtain ⟨op,_,rfl⟩ := List.mem_map.mp hs
        intro data; exact CleanSubbank.strip_bank _)
    (machine (u := u) ops) (compiled_skeleton hs bs aux hv hpos hn ops) data
  simpa only [execute_stages,List.map_map,List.length_map,Function.comp_def,stage] using hh


/-- A constant selected solely by each compile-time operation. -/
def coefficient : Op t → ℕ
  | .shift _ _ _ => 253906
  | .scale _ r _ _ => RecursiveInterchangeScalingClean.bound r 1
  | .xor _ => 61

private theorem scaling_bound (r : ℚ) (V : ℕ) (hV : 0 < V) :
    RecursiveInterchangeScalingClean.bound r V ≤ RecursiveInterchangeScalingClean.bound r 1*V := by
  have hh := RecursiveInterchangeScalingClean.bound_linear r V hV
  convert hh using 1
  unfold RecursiveInterchangeScalingClean.bound
  ring

/-- A short supplied volume descriptor suffices for linear cost. Constructing
that descriptor remains a separate physical obligation. -/
theorem cost_le {v : Descriptor} (bs : List Bool) (op : Op t)
    (hV : 0 < volume prime v) (hlen : bs.length ≤ volume prime v) :
    cost v bs op ≤ coefficient op * volume prime v := by
  cases op with
  | shift wire r hd => simp only [cost,coefficient]; omega
  | scale wire r hr target =>
    exact scaling_bound r (volume prime v) hV
  | xor g => simp only [cost,coefficient]; omega

/-- The complete finite block has a compile-time linear coefficient, including
all sequential joins. -/
theorem total_cost_le {v : Descriptor} (bs : List Bool) (ops : List (Op t))
    (hV : 0 < volume prime v) (hlen : bs.length ≤ volume prime v) :
    (ops.map (cost v bs)).sum+ops.length ≤
      ((ops.map coefficient).sum+ops.length)*volume prime v := by
  induction ops with
  | nil => simp
  | cons op ops ih =>
    have hh := cost_le bs op hV hlen
    simp only [List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

/-- The same fixed machine realizes the whole block in linear stream volume. -/
theorem realizes_linear {v : Descriptor} (ops : List (Op t)) (hs : Fin 6 → List Bool)
    (bs : List Bool) (aux : Tapes u prime) (hv : RecursiveDimensionBank.Headers v hs)
    (hpos : v.Positive) (hn : Counter.value bs = volume prime v)
    (hV : 0 < volume prime v) (hlen : bs.length ≤ volume prime v) (data : Data t v) :
    HoareTime (machine (u := u) ops).program
      (fun w => w = SharedBankStageInput.raw (commonBank hs bs aux data) (machine (u := u) ops).tapes)
      (fun w => w = SharedBankStageInput.raw (commonBank hs bs aux (run ops data)) (machine (u := u) ops).tapes)
      (((ops.map coefficient).sum+ops.length)*volume prime v) :=
  (realizes ops hs bs aux hv hpos hn data).consequence (fun _ h => h) (fun _ h => h)
    (total_cost_le bs ops hV hlen)

end
end IntegerMultBounds.Machine.RecursiveMixedSchedule
