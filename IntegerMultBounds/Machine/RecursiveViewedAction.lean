import IntegerMultBounds.Machine.RecursiveViewFrameRoleBank
import IntegerMultBounds.Machine.RecursiveScalingRoleBank

/-! A concrete scalar shift or scaling wrapped in physical parent-header save,
coordinate-view construction, occupied-header cleanup and parent restoration.
The fixed machine changes the selected role data, preserves all auxiliaries,
and returns its dedicated descriptor stack and private work tapes blank. -/
namespace IntegerMultBounds.Machine.RecursiveViewedAction
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewFrameRoleBank (count bank)
open RecursiveViewRoleBank (Selection layout)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
variable {t u m : ℕ}

inductive Action (t : ℕ) where
  | shift (wire : Fin t) (r : ℚ) (denominator : r.den < prime)
  | scale (wire : Fin t) (r : ℚ) (occurs : Shared50AffineCoefficients.ScaleOccurs r)
      (target : RecursiveInterchangeScaling.Target)

abbrev Data (t : ℕ) (v : Descriptor) := Fin t → Fin (volume prime v) → Fin 4

def transform {v : Descriptor} : Action t → Data t v → Data t v
  | .shift wire r _, data => Function.update data wire (RecursiveInterchangeShift.array r (data wire))
  | .scale wire _ hr target, data => Function.update data wire (RecursiveInterchangeScaling.array hr (data wire) target)

def cost (v : Descriptor) : Action t → ℕ
  | .shift _ _ _ => 221536*volume prime v+32370
  | .scale _ r _ _ => RecursiveInterchangeScalingClean.bound r (volume prime v)

def coefficient : Action t → ℕ
  | .shift _ _ _ => 253906
  | .scale _ r _ _ => RecursiveInterchangeScalingClean.bound r 1

def actionSkeleton : Action t → SharedBankSkeleton.Skeleton (count t u) prime
  | .shift wire r _ =>
    { tapes := count t u+68
      states := _
      program := RecursiveShiftRoleBank.program (u := 1+u) r wire
      slots := Fin.castAdd 68
      slots_injective := Fin.castAdd_injective _ _ }
  | .scale wire r hr target =>
    { tapes := count t u+(RecursiveInterchangeScalingConstruct.TapeCount r+RecursiveInterchangeScalingConstruct.TapeCount r)
      states := _
      program := RecursiveScalingRoleBank.program (u := 1+u) hr target wire
      slots := Fin.castAdd _
      slots_injective := Fin.castAdd_injective _ _ }

def viewSkeleton (s : Selection m) : SharedBankSkeleton.Skeleton (count t u) prime where
  tapes := count t u+38
  states := _
  program := RecursiveViewRoleBank.program (t := t) (u := 1+u) s
  slots := Fin.castAdd 38
  slots_injective := Fin.castAdd_injective _ _

def machine (s : Selection m) (act : Action t) : SharedBankSkeleton.Skeleton (count t u) prime :=
  SharedBankSkeleton.compose
    (SharedBankSkeleton.compose
      (SharedBankSkeleton.compose RecursiveViewFrameRoleBank.pushSkeleton (viewSkeleton s))
      (actionSkeleton act)) RecursiveViewFrameRoleBank.restoreSkeleton

private theorem action_slots (act : Action t) (i : Fin (count t u)) :
    ((actionSkeleton (u := u) act).slots i).val = i.val := by cases act <;> rfl

private theorem action_hoare {v : Descriptor} (act : Action t) (hs : Fin 6 → List Bool)
    (st : Tapes 1 prime) (aux : Tapes u prime) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (data : Data t v) :
    HoareTime (actionSkeleton (u := u) act).program
      (fun w => w = raw (bank (roles data) hs st aux) (actionSkeleton (u := u) act).tapes)
      (fun w => w = raw (bank (roles (transform act data)) hs st aux) (actionSkeleton (u := u) act).tapes)
      (cost v act) := by
  cases act with
  | shift wire r hd =>
    simpa only [actionSkeleton,cost,bank,transform,SharedBankRawCompose.bank_eq_raw,RecursiveRoleSerialization.roles_update] using
      RecursiveShiftRoleBank.realizes r wire (roles data) hs (st.append aux) (data wire) rfl rfl hv hp
  | scale wire r hr target =>
    simpa only [actionSkeleton,cost,bank,transform,SharedBankRawCompose.bank_eq_raw,RecursiveRoleSerialization.roles_update] using
      RecursiveScalingRoleBank.realizes hr target wire (roles data) hs (st.append aux) (data wire) rfl rfl hv hp

private theorem scaling_cost (r : ℚ) (V : ℕ) (hV : 0 < V) :
    RecursiveInterchangeScalingClean.bound r V ≤ RecursiveInterchangeScalingClean.bound r 1*V := by
  have hh := RecursiveInterchangeScalingClean.bound_linear r V hV
  convert hh using 1
  unfold RecursiveInterchangeScalingClean.bound
  ring

private theorem action_cost (act : Action t) (v : Descriptor) (hV : 0 < volume prime v) :
    cost v act ≤ coefficient act*volume prime v := by
  cases act with
  | shift wire r hd => simp only [cost,coefficient]; omega
  | scale wire r hr target => exact scaling_cost r _ hV

private theorem layout_positive (s : Selection m) (b : ℕ) (v : Descriptor) (hp : v.Positive) :
    (layout s b v).Positive := by
  have hq : 0 < prime := Shared50ModularControl.prime_prime.pos
  cases s with
  | cross i j =>
    rcases hp with ⟨hA,hR,hB,hC,hE⟩
    dsimp [layout,RecursiveAffineViews.cross,RecursiveInterchangeLayout.child,Descriptor.Positive]
    rw [Nat.div_one]
    exact ⟨hA,hR,Nat.mul_pos hB (pow_pos hq _),
      Nat.mul_pos (Nat.mul_pos (pow_pos hq _) hC) (pow_pos hq _),Nat.mul_pos (pow_pos hq _) hE⟩
  | within g j i hj =>
    cases g
    · exact RecursiveAffineViews.withinH_positive prime b hq v hp j i
    · exact RecursiveAffineViews.withinD_positive prime b hq v hp j i

def viewData (s : Selection m) (b : ℕ) (v : Descriptor) (hw : v.width=m*b) (data : Data t v) :
    Data t (layout s b v) := fun wire => RecursiveAffineViews.array prime (RecursiveViewRoleBank.layout_volume s b v hw) (data wire)

/-- Exact final role tapes; their payload type uses the selected coordinate
view, while the restored bank again contains the original parent headers. -/
def outputRoles (s : Selection m) (act : Action t) (b : ℕ) (v : Descriptor) (hw : v.width=m*b) (data : Data t v) :=
  roles (transform act (viewData s b v hw data))

/-- One fixed machine executes all four actual stages. The dedicated stack
starts and ends wholly blank, and the six original parent headers are exact. -/
theorem realizes (s : Selection m) (act : Action t) (b : ℕ) (v : Descriptor) (hw : v.width=m*b)
    (hp : v.Positive) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (aux : Tapes u prime) (data : Data t v) :
    HoareTime (machine (u := u) s act).program
      (fun w => w = raw (bank (roles data) hs (SharedBank.empty 1 prime) aux) (machine (u := u) s act).tapes)
      (fun w => w = raw (bank (outputRoles s act b v hw data) hs (SharedBank.empty 1 prime) aux)
        (machine (u := u) s act).tapes)
      ((RecursiveViewRoleBank.constant s+coefficient act+202)*volume prime v) := by
  let st := SharedBank.empty 1 prime
  let saved := RecursiveViewFrame.savedStack hs st
  obtain ⟨ch,hch,hview⟩ := RecursiveViewRoleBank.realizes s b v hw hp (roles data) hs (saved.append aux) hv
  have hpush := RecursiveViewFrameRoleBank.push_hoare (roles data) hs st aux
  have hact := action_hoare act ch saved aux hch (layout_positive s b v hp) (viewData s b v hw data)
  have hrestore := RecursiveViewFrameRoleBank.restore_hoare (outputRoles s act b v hw data) hs ch st aux
    (RecursiveViewFrame.free_empty hs)
  simp only [SharedBankRawCompose.bank_eq_raw] at hpush hview hrestore
  have hroles := RecursiveViewRoleBank.roles_view s b v hw data
  change roles (viewData s b v hw data) = roles data at hroles
  rw [hroles] at hact
  have hfirst := SharedBankRawCompose.realizes
    (RecursiveViewFrameRoleBank.pushSkeleton (t := t) (u := u)) (viewSkeleton (t := t) (u := u) s)
    (fun _ => rfl) (fun _ => rfl) _ _ _ _ _ hpush hview
  have hsecond := SharedBankRawCompose.realizes
    (SharedBankSkeleton.compose (RecursiveViewFrameRoleBank.pushSkeleton (t := t) (u := u)) (viewSkeleton (t := t) (u := u) s))
    (actionSkeleton (u := u) act) (fun _ => rfl) (action_slots act) _ _ _ _ _ hfirst hact
  have hthird := SharedBankRawCompose.realizes
    (SharedBankSkeleton.compose
      (SharedBankSkeleton.compose (RecursiveViewFrameRoleBank.pushSkeleton (t := t) (u := u)) (viewSkeleton (t := t) (u := u) s))
      (actionSkeleton (u := u) act)) (RecursiveViewFrameRoleBank.restoreSkeleton (t := t) (u := u))
    (fun _ => rfl) (fun _ => rfl) _ _ _ _ _ hsecond hrestore
  apply hthird.consequence (fun _ h => h) (fun _ h => h) ?_
  have hq := Shared50ModularControl.prime_prime.two_le
  have hV := RecursiveAffinePrepare.volume_positive hq v hp
  have hvol := RecursiveViewRoleBank.layout_volume s b v hw
  have hold (i : Fin 6) : (hs i).length ≤ 2*volume prime v := by
    have hh := RecursiveAffinePrepare.header_log hq v hp hs hv i
    have hl := Nat.log2_le_self (volume prime v)
    omega
  have hnew (i : Fin 6) : (ch i).length ≤ 2*volume prime v := by
    have hh := RecursiveAffinePrepare.header_log hq _ (layout_positive s b v hp) ch hch i
    rw [hvol] at hh
    have hl := Nat.log2_le_self (volume prime v)
    omega
  have hpc := RecursiveViewFrame.pushCost_le hs (2*volume prime v) hold
  have hrc := RecursiveViewFrame.restoreCost_le hs ch (2*volume prime v) hold hnew
  have hac := action_cost act (layout s b v) (by rw [hvol]; exact hV)
  rw [hvol] at hac
  nlinarith


/-- Express the changed payload in the caller's original dependent array type.
This cast changes no serialized symbol and requires no machine transition. -/
def array (s : Selection m) (act : Action t) (b : ℕ) (v : Descriptor) (hw : v.width=m*b)
    (data : Data t v) : Data t v := fun wire =>
  RecursiveAffineViews.array prime (RecursiveViewRoleBank.layout_volume s b v hw).symm
    (transform act (viewData s b v hw data) wire)

theorem outputRoles_eq (s : Selection m) (act : Action t) (b : ℕ) (v : Descriptor) (hw : v.width=m*b)
    (data : Data t v) : outputRoles s act b v hw data = roles (array s act b v hw data) := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext wire
    change FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0
        (List.ofFn (transform act (viewData s b v hw data) wire))) =
      FlatRepeatedControlNormalize.encoded (putWord (fun _ => blank) 0
        (List.ofFn (RecursiveAffineViews.array prime (RecursiveViewRoleBank.layout_volume s b v hw).symm
          (transform act (viewData s b v hw data) wire))))
    rw [RecursiveAffineViews.array_word]

/-- Parent-to-parent clean contract, ready for the next independently selected
field operation on the same fixed role and header bank. -/
theorem realizes_array (s : Selection m) (act : Action t) (b : ℕ) (v : Descriptor) (hw : v.width=m*b)
    (hp : v.Positive) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
    (aux : Tapes u prime) (data : Data t v) :
    HoareTime (machine (u := u) s act).program
      (fun w => w = raw (bank (roles data) hs (SharedBank.empty 1 prime) aux) (machine (u := u) s act).tapes)
      (fun w => w = raw (bank (roles (array s act b v hw data)) hs (SharedBank.empty 1 prime) aux)
        (machine (u := u) s act).tapes)
      ((RecursiveViewRoleBank.constant s+coefficient act+202)*volume prime v) := by
  simpa only [outputRoles_eq] using realizes s act b v hw hp hs hv aux data

end
end IntegerMultBounds.Machine.RecursiveViewedAction
