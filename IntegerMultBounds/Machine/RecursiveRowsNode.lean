import IntegerMultBounds.Machine.RecursiveRowsNodeRoleBank
import IntegerMultBounds.Machine.RecursiveViewFrameRoleBank
import IntegerMultBounds.Machine.SharedBankFamily
import IntegerMultBounds.Machine.RecursiveStackAllocation

/-! Physical node boundaries: save the original six headers, split cyclic rows,
and install the network descriptor; restore the saved headers before merging.
Each fixed skeleton has a literal common-bank endpoint and blank private work. -/
namespace IntegerMultBounds.Machine.RecursiveRowsNode
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewFrameRoleBank (count bank)
open SharedBankStageInput (raw)
variable {t u c : ℕ}

private theorem leading_compose {k a : ℕ} (s r : SharedBankSkeleton.Skeleton k a)
    (i : Fin k) : ((SharedBankSkeleton.compose s r).slots i).val = i.val := rfl

def splitSkeleton (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires) :
    SharedBankSkeleton.Skeleton (count t u) prime :=
  SharedBankFamily.ofProgram (RecursiveRowsRoleBank.splitProgram
    Shared50ModularControl.prime_prime.two_le (u := 1+u) wires hw)

def mergeSkeleton (rho : Equiv.Perm (Fin c)) (wires : Fin (1+c) → Fin t)
    (hw : Function.Injective wires) : SharedBankSkeleton.Skeleton (count t u) prime :=
  SharedBankFamily.ofProgram (RecursiveRowsRoleBank.mergeProgram
    Shared50ModularControl.prime_prime.two_le (u := 1+u) rho wires hw)

def headerSkeleton (c : ℕ) : SharedBankSkeleton.Skeleton (count t u) prime :=
  SharedBankFamily.ofProgram (RecursiveRowsNodeRoleBank.program (t := t) (u := 1+u) c)

def entry (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires) :=
  SharedBankSkeleton.compose
    (SharedBankSkeleton.compose (RecursiveViewFrameRoleBank.pushSkeleton (t := t) (u := u))
      (splitSkeleton (u := u) wires hw)) (headerSkeleton (t := t) (u := u) c)

def exit (rho : Equiv.Perm (Fin c)) (wires : Fin (1+c) → Fin t)
    (hw : Function.Injective wires) :=
  SharedBankSkeleton.compose (RecursiveViewFrameRoleBank.restoreSkeleton (t := t) (u := u))
    (mergeSkeleton (u := u) rho wires hw)

theorem entry_hoare (wires : Fin (1+c) → Fin t) (hw : Function.Injective wires)
    (hs : Fin 6 → List Bool) (st : Tapes 1 prime) (aux : Tapes u prime)
    (v : Descriptor) (hc : 0 < c) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4) :
    ∃ rs : List Bool, RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.role v c)
      (RecursiveRowsNodeHeaders.headers hs rs) ∧
      HoareTime (entry (u := u) wires hw).program
        (fun w => w = raw (bank (RecursiveRoleSerialization.roles
          (RecursiveRowsSerialization.sourceData wires x)) hs st aux) (entry (u := u) wires hw).tapes)
        (fun w => w = raw (bank (RecursiveRoleSerialization.roles
          (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hd x))
          (RecursiveRowsNodeHeaders.headers hs rs) (RecursiveViewFrame.savedStack hs st) aux)
          (entry (u := u) wires hw).tapes)
        (RecursiveViewFrame.pushCost hs+RecursiveRowsClean.bound c (volume prime v)+
          RecursiveRowsNodeRoleBank.constant c*volume prime v+2) := by
  let before := RecursiveRoleSerialization.roles (RecursiveRowsSerialization.sourceData wires x)
  let after := RecursiveRoleSerialization.roles (RecursiveRowsSerialization.roleData wires (Equiv.refl _) hd x)
  have hpush := RecursiveViewFrameRoleBank.push_hoare before hs st aux
  have hsplit := RecursiveRowsSerialization.split_hoare wires hw hs
    ((RecursiveViewFrame.savedStack hs st).append aux) v hc hv hp hd x
  obtain ⟨rs,hrs,hh⟩ := RecursiveRowsNodeRoleBank.realizes c hc v hp after hs
    ((RecursiveViewFrame.savedStack hs st).append aux) hv
  rw [SharedBankRawCompose.bank_eq_raw,SharedBankRawCompose.bank_eq_raw] at hpush hsplit hh
  have first := SharedBankRawCompose.realizes
    (RecursiveViewFrameRoleBank.pushSkeleton (t := t) (u := u)) (splitSkeleton (u := u) wires hw)
    (fun _ => rfl) (fun _ => rfl) _ _ _ _ _ hpush hsplit
  have full := SharedBankRawCompose.realizes _ (headerSkeleton (t := t) (u := u) c)
    (leading_compose _ _) (fun _ => rfl) _ _ _ _ _ first hh
  refine ⟨rs,hrs,?_⟩
  apply full.consequence (fun _ h => h) (fun _ h => h)
  omega

theorem exit_hoare (rho : Equiv.Perm (Fin c)) (wires : Fin (1+c) → Fin t)
    (hw : Function.Injective wires) (old hs : Fin 6 → List Bool)
    (st : Tapes 1 prime) (aux : Tapes u prime) (hf : RecursiveViewFrame.Free old st)
    (v : Descriptor) (hc : 0 < c) (hv : RecursiveDimensionBank.Headers v old)
    (hp : v.Positive) (hd : c ∣ v.rows) (x : Fin (volume prime v) → Fin 4) :
    HoareTime (exit (u := u) rho wires hw).program
      (fun w => w = raw (bank (RecursiveRoleSerialization.roles
        (RecursiveRowsSerialization.roleData wires rho hd x)) hs (RecursiveViewFrame.savedStack old st) aux)
        (exit (u := u) rho wires hw).tapes)
      (fun w => w = raw (bank (RecursiveRoleSerialization.roles
        (RecursiveRowsSerialization.sourceData wires x)) old st aux) (exit (u := u) rho wires hw).tapes)
      (RecursiveViewFrame.restoreCost old hs+RecursiveRowsClean.bound c (volume prime v)+1) := by
  have hr := RecursiveViewFrameRoleBank.restore_hoare
    (RecursiveRoleSerialization.roles (RecursiveRowsSerialization.roleData wires rho hd x)) old hs st aux hf
  have hm := RecursiveRowsSerialization.merge_hoare rho wires hw old (st.append aux) v hc hv hp hd x
  rw [SharedBankRawCompose.bank_eq_raw,SharedBankRawCompose.bank_eq_raw] at hr hm
  exact SharedBankRawCompose.realizes
    (RecursiveViewFrameRoleBank.restoreSkeleton (t := t) (u := u)) (mergeSkeleton (u := u) rho wires hw)
    (fun _ => rfl) (fun _ => rfl) _ _ _ _ _ hr hm

/-- A blank suffix gives every nested node the space needed for its frame. -/
theorem free_of_available (hs : Fin 6 → List Bool) (st : Tapes 1 prime)
    (hav : RecursiveStackAllocation.Available 0 st) : RecursiveViewFrame.Free hs st :=
  fun z hz _ => hav z hz

theorem saved_available (hs : Fin 6 → List Bool) (st : Tapes 1 prime)
    (hav : RecursiveStackAllocation.Available 0 st) :
    RecursiveStackAllocation.Available 0 (RecursiveViewFrame.savedStack hs st) := by
  have ha : RecursiveStackAllocation.Available RecursiveViewFrame.stack
      (RecursiveViewFrame.bank hs st) := by
    intro z hz
    exact hav z hz
  exact RecursiveStackAllocation.descriptor_saved RecursiveViewFrame.stack
    RecursiveViewFrame.fields (RecursiveViewFrame.words hs) (RecursiveViewFrame.bank hs st) ha

def rowConstant (c : ℕ) :=
  (2+5*RecursiveRowsMove.TapeCount c)*(RecursiveRowsQuotient.constant c+1099)+
    11*RecursiveRowsMove.TapeCount c+4

theorem header_length (v : Descriptor) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) (i : Fin 6) :
    (hs i).length ≤ 2*volume prime v := by
  have hl := RecursiveAffinePrepare.header_log Shared50ModularControl.prime_prime.two_le v hp hs hv i
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hlog := Nat.log2_le_self (volume prime v)
  omega

theorem entry_cost_linear (v : Descriptor) (hp : v.Positive) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers v hs) :
    RecursiveViewFrame.pushCost hs+RecursiveRowsClean.bound c (volume prime v)+
      RecursiveRowsNodeRoleBank.constant c*volume prime v+2 ≤
      (74+rowConstant c+RecursiveRowsNodeRoleBank.constant c)*volume prime v := by
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hp := RecursiveViewFrame.pushCost_le hs _ (header_length v hp hs hv)
  have hr := RecursiveRowsClean.bound_linear c (volume prime v) hV
  change RecursiveRowsClean.bound c (volume prime v) ≤ rowConstant c*volume prime v at hr
  nlinarith

theorem exit_cost_linear (v : Descriptor) (hp : v.Positive) (hc : 0 < c) (hd : c ∣ v.rows)
    (old hs : Fin 6 → List Bool) (ho : RecursiveDimensionBank.Headers v old)
    (hh : RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.role v c) hs) :
    RecursiveViewFrame.restoreCost old hs+RecursiveRowsClean.bound c (volume prime v)+1 ≤
      (128+rowConstant c)*volume prime v := by
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hrole := RecursiveRowsNodeLayout.role_positive c v hc hp hd
  have he := RecursiveInterchangeLayout.role_volume_mul prime c v hd
  have hle : volume prime (RecursiveInterchangeLayout.role v c) ≤ volume prime v := by
    nlinarith [Nat.le_mul_of_pos_right (volume prime (RecursiveInterchangeLayout.role v c)) hc]
  have hnew (i : Fin 6) : (hs i).length ≤ 2*volume prime v :=
    (header_length _ hrole hs hh i).trans (Nat.mul_le_mul_left 2 hle)
  have hr := RecursiveViewFrame.restoreCost_le old hs _ (header_length v hp old ho) hnew
  have hm := RecursiveRowsClean.bound_linear c (volume prime v) hV
  change RecursiveRowsClean.bound c (volume prime v) ≤ rowConstant c*volume prime v at hm
  nlinarith

end
end IntegerMultBounds.Machine.RecursiveRowsNode
