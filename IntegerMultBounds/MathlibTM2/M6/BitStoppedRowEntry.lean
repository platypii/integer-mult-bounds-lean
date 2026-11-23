module

public import IntegerMultBounds.MathlibTM2.M6.BitStoppedRoleHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitParkedPackedChild

/-! Execute the base case of the recursive row caller with six descriptor words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

theorem stoppedRowEntry [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (program : Pr Empty N Q prime U)
      (src dst : Fin (142081+2) ↪ Fin N) (slots : Fin 6 ↪ Fin N), 0 ≤ C ∧
    ∀ {T : ℕ} {A : Type} (host : A → Pr A T Q prime U) (place : Fin N ↪ Fin T)
      (entry : A) (_dispatch : host entry = embProg place Empty.elim program)
      (live : Fin (142080+2) ↪ Fin T) (tmp aux : Fin T) (master : Fin 6 → Fin T),
      (∀ (r : Fin 142080) (i : Fin 142081), live (r.castAdd 2) ≠ place (src (i.castAdd 2))) →
      (∀ r : Fin 142080, live (r.castAdd 2) ≠ tmp) →
      (∀ i : Fin 142081, place (src (i.castAdd 2)) ≠ tmp) →
      (∀ j : Fin 2, place (src (j.natAdd 142081)) = live (j.natAdd 142080)) →
      (∀ i j, place (slots i) ≠ live j) → (∀ i j, place (slots i) ≠ master j) →
      (∀ i, [master i,place (slots i),tmp,aux].Nodup) →
      ∃ code, ∀ (lane : Descriptor), let V := volume prime lane
      0 < V → 0 < lane.width → ∀ (data : Fin 142080 → Fin V → ZMod 2) u S,
      HelperFan live data S → S.L tmp = [] → S.R tmp = [] → S.R aux = [] →
      (∀ i, S.R (master i) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j, (∀ i : Fin 2, src (i.natAdd 142081) ≠ j) → S.L (place j) = [] ∧ S.R (place j) = []) →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧
        t ≤ ⌊(C*(lane.width : ℝ)^M8.Machine.BudgetBound.tau)*(V*142080 : ℕ)⌋₊ ∧
        z.user = u.user ∧ HelperFan ((childReturnFan dst).trans place) (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)) F ∧
        (∀ j, (∀ i, childReturnFan dst i ≠ j) → F.L (place j) = [] ∧ F.R (place j) = []) ∧
        ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨C,N,table,program,src,dst,slots,pos,privateSlots,sameControls,leaf⟩ :=
    stoppedRoleSeedCleanupCost (U := U) capacity
  let extra := 4*N+133+142081*20+4
  refine ⟨C+extra,N,program,src,dst,slots,by positivity,?_⟩
  intro T A host place entry dispatch live tmp aux master apart srcTmp dstTmp controls ownerOff masterOff regs
  obtain ⟨code,run⟩ := descriptorPackedRowEntry table host place Empty.elim (fun p => nomatch p)
    live src dst tmp apart srcTmp dstTmp controls sameControls slots master aux privateSlots ownerOff masterOff regs entry program dispatch
  refine ⟨code,?_⟩
  intro lane V positive width data u S ready tl tr auxFree words free
  obtain ⟨seed,headers,blank,transposes⟩ := leaf lane lane (Equiv.refl _) positive width rfl (fun _ => rfl)
  obtain ⟨z,F,t,exec,paid,same,out,clean,frame⟩ := run lane seed _ positive headers blank (by
    intro x v D rows stock
    obtain ⟨y,G,n,a,ran,cost,user,result,act⟩ := transposes x v D rows stock
    exact ⟨y,G,n,a,ran,cost,user,result,fun r => funext (act r)⟩)
    data u S ready tl tr auxFree words free
  refine ⟨z,F,t,exec,?_,same,out,clean,frame⟩
  let power := (lane.width : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast width) M8.Machine.BudgetBound.exponent_range.1.le
  have scale : (V : ℝ) ≤ (V*142080 : ℕ) := by exact_mod_cast Nat.le_mul_of_pos_right V (by decide : 0 < 142080)
  have absorb : (extra : ℝ)*V ≤ (extra*power)*(V*142080 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α := ℝ) extra)
    rw [mul_one] at h
    exact mul_le_mul h scale (Nat.cast_nonneg _) (by positivity)
  have base : 0 ≤ C*power*(V*142080 : ℕ) := by positivity
  apply paid.trans
  apply Nat.le_floor
  change ((⌊C*power*(V*142080 : ℕ)⌋₊+extra*V : ℕ) : ℝ) ≤ (C+extra)*power*(V*142080 : ℕ)
  push_cast at base absorb ⊢
  rw [add_mul,add_mul]
  exact add_le_add (Nat.floor_le base) absorb

end IntegerMultBounds.MathlibTM2.M6.BitNode
