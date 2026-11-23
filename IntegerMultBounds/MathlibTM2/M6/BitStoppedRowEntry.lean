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

theorem stoppedIntervalEntry [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (program : Pr Empty N Q prime U)
      (src : Fin (142081+2) ↪ Fin N) (slots : Fin 6 ↪ Fin N), 0 ≤ C ∧
    ∀ {T : ℕ} {A : Type} (host : A → Pr A T Q prime U) (place : Fin N ↪ Fin T)
      (entry : A) (_dispatch : host entry = embProg place Empty.elim program)
      (splitter : Fin intervalSplitTapes ↪ Fin T) (tmp aux : Fin T) (master : Fin 6 → Fin T),
      let live := (intervalOwners 142080).trans splitter
      let saved := (mergeSaved 142080).trans splitter
      (∀ i j, saved i ≠ place j) →
      (∀ (r : Fin 142080) (i : Fin 142081), live (r.castAdd 2) ≠ place (src (i.castAdd 2))) →
      (∀ r : Fin 142080, live (r.castAdd 2) ≠ tmp) →
      (∀ i : Fin 142081, place (src (i.castAdd 2)) ≠ tmp) →
      (∀ j : Fin 2, place (src (j.natAdd 142081)) = live (j.natAdd 142080)) →
      (∀ i j, place (slots i) ≠ live j) → (∀ i j, place (slots i) ≠ master j) →
      (∀ i, [master i,place (slots i),tmp,aux].Nodup) →
      (∀ i, splitter i ≠ tmp ∧ splitter i ≠ aux) → (∀ i j, splitter i ≠ master j) →
      (∀ j, (∀ i : Fin 2, src (i.natAdd 142081) ≠ j) → ∀ i, splitter i ≠ place j) →
      ∃ (code : Pr A T Q prime U) (bank : Fin intervalSplitTapes ↪ Fin T), bank 0 = splitter 0 ∧ ∀ (lane : Descriptor), let V := volume prime lane
      let wide := {lane with afterD := lane.afterD*142080}
      let size : V*142080 = volume prime wide := by simp [V,wide,volume,Nat.mul_assoc]
      0 < V → 0 < lane.width → ∀ (input : Fin (volume prime wide) → ZMod 2) u S,
      S.R (splitter 0) = List.ofFn (fun k => SparseRoleCircuit.encode (a := prime) (input (k.cast size))) →
      (∀ j, S.L (splitter j) = []) → (∀ j, j ≠ 0 → S.R (splitter j) = []) →
      S.L tmp = [] → S.R tmp = [] → S.R aux = [] →
      (∀ i, S.R (master i) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j, (∀ i : Fin 2, src (i.natAdd 142081) ≠ j) → S.L (place j) = [] ∧ S.R (place j) = []) →
      let y := fun k : Fin (V*142080) => Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) input (k.cast size)
      let rows := fun r (i : Fin V) => y (finProdFinEquiv (i,r))
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧
        t ≤ ⌊(C*(lane.width : ℝ)^M8.Machine.BudgetBound.tau)*(V*142080 : ℕ)⌋₊ ∧
        z.user = u.user ∧ RepT (intervalOwnerBank (putWord (fun _ => blank) 0
          (List.ofFn fun k => SparseRoleCircuit.encode (y k))) rows) (embStk bank F).L (embStk bank F).R := by
  obtain ⟨C,N,program,src,dst,slots,pos,leaf⟩ := stoppedRowEntry (U := U) capacity
  let overhead := 2*(149*(intervalSplitTapes+5))+35
  refine ⟨C+overhead,N,program,src,slots,by positivity,?_⟩
  intro T A host place entry dispatch splitter tmp aux master live saved outside apart srcTmp dstTmp controls ownerOff masterOff regs splitAux splitMaster splitPrivate
  obtain ⟨call,run⟩ := leaf host place entry dispatch live tmp aux master apart srcTmp dstTmp controls ownerOff masterOff regs
  let returned := (childReturnFan dst).trans place
  have separate i j : saved i ≠ returned j := outside i _
  let bank := returnedMergeBank saved returned separate
  let merge : Pr A T Q prime U := embProg bank Empty.elim (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) mergeCap))
  let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
    (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) mergeCap))
  refine ⟨(embProg splitter Empty.elim split).seq (call.seq merge),bank,returnedMergeBank_target _ _ _,?_⟩
  intro lane V wide size positive width input u S source left empty tl tr auxFree words free y rows
  let data := fun r (i : Fin V) => input ((finProdFinEquiv (i,r)).cast size)
  let original := putWord (fun _ => blank) 0 (List.ofFn fun k => SparseRoleCircuit.encode (a := prime) (input (k.cast size)))
  obtain ⟨a,E,d,prepare,initial,splitBill,represented,off⟩ := splitEncoded_exec host splitter mergeCap positive
    (fun k => input (k.cast size)) u S source left empty
  have tmpFrame := off tmp (fun i => (splitAux i).1)
  obtain ⟨v,D,k,exec,paid,user,owners,clean,frame⟩ := run lane positive width data a E
    (intervalOwners_ready original data _ represented) (tmpFrame.1.trans tl) (tmpFrame.2.trans tr)
    ((off aux (fun i => (splitAux i).2)).2.trans auxFree) (fun i => (off _ (fun j => splitMaster j i)).2.trans (words i))
    (fun j h => ⟨(off _ (splitPrivate j h)).1.trans (free j h).1,(off _ (splitPrivate j h)).2.trans (free j h).2⟩)
  have changed : (fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)) = rows := by
    funext r i
    exact (transpose_trailingRows lane 142080 input i r).symm
  rw [changed] at owners
  obtain ⟨z,F,n,ran,bill,same,result,_⟩ := mergeAfterReturnedRowsWithCost host call saved returned separate
    mergeCap positive original data rows (embStk splitter E) a E represented exec user owners
    (fun i => frame _ (fun j => (outside i j).symm))
  have merged (k : Fin (V*142080)) : rows (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1 = y k :=
    congrArg y (finProdFinEquiv.apply_symm_apply k)
  simp only [merged] at result
  have overwrite : putWord original 0 (List.ofFn fun k => SparseRoleCircuit.encode (a := prime) (y k)) =
      putWord (fun _ => blank) 0 (List.ofFn fun k => SparseRoleCircuit.encode (a := prime) (y k)) :=
    FlatControlledShiftArray.overwrite _ _ _ _ (by simp)
  rw [overwrite] at result
  refine ⟨z,F,_,prepare.seq ran,?_,same.trans initial,result⟩
  let power := (lane.width : ℝ)^M8.Machine.BudgetBound.tau
  let mass := V*142080
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast width) M8.Machine.BudgetBound.exponent_range.1.le
  have massPos : 0 < mass := Nat.mul_pos positive (by decide)
  have reindex : 149*mass*(intervalSplitTapes+5) = (149*(intervalSplitTapes+5))*mass := by ring
  change n ≤ k+(149*mass*(intervalSplitTapes+5)+6) at bill
  change d ≤ (149*(intervalSplitTapes+5)+5)*mass+24 at splitBill
  change k ≤ ⌊C*power*mass⌋₊ at paid
  have joint : d+n ≤ ⌊C*power*mass⌋₊+overhead*mass := by
    rw [reindex] at bill
    rw [Nat.add_mul] at splitBill
    dsimp only [overhead]
    rw [Nat.add_mul,Nat.mul_assoc]
    omega
  apply joint.trans
  apply Nat.le_floor
  have base : 0 ≤ C*power*mass := by positivity
  have scale := mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α := ℝ) overhead)
  rw [mul_one] at scale
  change ((⌊C*power*mass⌋₊+overhead*mass : ℕ) : ℝ) ≤ (C+overhead)*power*mass
  calc
    _ = (⌊C*power*mass⌋₊ : ℝ)+(overhead : ℝ)*mass := by norm_cast
    _ ≤ C*power*mass+((overhead : ℝ)*power)*mass :=
      add_le_add (Nat.floor_le base) (mul_le_mul_of_nonneg_right scale (Nat.cast_nonneg mass))
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.M6.BitNode
