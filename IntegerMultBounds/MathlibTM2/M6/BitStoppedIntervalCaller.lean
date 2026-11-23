module

public import IntegerMultBounds.MathlibTM2.M6.BitStoppedRowEntry
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleReturn

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Node Mult.PhaseCellToeplitz RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Return the stopped transpose to the original caller record, clearing the child
workspace and preserving both stacks on every other caller tape. -/
private theorem seededStoppedInterval [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (table : Unit → Pr Unit N Q prime U)
      (port : Fin N) (master : Fin 6 ↪ Fin N), 0 ≤ C ∧ (∀ i, master i ≠ port) ∧
    ∀ {P : Type} {T : ℕ} (body : P → Pr P T Q prime U) (place : Fin N ↪ Fin T) (entry : Unit → P),
      (∀ f, body (entry f) = embProg place entry (table f)) →
    ∀ (src tmp count saved : Fin T), [count,place port,src,saved,tmp].Nodup →
      (∀ i, place i ≠ src ∧ place i ≠ tmp ∧ place i ≠ count ∧ place i ≠ saved) →
      ∃ code : Pr P T Q prime U,
    ∀ (lane child : Descriptor), let wide := {lane with afterD := lane.afterD*142080}
      ∀ (position : Fin (volume prime child) ≃ Fin (volume prime wide)),
      InheritedIntervalPositions child wide rfl position → lane.width = child.width →
      0 < volume prime lane → 0 < lane.width → ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      RecordPayload src (fun _ => blank) 0 word S → S.L tmp = [] → S.R tmp = [] → S.R (place port) = [] → S.R count = [] → S.R saved = [] →
      (∀ i, S.R (place (master i)) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j, S.L (place j) = []) → (∀ j, j ≠ port → (∀ i, master i ≠ j) → S.R (place j) = []) →
      ∃ z F t changed, Exec body code (mk u S) t (mk z F) ∧
        t ≤ ⌊(C*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊ ∧
        z.user = u.user ∧ RecordPayload src (fun _ => blank) 0 changed F ∧
        (∀ j, changed (position j) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) j) ∧
        (∀ j, F.L (place j) = [] ∧ F.R (place j) = []) ∧
        ∀ j, j ≠ src → (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨C,N,table,worker,port,master,pos,apart,run⟩ := cleanStoppedInterval (U := U) capacity mergeCap
  refine ⟨C+59,N,table,port,master,by positivity,apart,?_⟩
  intro P T body place entry dispatch src tmp count saved distinct outside
  have regs := distinct
  regs_ne regs
  let output := place port
  let write : Pr P T Q prime U := (loadCompactWord output tmp count).seq
    (((usub count src tmp).seq (movePrefix count output src saved tmp)).seq (bclear count))
  refine ⟨((loadCompactWord src tmp output).seq (embProg place entry worker)).seq
    (write.seq (clearWorkTapes [output])),?_⟩
  intro lane child wide position coords width positive live word u S source tl tr fresh hc hs headers left free
  have size : volume prime lane*142080 = volume prime wide := by simp [wide,volume,Nat.mul_assoc]
  have mass := Fintype.card_congr position
  simp only [Fintype.card_fin] at mass
  have reads : WordAtZero word (S.L src) (S.R src) := by
    intro j
    rw [← encodedOwnerCell]
    simpa only [sub_zero,List.map_ofFn] using source j
  obtain ⟨a,initial,load⟩ := loadCompactWord_exec body src tmp (place port) (by simp [‹src ≠ tmp›,(outside port).1.symm,(outside port).2.1.symm]) word u S reads tl tr
  simp only [fresh,List.append_nil] at load
  let E := {S with R := Function.update S.R (place port) (List.ofFn fun i => SparseRoleCircuit.encode (word i))}
  have input : E.R (place port) = _ := (Function.update_self ..).trans (List.ofFn_congr size.symm _)
  have off (j) (ne : j ≠ place port) : E.R j = S.R j := Function.update_of_ne ne ..
  obtain ⟨v,D,t,ran,paid,user,read,clean⟩ := run lane positive live word (embDn place a) (embStk place E)
    input (fun i => (off _ (place.injective.ne (apart i))).trans (headers i)) left
    (fun j away h => (off _ (place.injective.ne away)).trans (free j away h))
  obtain ⟨z,F,exec,_,same,eq,frame⟩ := exec_emb place.injective dispatch ran a rfl E rfl
  rw [← eq] at read clean
  have before : RecordPayload src (fun _ => blank) 0 word F := by
    obtain ⟨l,r⟩ := frame src (fun i => (outside i).1)
    intro k
    rw [l,r,off src (outside port).1.symm]
    exact source k
  have kept (j) (away : ∀ i, place i ≠ j) : F.L j = S.L j ∧ F.R j = S.R j :=
    ⟨(frame j away).1,(frame j away).2.trans (off j (away port).symm)⟩
  have temp := kept tmp (fun i => (outside i).2.1)
  obtain ⟨b,G,n,back,cost,returned,out,empty,rest⟩ := returnIdleBank_exec body distinct [place port]
    (by simp) (by simp) (by simp [(outside port).1.symm]) word _ z F before read
    ((kept count (fun i => (outside i).2.2.1)).2.trans hc)
    ((kept saved (fun i => (outside i).2.2.2)).2.trans hs) (temp.1.trans tl) (temp.2.trans tr)
  refine ⟨b,G,_,_,(load.seq exec).seq back,?_,returned.trans (same.trans (user.trans initial)),out,
    (coords.transpose_iff width word _).2 rfl,?_,?_⟩
  · rw [← eq] at paid
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at cost
    change t+cleanupWeight (F.L (place port)) (F.R (place port)) ≤ _ at paid
    rw [width,size] at paid
    rw [mass]
    unfold cleanupWeight at paid
    let V := volume prime wide
    let power := (child.width : ℝ)^M8.Machine.BudgetBound.tau
    have hv : 0 < V := by
      change 0 < volume prime wide
      rw [← size]
      exact Nat.mul_pos positive (by decide)
    have hw : 1 ≤ (child.width : ℝ) := by exact_mod_cast width ▸ live
    have one : 1 ≤ power := Real.one_le_rpow hw M8.Machine.BudgetBound.exponent_range.1.le
    have charge : 8*V+10+t+n ≤ 59*V+⌊C*power*V⌋₊ := by
      dsimp only [V,power]
      dsimp only [V] at hv
      omega
    apply charge.trans
    apply Nat.le_floor
    push_cast
    have base := Nat.floor_le (show 0 ≤ C*power*V by positivity)
    have scale := mul_le_mul_of_nonneg_right one (Nat.cast_nonneg (α := ℝ) V)
    change 59*(V : ℝ)+(⌊C*power*V⌋₊ : ℝ) ≤ (C+59)*power*V
    linarith only [base,scale]
  · intro j
    by_cases h : j = port
    · subst j
      exact empty _ (by simp)
    · have keep := rest (place j) (outside j).1 (by simpa using place.injective.ne h)
      exact ⟨keep.1.trans (clean j h).1,keep.2.trans (clean j h).2⟩
  · intro j ne away
    have keep := rest j ne (by simpa using (away port).symm)
    exact ⟨keep.1.trans (kept j away).1,keep.2.trans (kept j away).2⟩

/-- Copy the caller's descriptor into blank private tapes, execute the stopped child,
and return the transformed record with the entire private workspace cleared. -/
theorem placedStoppedInterval [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (table : Unit → Pr Unit N Q prime U)
      (port : Fin N) (master : Fin 6 ↪ Fin N), 0 ≤ C ∧ (∀ i, master i ≠ port) ∧
    ∀ {P : Type} {T : ℕ} (body : P → Pr P T Q prime U) (place : Fin N ↪ Fin T) (entry : Unit → P),
      (∀ f, body (entry f) = embProg place entry (table f)) →
    ∀ (src tmp count saved : Fin T), [count,place port,src,saved,tmp].Nodup →
      (∀ i, place i ≠ src ∧ place i ≠ tmp ∧ place i ≠ count ∧ place i ≠ saved) →
      ∀ (headers : Fin 6 → Fin T), (∀ i j, place (master i) ≠ headers j) →
      (∀ i, [headers i,place (master i),tmp,saved].Nodup) →
      ∃ code : Pr P T Q prime U,
    ∀ (lane child : Descriptor), let wide := {lane with afterD := lane.afterD*142080}
      ∀ (position : Fin (volume prime child) ≃ Fin (volume prime wide)),
      InheritedIntervalPositions child wide rfl position → lane.width = child.width →
      0 < volume prime lane → 0 < lane.width → ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      RecordPayload src (fun _ => blank) 0 word S → S.L tmp = [] → S.R tmp = [] → S.R count = [] → S.R saved = [] →
      (∀ i, S.R (headers i) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j, S.L (place j) = [] ∧ S.R (place j) = []) →
      ∃ z F t changed, Exec body code (mk u S) t (mk z F) ∧
        t ≤ ⌊(C*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊ ∧
        z.user = u.user ∧ RecordPayload src (fun _ => blank) 0 changed F ∧
        (∀ j, changed (position j) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) j) ∧
        (∀ j, F.L (place j) = [] ∧ F.R (place j) = []) ∧
        ∀ j, j ≠ src → (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨C,N,table,port,master,pos,apart,build⟩ := seededStoppedInterval (U := U) capacity mergeCap
  refine ⟨C+1,N,table,port,master,by positivity,apart,?_⟩
  intro P T body place entry dispatch src tmp count saved distinct outside headers separate regs
  obtain ⟨call,run⟩ := build body place entry dispatch src tmp count saved distinct outside
  obtain ⟨load,copy⟩ := reloadChildSeed body (master.trans place) headers tmp saved separate regs
  refine ⟨load.seq call,?_⟩
  intro lane child wide position coords width positive live word u S source tl tr hc hs words fresh
  let seed := fun i => (Routines.hdr lane i).map (bitSymbol (a := prime))
  obtain ⟨a,R,k,setup,paid,initial,loaded,keep⟩ := copy seed u S words (fun i => (fresh (master i)).2) tr hs
  have off (j) (away : ∀ i, place i ≠ j) := keep j (fun i => away (master i))
  have srcEq := off src (fun i => (outside i).1)
  obtain ⟨z,F,t,y,exec,cost,user,out,act,clean,frame⟩ := run lane child position coords width positive live
    word a {S with R := R} (fun j => by simpa only [srcEq] using source j) tl
    ((off tmp (fun i => (outside i).2.1)).trans tr)
    ((keep _ (fun i => place.injective.ne (apart i))).trans (fresh port).2)
    ((off count (fun i => (outside i).2.2.1)).trans hc)
    ((off saved (fun i => (outside i).2.2.2)).trans hs) loaded (fun j => (fresh j).1)
    (fun j _ h => (keep _ (fun i => place.injective.ne (h i))).trans (fresh j).2)
  refine ⟨z,F,_,y,setup.seq exec,?_,user.trans initial,out,act,clean,?_⟩
  · have each (i : Fin 6) : 6*(seed i).length+6 ≤ 12*volume prime lane+6 := by
      have len := RecursiveRowsNode.header_length lane (LeafCore.positive_of_volume positive) _ (Routines.hdr_headers lane) i
      simp only [seed,List.length_map]
      omega
    have sum := List.sum_le_length_nsmul ((List.finRange 6).map (fun i => 6*(seed i).length+6)) (12*volume prime lane+6) (fun _ h => by
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
      exact each i)
    have mass := Fintype.card_congr position
    simp only [Fintype.card_fin] at mass
    have size : volume prime wide = volume prime lane*142080 := by simp [wide,volume,Nat.mul_assoc]
    simp only [List.length_map,List.length_finRange,nsmul_eq_mul] at sum
    have kBound : k ≤ volume prime child := by omega
    let power := (child.width : ℝ)^M8.Machine.BudgetBound.tau
    have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast width ▸ live) M8.Machine.BudgetBound.exponent_range.1.le
    have scale := mul_le_mul_of_nonneg_right one (Nat.cast_nonneg (α := ℝ) (volume prime child))
    have base := Nat.floor_le (show 0 ≤ C*power*volume prime child by positivity)
    apply Nat.le_floor
    push_cast
    have clock : (t : ℝ) ≤ (⌊C*power*volume prime child⌋₊ : ℕ) := by exact_mod_cast cost
    have copied : (k : ℝ) ≤ volume prime child := by exact_mod_cast kBound
    change (k : ℝ)+t ≤ (C+1)*power*volume prime child
    linarith only [clock,copied,base,scale]
  · intro j ne away
    exact ⟨(frame j ne away).1,(frame j ne away).2.trans (off j away)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
