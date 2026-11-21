module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperLabelRun
public import IntegerMultBounds.MathlibTM2.M6.BitOwnerRead
public import IntegerMultBounds.MathlibTM2.M6.BitHelperSlotSchedule

/-! Slot changes on the represented permanent owner bank of a PR589 invocation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

def HelperFan {k T V : ℕ} (fan : Fin (k+2) ↪ Fin T) (data : Fin k → Fin V → ZMod 2) (S : Stacks T prime) :=
  RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
    (SparseRoleCircuit.encoded data) (FlatCoordinateSchedule.bits V)) (embStk fan S).L (embStk fan S).R

private theorem fanEncoded {k V : ℕ} (data : Fin k → Fin V → ZMod 2) (j : Fin k) :
    SparseRoleCircuit.encoded (a := prime) data j = fun i => SparseRoleCircuit.encode (data j i) := rfl

private theorem fanPayload {k T V : ℕ} {fan : Fin (k+2) ↪ Fin T} {data : Fin k → Fin V → ZMod 2}
    {S : Stacks T prime} (rep : HelperFan fan data S) (owner : Fin k) :
    RecordPayload (fan (owner.castAdd 2)) (fun _ => blank) 0 (data owner) S := by
  intro z
  rw [encodedOwnerCell]
  simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,fanEncoded] using (rep (owner.castAdd 2) z).symm

private theorem fanUpdate {k T V : ℕ} {fan : Fin (k+2) ↪ Fin T} {data : Fin k → Fin V → ZMod 2}
    {S F : Stacks T prime} (owner : Fin k) (word : Fin V → ZMod 2) (rep : HelperFan fan data S)
    (payload : RecordPayload (fan (owner.castAdd 2)) (fun _ => blank) 0 word F)
    (keep : ∀ j, j ≠ owner.castAdd 2 → F.L (fan j) = S.L (fan j) ∧ F.R (fan j) = S.R (fan j)) :
    HelperFan fan (Function.update data owner word) F := by
  intro i
  refine Fin.addCases (fun j z => ?_) (fun j z => ?_) i
  · by_cases same : j = owner
    · subst j
      have cell := payload z
      rw [encodedOwnerCell] at cell
      simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,
        Function.comp_apply,fanEncoded,Function.update_self] using cell.symm
    · obtain ⟨l,r⟩ := keep (j.castAdd 2) ((Fin.castAddEmb 2).injective.ne same)
      simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,
        fanEncoded,Function.update_of_ne same,l,r] using rep (j.castAdd 2) z
  · have ne : j.natAdd k ≠ owner.castAdd 2 := by
      intro e; have h := congrArg Fin.val e; simp at h; omega
    obtain ⟨l,r⟩ := keep _ ne
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,l,r]
      using rep (j.natAdd k) z

/-- Repack a single owner directly inside the invocation's represented bank.
The invocation retains both loop controls and the exact stacks on all other caller tapes. -/
theorem helperFanSlot_exec [M8.Machine.Net] {k T Q : ℕ} {P U : Type}
    (fan : Fin (k+2) ↪ Fin T) (owner : Fin k) (src dst : Option (Fin 56))
    (capacity : columnCapacity ≤ Q) (body : P → Pr P (T+LeafCore.small) Q prime U)
    (headers : ℕ → Fin 6 → Fin T) (separate : ∀ i j, headers i j ≠ fan (owner.castAdd 2)) :
    let full := fan.trans (Fin.castAddEmb LeafCore.small)
    ∃ (code : Pr P (T+LeafCore.small) Q prime U) (C : ℝ), ∀ {w L W : ℕ} {v : Descriptor},
      volume prime v = (prime^w)^16*(L*((prime^w)^112*W)) → 0 < volume prime v →
      ∀ (data : Fin k → Fin (volume prime v) → ZMod 2) u S,
      (∀ i : Fin 127, ∀ j, S.R ((headers i.val j).castAdd LeafCore.small) =
        (Routines.hdr (helperAdjacentView w L W i) j).map bitSymbol) →
      HelperFan full data S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ z F t, ∃ word : Fin (volume prime v) → ZMod 2, z.user = u.user ∧
        Exec body code (mk u S) t (mk z F) ∧ (t : ℝ) ≤ C*((volume prime v : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        HelperFan full (Function.update data owner word) F ∧
        (∀ c s (label : Fin L) (j : Fin W), ext word (helperFieldCell (helperSlotField c dst w s) label j) =
          ext (data owner) (helperFieldCell (helperSlotField c src w s) label j)) ∧
        (∀ j : Fin T, j ≠ fan (owner.castAdd 2) → F.L (j.castAdd LeafCore.small) = S.L (j.castAdd LeafCore.small) ∧
          F.R (j.castAdd LeafCore.small) = S.R (j.castAdd LeafCore.small)) ∧
        ∀ j : Fin LeafCore.small, F.L (j.natAdd T) = [] ∧ F.R (j.natAdd T) = [] := by
  intro full
  obtain ⟨code,C,run⟩ := helperLabelSlot_exec src dst capacity body headers (fan (owner.castAdd 2)) separate
  refine ⟨code,C,?_⟩
  intro w L W v size pos data u S stored rep free
  obtain ⟨z,F,t,word,user,exec,paid,out,read,keep,clean⟩ :=
    run size pos (data owner) u S stored (fanPayload rep owner) free
  exact ⟨z,F,t,word,user,exec,paid,fanUpdate owner word rep out (fun j ne => keep _ (fan.injective.ne ne)),read,keep,clean⟩

def HelperLabelTrace {k V : ℕ} (w L W : ℕ) (changes : List (Fin k × Option (Fin 56) × Option (Fin 56)))
    (data result : Fin k → Fin V → ZMod 2) : Prop :=
  changes.foldr (fun (owner,src,dst) next a => ∃ word,
    (∀ c s (label : Fin L) (j : Fin W), ext word (helperFieldCell (helperSlotField c dst w s) label j) =
      ext (a owner) (helperFieldCell (helperSlotField c src w s) label j)) ∧
      next (Function.update a owner word)) (· = result) data

/-- Run the ordered helper changes against a single represented invocation bank.
Archive and leaf workspace are reused at each change. -/
theorem helperFanChanges_exec [M8.Machine.Net] {k T Q : ℕ} {P U : Type}
    (fan : Fin (k+2) ↪ Fin T) (changes : List (Fin k × Option (Fin 56) × Option (Fin 56)))
    (capacity : columnCapacity ≤ Q) (body : P → Pr P (T+LeafCore.small) Q prime U)
    (headers : ℕ → Fin 6 → Fin T) (apart : ∀ i j (o : Fin k), headers i j ≠ fan (o.castAdd 2)) :
    let full := fan.trans (Fin.castAddEmb LeafCore.small)
    ∃ (code : Pr P (T+LeafCore.small) Q prime U) (C : ℝ), ∀ {w L W : ℕ} {v : Descriptor},
      volume prime v = (prime^w)^16*(L*((prime^w)^112*W)) → 0 < volume prime v →
      ∀ (data : Fin k → Fin (volume prime v) → ZMod 2) u S,
      (∀ i : Fin 127, ∀ j, S.R ((headers i.val j).castAdd LeafCore.small) =
        (Routines.hdr (helperAdjacentView w L W i) j).map bitSymbol) →
      HelperFan full data S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      ∃ z F t result, z.user = u.user ∧ Exec body code (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ C*((volume prime v : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        HelperFan full result F ∧ HelperLabelTrace w L W changes data result ∧
        (∀ j : Fin T, (∀ o : Fin k, j ≠ fan (o.castAdd 2)) → F.L (j.castAdd LeafCore.small) = S.L (j.castAdd LeafCore.small) ∧
          F.R (j.castAdd LeafCore.small) = S.R (j.castAdd LeafCore.small)) ∧
        ∀ j : Fin LeafCore.small, F.L (j.natAdd T) = [] ∧ F.R (j.natAdd T) = [] := by
  intro full
  induction changes with
  | nil =>
    refine ⟨.act .done,1,?_⟩
    intro w L W v _ pos data u S _ rep free
    refine ⟨u,S,1,data,rfl,Exec.act ..,?_,rep,rfl,fun _ _ => ⟨rfl,rfl⟩,free⟩
    have vol : (1 : ℝ) ≤ volume prime v := by exact_mod_cast (show 1 ≤ volume prime v from pos)
    simpa using one_le_mul_of_one_le_of_one_le vol (Real.one_le_rpow
      (by exact_mod_cast le_max_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le)
  | cons change changes ih =>
    obtain ⟨o,src,dst⟩ := change
    obtain ⟨pack,A,step⟩ := helperFanSlot_exec fan o src dst capacity body headers (fun i j => apart i j o)
    obtain ⟨tail,B,rest⟩ := ih
    refine ⟨.seq pack tail,A+B,?_⟩
    intro w L W v size pos data u S stored rep free
    obtain ⟨y,D,m,word,same,run,price,represented,read,keep,clear⟩ := step size pos data u S stored rep free
    obtain ⟨z,F,n,result,user,exec,paid,done,trace,off,clean⟩ := rest size pos _ y D
      (fun i j => ((keep _ (apart _ _ o)).2).trans (stored i j)) represented clear
    refine ⟨z,F,m+n,result,user.trans same,Exec.seq run exec,?_,done,⟨word,read,trace⟩,?_,clean⟩
    · rw [Nat.cast_add,add_mul]; exact add_le_add price paid
    · intro j hj
      exact ⟨(off j hj).1.trans (keep j (hj o)).1,(off j hj).2.trans (keep j (hj o)).2⟩

theorem labelTrace_off {k V w L W : ℕ} (changes : List (Fin k × Option (Fin 56) × Option (Fin 56)))
    (data out : Fin k → Fin V → ZMod 2) (trace : HelperLabelTrace w L W changes data out)
    (t : Fin k) (off : ∀ p ∈ changes, p.1 ≠ t) : out t = data t := by
  induction changes generalizing data with
  | nil => exact congrFun trace.symm t
  | cons p ps ih =>
    obtain ⟨word,_,tail⟩ := trace
    rw [ih _ tail (fun q hq => off q (List.mem_cons_of_mem _ hq)),Function.update_of_ne
      (Ne.symm (off p List.mem_cons_self))]

private theorem labelTrace_read {k V w L W : ℕ} (changes : List (Fin k × Option (Fin 56) × Option (Fin 56)))
    (data out : Fin k → Fin V → ZMod 2) (trace : HelperLabelTrace w L W changes data out)
    (unique : (changes.map Prod.fst).Nodup) (t : Fin k) (src dst : Option (Fin 56))
    (hit : (t,src,dst) ∈ changes) (c : Certificates.PR589.Nine.PortCertificate) s (label : Fin L) (j : Fin W) :
    ext (out t) (helperFieldCell (helperSlotField c dst w s) label j) =
      ext (data t) (helperFieldCell (helperSlotField c src w s) label j) := by
  induction changes generalizing data with
  | nil => simp at hit
  | cons p ps ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp unique
    obtain ⟨word,read,tail⟩ := trace
    rcases List.mem_cons.mp hit with eqn | mem
    · subst p
      rw [labelTrace_off ps _ _ tail t (fun q hq eq => fresh (List.mem_map.mpr ⟨q,hq,eq⟩)),Function.update_self]
      exact read c s label j
    · rw [ih _ tail nd mem,Function.update_of_ne]
      intro eqn
      exact fresh (eqn ▸ List.mem_map_of_mem mem)

/-- Restore only tapes whose helper slot is still installed. -/
@[irreducible] def restoreSlotChanges {k : ℕ} (slot : Fin k → Option (Fin 56)) :=
  ((List.finRange k).filter fun t => (slot t).isSome).map fun t => (t, slot t, (none : Option (Fin 56)))

theorem restoreSlot_off {k V w L W : ℕ} (slot : Fin k → Option (Fin 56)) {data out : Fin k → Fin V → ZMod 2}
    (trace : HelperLabelTrace w L W (restoreSlotChanges slot) data out) (t : Fin k) (empty : slot t = none) :
    out t = data t := by
  apply labelTrace_off _ _ _ trace
  rintro q mem eqn
  unfold restoreSlotChanges at mem
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp mem
  change a = t at eqn
  subst a
  simpa [empty] using (List.mem_filter.mp ha).2

theorem restoreSlot_read {k V w L W : ℕ} (slot : Fin k → Option (Fin 56)) {data out : Fin k → Fin V → ZMod 2}
    (trace : HelperLabelTrace w L W (restoreSlotChanges slot) data out) (t : Fin k)
    (c : Certificates.PR589.Nine.PortCertificate) s (label : Fin L) (j : Fin W) :
    ext (out t) (helperFieldCell (helperSlotField c none w s) label j) =
      ext (data t) (helperFieldCell (helperSlotField c (slot t) w s) label j) := by
  cases h : slot t with
  | none => rw [restoreSlot_off slot trace t h]
  | some pos =>
    have unique : ((restoreSlotChanges slot).map Prod.fst).Nodup := by
      simpa [restoreSlotChanges,List.map_map,Function.comp_def] using
        (List.nodup_finRange k).filter (fun t => (slot t).isSome)
    apply labelTrace_read _ _ _ trace unique
    unfold restoreSlotChanges
    exact List.mem_map.mpr ⟨t,List.mem_filter.mpr ⟨List.mem_finRange _,by simp [h]⟩,by simp [h]⟩

theorem scheduledLabelRead (n : Fin 9) (p : Fin 32 × Fin 5) (before) {V w L W : ℕ}
    (data out : Fin 142081 → Fin V → ZMod 2)
    (trace : HelperLabelTrace w L W (scheduledSlotChanges n p before) data out) (h : Fin 439) :
    let change := helperSlotChange n p before h
    ∀ c s (label : Fin L) (j : Fin W),
      ext (out change.1) (helperFieldCell (helperSlotField c change.2.2 w s) label j) =
        ext (data change.1) (helperFieldCell (helperSlotField c change.2.1 w s) label j) := by
  intro change c s label j
  by_cases same : change.2.1 = change.2.2
  · rw [same]
    have untouched : out change.1 = data change.1 := by
      apply labelTrace_off _ _ _ trace
      rintro q mem eqn
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp mem
      have ij := congrArg Fin.val (ownerTape_injective n p.1 p.2 eqn)
      have kh : k = h := Fin.ext (Nat.add_left_cancel ij)
      subst k
      exact (bne_iff_ne.mp (List.mem_filter.mp hk).2) same
    rw [untouched]
  · apply labelTrace_read _ _ _ trace (scheduledSlotChanges_unique ..)
    exact List.mem_map.mpr ⟨h,List.mem_filter.mpr ⟨List.mem_finRange _,bne_iff_ne.mpr same⟩,rfl⟩

/-- Run the changes selected by the sweep history, then enter the supplied
invocation on its original tapes. Its recursive time allowance is added once. -/
theorem scheduledLabelCall_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (n : Fin 9) (p : Fin 32 × Fin 5) (prefixRuns : List (Fin 32 × Fin 5))
    (fan : Fin (142081+2) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (body : P → Pr P T Q prime U) (headers : ℕ → Fin 6 → Fin T)
    (apart : ∀ i j (o : Fin 142081), headers i j ≠ fan (o.castAdd 2)) :
    let bank := Fin.castAddEmb LeafCore.small (n := T)
    let full := fan.trans bank
    let outer := fun f => embProg bank id (body f)
    let before := prefixRuns.foldl (fun c r => helperChartsAfter n r c) (fun _ => none)
    ∃ pack, ∃ C : ℝ, ∀ {w L W : ℕ} {v : Descriptor},
      volume prime v = (prime^w)^16*(L*((prime^w)^112*W)) → 0 < volume prime v →
      ∀ (data : Fin 142081 → Fin (volume prime v) → ZMod 2) u S call (price : ℕ)
        (effect : (Fin 142081 → Fin (volume prime v) → ZMod 2) → (Fin 142081 → Fin (volume prime v) → ZMod 2) → Prop),
      (∀ i : Fin 127, ∀ j, S.R (bank (headers i.val j)) = (Routines.hdr (helperAdjacentView w L W i) j).map bitSymbol) →
      HelperFan full data S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd T) = [] ∧ S.R (j.natAdd T) = []) →
      (∀ a y D, HelperFan fan a D →
        (∀ j, (∀ h, fan h ≠ j) → D.L j = S.L (bank j) ∧ D.R j = S.R (bank j)) →
        ∃ z F m b, Exec body call (mk y D) m (mk z F) ∧ m ≤ price ∧ z.user = y.user ∧ HelperFan fan b F ∧ effect a b) →
      ∃ z F t a b, Exec outer (.seq pack (embProg bank id call)) (mk u S) t (mk z F) ∧
        (t : ℝ) ≤ C*((volume prime v : ℝ)*((max 1 w : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)+price ∧
        z.user = u.user ∧ HelperFan full b F ∧ effect a b ∧
        (∀ j, (∀ h : Fin 439, (helperSlotChange n p before h).1 ≠ j) → a j = data j) ∧
        ∀ h : Fin 439, let change := helperSlotChange n p before h
          ∀ c s (label : Fin L) (j : Fin W), ext (a change.1) (helperFieldCell (helperSlotField c change.2.2 w s) label j) =
            ext (data change.1) (helperFieldCell (helperSlotField c change.2.1 w s) label j) := by
  intro bank full outer before
  obtain ⟨pack,C,run⟩ := helperFanChanges_exec fan (scheduledSlotChanges n p before) capacity outer headers apart
  refine ⟨pack,C,?_⟩
  intro w L W v size pos data u S call price effect stored rep free invoke
  obtain ⟨y,D,k,a,user,packed,paid,ready,trace,keep,_⟩ := run size pos data u S stored rep free
  obtain ⟨z,F,m,b,exec,bill,same,done,act⟩ := invoke a (embDn bank y) (embStk bank D) ready
    (fun j off => keep j (fun o => (off (o.castAdd 2)).symm))
  obtain ⟨z',F',placed,_,state,view,_⟩ := exec_emb (ι := id) (body' := outer) bank.injective
    (fun _ => rfl) exec y rfl D rfl
  refine ⟨z',F',k+m,a,b,Exec.seq packed placed,?_,state.trans (same.trans user),?_,act,?_,
    scheduledLabelRead n p before _ _ trace⟩
  · rw [Nat.cast_add]; exact add_le_add paid (by exact_mod_cast bill)
  · rw [← view] at done; exact done
  · intro j off
    apply labelTrace_off _ _ _ trace
    rintro q mem
    obtain ⟨h,_,rfl⟩ := List.mem_map.mp mem
    exact off h

end IntegerMultBounds.MathlibTM2.M6.BitNode
