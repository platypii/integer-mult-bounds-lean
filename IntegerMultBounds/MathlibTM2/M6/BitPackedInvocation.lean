module

public import IntegerMultBounds.MathlibTM2.M6.BitHelperSlotSchedule
public import IntegerMultBounds.MathlibTM2.M6.BitOwnerRead

/-! Place the helper packing workspace and run the next invocation on the shared owners. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

private theorem placeClosedRun {P U : Type} {t k q r A : ℕ} (bank : Fin k ↪ Fin t)
    (capacity : r ≤ q) (positive : 0 < r) (body : P → Pr P t q A U) (code : Pr Empty k r A U)
    (v : HS t q A U) (S : Stacks t A) {u D m}
    (run : Exec Empty.elim code (mk (stateLiftDown positive (embDn bank v)) (embStk bank S)) m (mk u D)) :
    ∃ z F, Exec body (statePlacedNormalized bank capacity positive Empty.elim code) (mk v S) (1+m) (mk z F) ∧
      z.user = u.user ∧ embStk bank F = D ∧ ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨z,_,same,placed⟩ := statePlaced_exec_normalized bank bank.injective capacity positive
    Empty.elim (body' := body) (fun e => nomatch e) v S run
  exact ⟨z,_,placed,same,embStk_ovr bank.injective _ _,fun _ apart => embOvr_off _ _ apart⟩

variable [M8.Machine.Net]
local notation "T" => (rowSwapBlock.tapes+35)+142081
local notation "Q" => rowSwapBlock.states
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Install a packing program on an enclosing bank and return its owner
words in the representation consumed by the invocation. Every tape outside
the packing workspace and its owners retains its exact stacks. -/
theorem scheduledSlotPack_placed {P U : Type} {t q : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5)
    (pre : List (Fin 32 × Fin 5)) (bank : Fin T ↪ Fin t) (capacity : Q ≤ q)
    (body : P → Pr P t q prime U) :
    let owners := (Fin.natAddEmb (rowSwapBlock.tapes+35) (m := 142081)).trans bank
    let before := pre.foldl (fun c r => helperChartsAfter n r c) (fun _ => none)
    ∃ code C, ∀ w W : ℕ, 0 < W →
      let V := (prime^(w+1))^128*W
      ∀ (v : HS t q prime U) (S : Stacks t prime) (data : Fin 142081 → Fin V → ZMod 2),
      embStk bank S = helperPackInput w W (embStk owners S) →
      RepT (phaseOwners data) (embStk owners S).L (embStk owners S).R →
      ∃ z F, ∃ time : ℕ, ∃ result : Fin 142081 → Fin V → ZMod 2,
        Exec body code (mk v S) time (mk z F) ∧ z.user = v.user ∧
        (time : ℝ) ≤ 1+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ∧
        RepT (phaseOwners result) (embStk owners F).L (embStk owners F).R ∧
        (∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        (∀ j, (∀ h : Fin 439, (helperSlotChange n p before h).1 ≠ j) → result j = data j) ∧
        ∀ h : Fin 439, let change := helperSlotChange n p before h
          ∀ c s j, result change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.2 (w+1) s) j) =
            data change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.1 (w+1) s) j) := by
  intro owners before
  obtain ⟨code,C,pack⟩ := scheduledSlotPack_exec (P := Empty) (U := U) n p pre Empty.elim
  refine ⟨statePlacedNormalized bank capacity swapStates_pos Empty.elim code,C,?_⟩
  intro w W live V v S data initial represented
  obtain ⟨u,D,m,result,user,cost,exec,reads,idle,slots⟩ := pack w W live
    (stateLiftDown swapStates_pos (embDn bank v)) (embStk owners S) data ((phaseOwner_reads ..).1 represented)
  rw [← initial] at exec
  obtain ⟨z,F,run,same,view,off⟩ := placeClosedRun bank capacity swapStates_pos body code v S exec
  refine ⟨z,F,1+m,result,run,same.trans user,?_,(phaseOwner_reads ..).2 ?_,off,idle,slots⟩
  · simpa only [Nat.cast_add,Nat.cast_one] using add_le_add (le_refl (1:ℝ)) cost
  · intro j a
    have atOwner := reads j a
    rw [← view] at atOwner
    simpa only [owners,embStk,Function.comp_apply,Function.Embedding.trans_apply,Fin.natAddEmb_apply] using atOwner

omit [M8.Machine.Net] in
private theorem encoded_word {k V : ℕ} (data : Fin k → Fin V → ZMod 2) (i : Fin k) :
    SparseRoleCircuit.encoded (a := prime) data i = fun j => SparseRoleCircuit.encode (data i j) := rfl

omit [M8.Machine.Net] in
/-- Replace the represented owner words of an invocation bank while carrying
its two loop controls from the input configuration. -/
private theorem packedFan {k t V : ℕ} (fan : Fin (k+2) ↪ Fin t)
    (a b : Fin k → Fin V → ZMod 2) (S F : Stacks t prime)
    (start : RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
      (SparseRoleCircuit.encoded a) (FlatCoordinateSchedule.bits V)) (embStk fan S).L (embStk fan S).R)
    (words : RepT (phaseOwners b) (embStk ((Fin.castAddEmb 2).trans fan) F).L
      (embStk ((Fin.castAddEmb 2).trans fan) F).R)
    (controls : ∀ i : Fin 2, F.L (fan (i.natAdd k)) = S.L (fan (i.natAdd k)) ∧
      F.R (fan (i.natAdd k)) = S.R (fan (i.natAdd k))) :
    RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
      (SparseRoleCircuit.encoded b) (FlatCoordinateSchedule.bits V)) (embStk fan F).L (embStk fan F).R := by
  intro i
  refine Fin.addCases (fun j z => ?_) (fun j z => ?_) i
  · simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,phaseOwners,
      encoded_word,embStk,Function.comp_apply,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using words j z
  · have cell := start (j.natAdd k) z
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,
      (controls j).1,(controls j).2] using cell

/-- Packing adds its local work before a hosted invocation. The call keeps
its supplied time allowance, including the price of each recursive child. -/
theorem packThenInvoke {P U : Type} {t q : ℕ} (n : Fin 9) (p : Fin 32 × Fin 5)
    (pre : List (Fin 32 × Fin 5)) (bank : Fin T ↪ Fin t) (capacity : Q ≤ q)
    (body : P → Pr P t q prime U) (fan : Fin (142081+2) ↪ Fin t)
    (shared : (Fin.castAddEmb 2).trans fan = (Fin.natAddEmb (rowSwapBlock.tapes+35)).trans bank)
    (separate : ∀ i : Fin 2, ∀ j, bank j ≠ fan (i.natAdd 142081)) :
    let owners := (Fin.castAddEmb 2).trans fan
    let before := pre.foldl (fun c r => helperChartsAfter n r c) (fun _ => none)
    ∃ pack C, ∀ w W : ℕ, 0 < W →
      let V := (prime^(w+1))^128*W
      let represented := fun (a : Fin 142081 → Fin V → ZMod 2) (S : Stacks t prime) =>
        RepT (PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
          (SparseRoleCircuit.encoded a) (FlatCoordinateSchedule.bits V)) (embStk fan S).L (embStk fan S).R
      ∀ v S data (call : Pr P t q prime U) (price : ℕ)
        (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop),
      embStk bank S = helperPackInput w W (embStk owners S) → represented data S →
      (∀ a u D, represented a D → (∀ j, (∀ i, bank i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        ∃ z F m b, Exec body call (mk u D) m (mk z F) ∧ m ≤ price ∧ z.user = u.user ∧ represented b F ∧ effect a b) →
      ∃ z F, ∃ time : ℕ, ∃ a b, Exec body (.seq pack call) (mk v S) time (mk z F) ∧
        (time : ℝ) ≤ 1+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau + price ∧ z.user = v.user ∧
        represented b F ∧ effect a b ∧
        (∀ j, (∀ h : Fin 439, (helperSlotChange n p before h).1 ≠ j) → a j = data j) ∧
        ∀ h : Fin 439, let change := helperSlotChange n p before h
          ∀ c s j, a change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.2 (w+1) s) j) =
            data change.1 (FlatCoordinateLayout.index (helperSlotField c change.2.1 (w+1) s) j) := by
  intro owners before
  obtain ⟨pack,C,execute⟩ := scheduledSlotPack_placed n p pre bank capacity body
  refine ⟨pack,C,?_⟩
  intro w W live V represented v S data call price effect initial start invoke
  have words : RepT (phaseOwners data) (embStk owners S).L (embStk owners S).R := by
    intro j z
    simpa only [owners,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,phaseOwners,
      encoded_word,embStk,Function.comp_apply,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using start (j.castAdd 2) z
  rw [show owners = _ from shared] at initial words
  obtain ⟨u,D,m,a,first,user,cost,ready,off,idle,slots⟩ := execute w W live v S data initial words
  rw [← shared] at ready
  obtain ⟨z,F,k,b,second,paid,keep,done,act⟩ := invoke a u D
    (packedFan fan data a S D start ready (fun i => off _ (separate i))) off
  refine ⟨z,F,m+k,a,b,Exec.seq first second,?_,keep.trans user,done,act,idle,slots⟩
  exact_mod_cast add_le_add cost ((Nat.cast_le (α := ℝ)).mpr paid)

end IntegerMultBounds.MathlibTM2.M6.BitNode
