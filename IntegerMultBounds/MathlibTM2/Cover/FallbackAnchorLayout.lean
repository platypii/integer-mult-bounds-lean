module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearReady
public import IntegerMultBounds.MathlibTM2.Cover.FallbackAnchorPass
public import IntegerMultBounds.Machine.SparseRoleCircuit
import IntegerMultBounds.MathlibTM2.Host.ChunkSwap

/-! Interpret a signed single-atom record in the residual machine's coordinate layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine M8 ActualAffineScaling FlatCoordinateLayout
variable {d b W : ℕ}
local notation "M" => modulus b
local instance : NeZero M := ⟨(modulus_pos b).ne'⟩

noncomputable def scalarArray (a : Array d 1 b W) (n : Fin (M^(d+1)*W)) : Fin 4 :=
  a (n.cast (by simp))

private theorem index_cast {m n Q : ℕ} [NeZero Q] (h : m = n) (x : Fin n → ZMod Q) (j : Fin W) :
    index (fun i : Fin m => x (i.cast h)) j = (index x j).cast (by rw [h]) := by subst n; rfl

private theorem refine_scalar (x : Fin (d+1) → ZMod M) (j : Fin W) :
    index (AtomOps.refine (fun i (_ : Fin 1) => x i)) j = (index x j).cast (by simp) := by
  rw [← index_cast (Nat.mul_one (d+1)) x j]
  congr 1
  funext i
  apply congrArg x
  apply Fin.ext
  simp [finProdFinEquiv]

noncomputable def signedAddress (negative : Bool) (x : Fin (d+1) → ZMod M) (j : Fin (d+1)) : ZMod M :=
  ((Fin.cons (if negative then -1 else 1) (fun _ => 1) : Fin (d+1) → (ZMod M)ˣ) j : ZMod M) * x j

theorem signedAddress_involutive (negative : Bool) (x : Fin (d+1) → ZMod M) :
    signedAddress negative (signedAddress negative x) = x := by
  funext i
  cases i using Fin.cases with
  | zero => cases negative <;> simp [signedAddress]
  | succ i => simp [signedAddress]

theorem correct_scalar (negative : Bool) (a out : Array d 1 b W) (h : Correct (negative,a) out)
    (x : Fin (d+1) → ZMod M) (j : Fin W) :
    scalarArray out (index (signedAddress negative x) j) = scalarArray a (index x j) := by
  have eq : (Fin.cons (fun _ : Fin 1 => if negative then -x 0 else x 0) (fun i _ => x i.succ)) =
      fun i (_ : Fin 1) => signedAddress negative x i := by
    funext i k
    cases i using Fin.cases with
    | zero => cases negative <;> simp [signedAddress]
    | succ i => simp [signedAddress]
  have result := h (fun i _ => x i) j
  change out (index (AtomOps.refine (Fin.cons (fun _ : Fin 1 => if negative then -x 0 else x 0) _)) j) = _ at result
  rw [eq,refine_scalar,refine_scalar] at result
  exact result

/-- The bit word represented by the anchor's output tape, including every trailing payload position. -/
theorem signedPayload (negative : Bool) (a out : Array d 1 b W) (h : Correct (negative,a) out)
    (original : Fin (M^(d+1)*W) → ZMod 2) (input : scalarArray a = SparseRoleCircuit.encode ∘ original) :
    ∃ word : Fin (M^(d+1)*W) → ZMod 2, scalarArray out = SparseRoleCircuit.encode ∘ word ∧
      ∀ x j, word (index (signedAddress negative x) j) = original (index x j) := by
  let word := fun n : Fin (M^(d+1)*W) =>
    let part := finProdFinEquiv.symm n
    original (index (signedAddress negative (coordinates part.1)) part.2)
  have eval (x : Fin (d+1) → ZMod M) (j : Fin W) : word (index x j) = original (index (signedAddress negative x) j) := by
    simp only [word,index,Equiv.symm_apply_apply,coordinates_rank]
  refine ⟨word,?_,fun x j => by rw [eval,signedAddress_involutive]⟩
  funext n
  obtain ⟨⟨r,j⟩,rfl⟩ := finProdFinEquiv.surjective n
  rw [show finProdFinEquiv (r,j) = index (coordinates r : Fin (d+1) → ZMod M) j by simp [index]]
  simp only [Function.comp_apply,eval]
  simpa only [signedAddress_involutive,input,Function.comp_apply] using correct_scalar negative a out h (signedAddress negative (coordinates r)) j

/-- A record program reading the signed queue first undoes the anchor on
addresses, then applies its move. Its output is the move on the original input. -/
theorem move_signedPayload (negative : Bool) (move : (Fin (d+1) → ZMod M) → (Fin (d+1) → ZMod M))
    (original signed output : Fin (M^(d+1)*W) → ZMod 2)
    (anchor : ∀ x j, signed (index (signedAddress negative x) j) = original (index x j))
    (run : ∀ x j, output (index (move (signedAddress negative x)) j) = signed (index x j)) :
    ∀ x j, output (index (move x) j) = original (index x j) := by
  intro x j
  simpa only [signedAddress_involutive] using (run (signedAddress negative x) j).trans (anchor x j)

private theorem ofFn_cast {m n : ℕ} (h : m = n) (a : Fin n → α) :
    List.ofFn (fun i : Fin m => a (i.cast h)) = List.ofFn a := by subst n; rfl

theorem payloadWord_scalarArray (a : Array d 1 b W) : payloadWord (scalarArray a) = payloadWord a := by
  unfold payloadWord
  rw [show List.ofFn (scalarArray a) = List.ofFn a from ofFn_cast _ a]

open IntegerMultBounds.MathlibTM2.Stack Host Mult.PhaseCellToeplitz
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

/-- On single-atom fields the placed correction acts directly on the indexed payload.
The incoming address can already include the signed exchange. -/
theorem correctFieldPayload_exec {P U : Type} {T Q : ℕ} (i : Fin (d+1))
    (ports : Fin (22+fieldSignSlots i) ↪ Fin T) (capacity : (fieldSignProgram i true).1 ≤ Q)
    (hb : 0 < b) (hW : 0 < W) (a : Array d 1 b W) (body : P → Pr P T Q prime U)
    (v : HS T Q prime U) (S : Stacks T prime)
    (rep : RepT (AtomBank.outer (fieldSignSlots i) (AtomSegment.neutral b W) (AtomBank.arrTape a) 1)
      (embStk ports S).L (embStk ports S).R)
    (original : Fin (M^(d+1)*W) → ZMod 2) (addr : (Fin (d+1) → ZMod M) → Fin (d+1) → ZMod M)
    (placed : ∀ x j, scalarArray a (index (addr x) j) = SparseRoleCircuit.encode (original (index x j))) :
    ∃ out : Array d 1 b W, ∃ z F t, z.user = v.user ∧
      t ≤ 1 + (AtomSegment.chainConst (fieldSignOps i true) * (M^(d+1)*W) * (22+fieldSignSlots i+5)+6) ∧
      Exec body (placedFieldNeg i ports capacity) (mk v S) t (mk z F) ∧
      RepT (AtomBank.outer (fieldSignSlots i) (AtomSegment.neutral b W) (AtomBank.arrTape out) 1)
        (embStk ports F).L (embStk ports F).R ∧
      (∀ h, (∀ k, ports k ≠ h) → F.L h = S.L h ∧ F.R h = S.R h) ∧
      ∀ x j, scalarArray out (index (Function.update (addr x) i (-addr x i)) j) =
        SparseRoleCircuit.encode (original (index x j)) := by
  obtain ⟨out,z,F,t,hz,ht,run,after,frame,act⟩ := placedFieldNeg_exec i ports capacity
    (by decide : 0 < 1) hb hW a body v S rep
  refine ⟨out,z,F,t,hz,by simpa using ht,run,after,frame,?_⟩
  intro x j
  have h := act (fun k _ => addr x k) j
  have eq : Function.update (fun k (_ : Fin 1) => addr x k) i (fun _ => -addr x i) =
      fun k (_ : Fin 1) => Function.update (addr x) i (-addr x i) k := by
    funext k u
    by_cases e : k = i <;> simp [e]
  rw [eq,refine_scalar,refine_scalar] at h
  exact h.trans (placed x j)

/-- The sign bank has two size descriptors and three loop controls. -/
def fieldHeader {slots : ℕ} (b W : ℕ) (k : Fin (22+slots)) : Option (List Bool) :=
  if h : k.val < 17 then AtomSegment.neutral b W ⟨k.val,h⟩ else
    if k.val = 18 then some [] else if k.val = 19 then some (FlatCoordinateSchedule.bits 0) else
    if k.val = 20 then some (FlatCoordinateSchedule.bits 1) else none

theorem fieldHeader_rep {T slots : ℕ} (ports : Fin (22+slots) ↪ Fin T) (S : Stacks T prime)
    (headers : ∀ k, k.val ≠ 17 →
      S.L (ports k) = (fieldHeader b W k).toList.map (fun _ => separator) ∧
      S.R (ports k) = ((fieldHeader b W k).getD []).map bitSymbol) :
    let base := AtomBank.outer slots (AtomSegment.neutral b W) (fun _ => blank) 1
    ∀ k, k.val ≠ 17 → ∀ z, base.tape k z = readAt blank (S.L (ports k)) (S.R (ports k)) (z-base.head k) := by
  intro base k hk z
  obtain ⟨left,right⟩ := headers k hk
  rw [left,right]
  have repr (o : Option (List Bool)) : CounterDimensions.descriptorTape prime o z =
      readAt blank (o.toList.map (fun _ => separator)) ((o.getD []).map bitSymbol)
        (z-CounterDimensions.descriptorHead o) := by
    cases o with
    | none => simp [CounterDimensions.descriptorTape,CounterDimensions.descriptorHead,readAt_nil_left,wordTape_nil]
    | some xs => change RadixZeroFill.encodedBinary xs z = readAt blank [separator] _ (z-1)
                 rw [encodedBinary_eq,readAt_single]; rfl
  by_cases h : k.val < 17
  · simpa [base,AtomBank.outer,fieldHeader,h] using repr (AtomSegment.neutral b W ⟨k.val,h⟩)
  by_cases h18 : k.val = 18
  · simpa [base,AtomBank.outer,fieldHeader,h,hk,h18,CounterDimensions.descriptorTape,
      CounterDimensions.descriptorHead,← CounterAdvance.binary_encoded,CountedLoopReuseAlphabet.binary,CountedLoopAlphabet.putBits] using repr (some [])
  by_cases h19 : k.val = 19
  · simpa [base,AtomBank.outer,fieldHeader,h,hk,h18,h19,CounterDimensions.descriptorTape,
      CounterDimensions.descriptorHead,← CounterAdvance.binary_encoded] using repr (some (FlatCoordinateSchedule.bits 0))
  by_cases h20 : k.val = 20
  · simpa [base,AtomBank.outer,fieldHeader,h,hk,h18,h19,h20,CounterDimensions.descriptorTape,
      CounterDimensions.descriptorHead,← CounterAdvance.binary_encoded] using repr (some (FlatCoordinateSchedule.bits 1))
  · have outside : ¬ (18 ≤ k.val ∧ k.val ≤ 20) := by omega
    simpa [base,AtomBank.outer,fieldHeader,h,hk,h18,h19,h20,outside,CounterDimensions.descriptorTape,
      CounterDimensions.descriptorHead] using repr none

/-- A column payload can serve directly as the sign machine's array tape. -/
theorem column_field_input {T w : ℕ} (bank : Fin 35 ↪ Fin T) (i : Fin (d+1))
    (ports : Fin (22+fieldSignSlots i) ↪ Fin T) (payload : ports 17 = bank 24)
    (H J : ℕ) (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (original : Fin ((prime^(w+1))^(d+1)*W) → ZMod 2)
    (addr : (Fin (d+1) → ZMod (prime^(w+1))) → Fin (d+1) → ZMod (prime^(w+1))) (S : Stacks T prime)
    (ready : ColumnRecordReady bank H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original addr S)
    (frame : let base := AtomBank.outer (fieldSignSlots i) (AtomSegment.neutral (w+1) W) (fun _ => blank) 1
      ∀ k, k.val ≠ 17 → ∀ z, base.tape k z = readAt blank (S.L (ports k)) (S.R (ports k)) (z-base.head k)) :
    ∃ a : Array d 1 (w+1) W,
      RepT (AtomBank.outer (fieldSignSlots i) (AtomSegment.neutral (w+1) W) (AtomBank.arrTape a) 1)
        (embStk ports S).L (embStk ports S).R ∧
      ∀ x j, scalarArray a (index (addr x) j) = SparseRoleCircuit.encode (original (index x j)) := by
  obtain ⟨word,layout,action⟩ := ready
  let a : Array d 1 (w+1) W := fun h => SparseRoleCircuit.encode (word (h.cast (by simp [modulus])))
  have words : List.ofFn a = List.ofFn (SparseRoleCircuit.encode ∘ word) :=
    ofFn_cast (by simp [modulus]) (SparseRoleCircuit.encode ∘ word)
  refine ⟨a,?_,fun x j => congrArg SparseRoleCircuit.encode (action x j)⟩
  intro k z
  by_cases h : k.val = 17
  · have e : k = 17 := Fin.ext (by simpa [Fin.val_ofNat,Nat.mod_eq_of_lt (show 17 < 22+fieldSignSlots i by omega)] using h)
    subst k
    have tape : AtomBank.arrTape a z = readAt blank (S.L (bank 24)) (S.R (bank 24)) z := by
      unfold AtomBank.arrTape
      rw [words]
      simpa only [sub_zero] using (layout.src z).symm
    simpa [AtomBank.outer,Fin.val_ofNat,Nat.mod_eq_of_lt (show 17 < 22+fieldSignSlots i by omega),
      embStk,payload] using tape
  · simpa [AtomBank.outer,h,embStk] using frame k h z

theorem column_field_neg_exec {P U : Type} {T Q w : ℕ} (bank : Fin 35 ↪ Fin T) (i : Fin (d+1))
    (ports : Fin (22+fieldSignSlots i) ↪ Fin T) (payload : ports 17 = bank 24)
    (H J : ℕ) (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (original : Fin ((prime^(w+1))^(d+1)*W) → ZMod 2)
    (addr : (Fin (d+1) → ZMod (prime^(w+1))) → Fin (d+1) → ZMod (prime^(w+1))) (S : Stacks T prime)
    (capacity : (fieldSignProgram i true).1 ≤ Q) (hW : 0 < W)
    (body : P → Pr P T Q prime U) (v : HS T Q prime U)
    (apart : ∀ h : Fin 35, h ≠ 24 → ∀ k, ports k ≠ bank h)
    (ready : ColumnRecordReady bank H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original addr S)
    (frame : let base := AtomBank.outer (fieldSignSlots i) (AtomSegment.neutral (w+1) W) (fun _ => blank) 1
      ∀ k, k.val ≠ 17 → ∀ z, base.tape k z = readAt blank (S.L (ports k)) (S.R (ports k)) (z-base.head k)) :
    ∃ z F l, z.user = v.user ∧
      l ≤ 1 + (AtomSegment.chainConst (fieldSignOps i true) * ((prime^(w+1))^(d+1)*W) * (22+fieldSignSlots i+5)+6) ∧
      Exec body (placedFieldNeg i ports capacity) (mk v S) l (mk z F) ∧
      ColumnRecordReady bank H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
        (fun x => Function.update (addr x) i (-addr x i)) F ∧
      (let base := AtomBank.outer (fieldSignSlots i) (AtomSegment.neutral (w+1) W) (fun _ => blank) 1
       ∀ k, k.val ≠ 17 → ∀ z, base.tape k z = readAt blank (F.L (ports k)) (F.R (ports k)) (z-base.head k)) ∧
      ∀ h, (∀ k, ports k ≠ h) → F.L h = S.L h ∧ F.R h = S.R h := by
  obtain ⟨word,layout,atAddr⟩ := ready
  obtain ⟨a,rep,input⟩ := column_field_input bank i ports payload H J record dest q word id S
    ⟨word,layout,fun _ _ => rfl⟩ frame
  obtain ⟨out,z,F,l,hz,hl,run,after,off,act⟩ := correctFieldPayload_exec i ports capacity
    (Nat.zero_lt_succ w) hW a body v S rep word id input
  let flip := fun x : Fin (d+1) → ZMod (prime^(w+1)) => Function.update x i (-x i)
  have twice (x) : flip (flip x) = x := by funext k; by_cases e : k = i <;> simp [flip,e]
  let next := fun h : Fin ((prime^(w+1))^(d+1)*W) =>
    let p := finProdFinEquiv.symm h
    word (index (flip (coordinates p.1)) p.2)
  have eval x j : next (index x j) = word (index (flip x) j) := by simp only [next,index,Equiv.symm_apply_apply,coordinates_rank]
  have encoded : scalarArray out = SparseRoleCircuit.encode ∘ next := by
    funext h
    obtain ⟨⟨r,j⟩,rfl⟩ := finProdFinEquiv.surjective h
    rw [show finProdFinEquiv (r,j) = index (coordinates r : Fin (d+1) → ZMod (prime^(w+1))) j by unfold index; rw [@FlatCoordinateLayout.rank_coordinates (d+1) (prime^(w+1)) _ r]; rfl]
    simp only [Function.comp_apply,eval]
    have h := act (flip (coordinates r)) j
    change scalarArray out (index (flip (flip (coordinates r))) j) = _ at h
    rwa [twice] at h
  have words : List.ofFn out = List.ofFn (SparseRoleCircuit.encode ∘ next) := by
    rw [← encoded]; exact (ofFn_cast _ out).symm
  have keep (h : Fin 35) (hh : h ≠ 24) := off _ (apart h hh)
  refine ⟨z,F,l,hz,hl,run,⟨next,?_,?_⟩,?_,off⟩
  · refine ⟨(keep 2 (by decide)).2.trans layout.modulus,(keep 27 (by decide)).2.trans layout.width,
      (keep 28 (by decide)).2.trans layout.one,(keep 32 (by decide)).2.trans layout.padded,
      (congrArg List.length (keep 33 (by decide)).2).trans layout.clock,(keep 34 (by decide)).2.trans layout.archive,
      ?_,?_,?_⟩
    · intro k hk
      have eq := keep k (fun e => (by decide : (24 : Fin 35) ∉ shearWork) (e ▸ hk))
      rw [eq.1,eq.2]; exact layout.scratch k hk
    · intro pos
      have h := after (17 : Fin (22+fieldSignSlots i)) pos
      change AtomBank.arrTape out pos = readAt blank (F.L (ports 17)) (F.R (ports 17)) (pos-0) at h
      simpa only [AtomBank.arrTape,words,payload] using h.symm
    · intro pos; rw [(keep 25 (by decide)).1,(keep 25 (by decide)).2]; exact layout.dst pos
  · intro x j
    exact (eval (flip (addr x)) j).trans (by rw [twice]; exact atAddr x j)
  · intro base k hk pos
    simpa [base,AtomBank.outer,hk,embStk] using after k pos

/-- Load one live signed record, preserving the remaining queue and identifying the
sign and pivots of the corresponding residual matrix. -/
theorem loadAnchorRecord_exec {r w records T Q : ℕ} {P U : Type}
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (g : LabelPadding.Label r (w+1)) (G : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod (prime^(w+1))))
    (det : G.det = 1 ∨ G.det = -1)
    (lift : (LabelRing.res prime (w+1) (by omega)).mapMatrix G = table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    (block : ℕ) (live : block*(prime^(w+1))^(r*r)+(LabelAddress.address g).val < records)
    (inputs : ℕ → Array d 1 (w+1) W) (outs : List (Array d 1 (w+1) W))
    (result : (signedInputs table (w+1) records inputs).Forall₂ Correct outs)
    (body : P → Pr P T Q prime U) {count src dst saved tmp : Fin T} (ports : [count,src,dst,saved,tmp].Nodup)
    (v : HS T Q prime U) (S : Stacks T prime) (tail : List (Fin (prime+4)))
    (original : Fin ((modulus (w+1))^(d+1)*W) → ZMod 2)
    (width : (S.R count).length = (modulus (w+1))^(d+1)*W)
    (empty : ∀ z, readAt blank (S.L dst) (S.R dst) z = blank) (hs : S.R saved = []) (ht : S.R tmp = []) :
    let j := block*(prime^(w+1))^(r*r)+(LabelAddress.address g).val
    let rows := classPivots (table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    let next := (outs.drop (j+1)).flatMap payloadWord ++ tail
    scalarArray (inputs j) = SparseRoleCircuit.encode ∘ original →
    S.R src = (outs.drop j).flatMap payloadWord ++ tail →
    ∃ neg u F word, Itinerary.Valid rows G (d+1) ∧ (Itinerary.run rows G (d+1)).det = (if neg then -1 else 1) ∧
      u.user = v.user ∧ Exec body (movePrefix count src dst saved tmp) (mk v S) (6*((modulus (w+1))^(d+1)*W)+6) (mk u F) ∧
      S.R src = payloadWord (SparseRoleCircuit.encode ∘ word) ++ next ∧
      F = {S with R := Function.update (Function.update S.R src next) dst (payloadWord (SparseRoleCircuit.encode ∘ word) ++ S.R dst)} ∧
      (∀ z, readAt blank (F.L dst) (F.R dst) z = RadixToBinary.binaryEncoding.encode
        (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ word)) z)) ∧
      ∀ x k, word (index (signedAddress neg x) k) = original (index x k) := by
  intro j rows next input queue
  obtain ⟨neg,out,entry,correct,valid,sign⟩ := output_at (by omega) table g G det lift inputs outs result block live
  obtain ⟨inside,eq⟩ := List.getElem?_eq_some_iff.mp entry
  have split : outs.drop j = out :: outs.drop (j+1) := eq ▸ (List.getElem_cons_drop inside).symm
  rw [split,List.flatMap_cons,List.append_assoc] at queue
  obtain ⟨word,encoded,placed⟩ := signedPayload neg (inputs j) out correct original input
  have same : payloadWord out = payloadWord (SparseRoleCircuit.encode ∘ word) := by
    unfold payloadWord
    rw [← encoded,show List.ofFn (scalarArray out) = List.ofFn out from ofFn_cast _ out]
  obtain ⟨u,F,hu,run,stacksEq,tape⟩ := loadPayload_exec body ports out next v S queue (by simpa using width) empty hs ht
  refine ⟨neg,u,F,word,valid,sign,hu,by simpa using run,by rwa [← same],by rwa [← same],?_,placed⟩
  intro z
  rw [← encoded,show List.ofFn (scalarArray out) = List.ofFn out from ofFn_cast _ out]
  exact (tape z).symm

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
