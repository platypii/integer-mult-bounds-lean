module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackAnchorPass
public import IntegerMultBounds.Machine.SparseRoleCircuit

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
