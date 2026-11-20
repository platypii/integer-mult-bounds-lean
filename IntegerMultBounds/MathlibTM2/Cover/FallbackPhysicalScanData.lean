module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanState
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordMasks

/-! Identify the generated live and padding words with the signed pass's matrix archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open IntegerMultBounds.Swap.Modular (reduce Admissible)
variable {r d w W : ℕ}
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

def ScanData.physical (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (P : Matrix (Fin r) (Fin r) ℚ) (α α' : Fin r → ZMod M) : ScanData r d w W :=
  let φ := LabelRing.res prime (w+1) (by omega)
  {a with
    matrix := fun j => if LabelStock.live r (w+1) 1 j then
      projectorResidual e (reduce M P) α α' (physicalLabel r (w+1) j) else 1
    table := projectorResidual e (reduce prime P) (φ ∘ α) (φ ∘ α')
    matrixTail := []}

theorem ScanData.physical_archive (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (P : Matrix (Fin r) (Fin r) ℚ) (α α' : Fin r → ZMod M) :
    (a.physical e P α α').matrices 0 = (List.range a.records).flatMap fun j =>
      if LabelStock.live r (w+1) 1 j then matrixWords prime a.H
        (projectorResidual e (reduce M P) α α' (physicalLabel r (w+1) j))
      else matrixWords prime a.H (1 : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M)) := by
  simp only [ScanData.matrices,ScanData.physical,List.drop_zero,List.append_nil]
  congr 1
  funext j
  split <;> rfl

theorem ScanData.physical_live (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (P : Matrix (Fin r) (Fin r) ℚ) (hp : P*P = P) (adm : Admissible prime P)
    (α α' : Fin r → ZMod M) (ha : ∀ i, α i * α' i = 1) (j : ℕ)
    (live : LabelStock.live r (w+1) 1 j = true) :
    let data := a.physical e P α α'
    ((data.matrix j).det = 1 ∨ (data.matrix j).det = -1) ∧
      (LabelRing.res prime (w+1) (by omega)).mapMatrix (data.matrix j) =
        data.table (LabelStock.residue r (w+1) 1 j) := by
  simpa only [ScanData.physical,live,ite_true] using
    physicalProjector_spec (by omega : 0 < w+1) j live e P hp adm α α' ha

local instance (b : ℕ) : NeZero (IntegerMultBounds.Machine.ActualAffineScaling.modulus b) :=
  ⟨(IntegerMultBounds.Machine.ActualAffineScaling.modulus_pos b).ne'⟩

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Record in
/-- Read the sign from an exceptional schedule, apply the anchor, and return
the signed payload to the front of the input queue in forward order. -/
theorem scheduledAnchor_exec {T : ℕ} {P U : Type} (ports : Fin 6 ↪ Fin T)
    (C : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime)) (positive : 0 < W)
    (a : Record.Array d 1 (w+1) W) (word : Fin (M^(d+1)*W) → ZMod 2)
    (encoded : scalarArray a = SparseRoleCircuit.encode ∘ word)
    (body : P → Pr P _ _ prime U) (u : HS _ _ prime U) (S : Stacks (size d+T) prime)
    (tail rest : List (Fin (prime+4))) (ready : Record.Ready d 1 (w+1) W S)
    (count : (S.R (port d ports 0)).length = M^(d+1)*W)
    (input : S.R (port d ports 1) = payloadWord a ++ tail)
    (free : ∀ i ∈ ([2,3,5] : List (Fin 6)), S.R (port d ports i) = [])
    (schedule : S.R (port d ports 4) = residualSchedule C ++ rest) :
    let rows := classPivots C
    let neg := negativeAnchor rows C
    ∃ a' : Record.Array d 1 (w+1) W, ∃ next z D n, z.user = u.user ∧
      n ≤ cost d T 1 (w+1) W neg + (2*(M^(d+1)*W)+2) ∧
      Exec body ((program d ports).seq (moveR (port d ports 5) (port d ports 1) id))
        (mk u S) n (mk z D) ∧
      D.R (port d ports 1) = payloadWord (SparseRoleCircuit.encode ∘ next) ++ tail ∧
      D.R (port d ports 4) = scheduleCode rows ++ (orderedScheduleCode (List.finRange (d+1)).reverse rows ++ rest) ∧
      D.R (port d ports 5) = [] ∧ Record.Ready d 1 (w+1) W D ∧
      (∀ i : Fin T, i ≠ ports 1 → i ≠ ports 4 → i ≠ ports 5 →
        D.R (Fin.natAdd (size d) i) = S.R (Fin.natAdd (size d) i)) ∧ scalarArray a' = SparseRoleCircuit.encode ∘ next ∧
      ∀ x k, next (FlatCoordinateLayout.index (signedAddress neg x) k) = word (FlatCoordinateLayout.index x k) := by
  intro rows neg
  let pivots := scheduleCode (A := prime) rows ++ (orderedScheduleCode (List.finRange (d+1)).reverse rows ++ rest)
  have sign : S.R (port d ports 4) = bitSymbol neg :: pivots := by
    simpa only [residualSchedule,List.cons_append,List.append_assoc,neg,rows,pivots] using schedule
  obtain ⟨out,y,F,t,run,neutral,user,_,_,_,price,frame,action⟩ := Record.runs ports neg (by decide : 0 < 1)
    (by omega : 0 < w+1) positive a body u S tail pivots ready (by simpa [ActualAffineScaling.modulus] using count)
    input (free 2 (by simp)) (free 3 (by simp)) sign
  have atPort (i : Fin 6) := frame (ports i)
  have acc : F.R (port d ports 5) = (payloadWord out).reverse := by
    simpa [port,free 5 (by simp)] using atPort 5
  have src : F.R (port d ports 1) = tail := by simpa [port,ports.injective.eq_iff] using atPort 1
  have steps : (F.R (port d ports 5)).length = M^(d+1)*W := by simp [acc,payloadWord,ActualAffineScaling.modulus]
  have distinct (i j : Fin 6) (h : i ≠ j) : port d ports i ≠ port d ports j :=
    (Fin.natAdd_injective _ _).ne (ports.injective.ne h)
  obtain ⟨z,hz,rewind⟩ := moveR_exec body (port d ports 5) (port d ports 1) (distinct 5 1 (by decide)) id y F
  rw [steps] at rewind
  obtain ⟨next,output,perm⟩ := signedPayload neg a out action word encoded
  refine ⟨out,next,z,_,_,hz.trans user,Nat.add_le_add_right price _,Exec.seq run rewind,?_,?_,?_,?_,?_,output,perm⟩
  · rw [← output,Record.payloadWord_scalarArray]
    simp [movedR,acc,src]
  · simpa [movedR,distinct 4 1 (by decide),distinct 4 5 (by decide),port,ports.injective.eq_iff] using atPort 4
  · simp [movedR,distinct 5 1 (by decide)]
  · intro i j
    have off (k : Fin 6) : Fin.castAdd T i ≠ port d ports k := by
      intro eq; have h := congrArg Fin.val eq
      change i.val = size d + (ports k).val at h
      exact (Nat.not_le_of_lt i.isLt) (h ▸ Nat.le_add_right _ _)
    simpa only [movedR,Function.update_of_ne (off 1),Function.update_of_ne (off 5)] using neutral i j
  · intro i src sign acc
    simpa [movedR,port,src,sign,acc] using frame i

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host in
/-- Execute a single live projector residual from the pivot codes of its residue
class. Only this record is consumed, so skipped labels need no pivot codes. -/
theorem physicalResidualRecord_exec [M8.Machine.Net] {T : ℕ} {P U : Type}
    (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) (proj : Matrix (Fin r) (Fin r) ℚ)
    (idem : proj*proj = proj) (adm : Admissible prime proj)
    (α inv : Fin r → ZMod M) (reciprocal : ∀ i, α i * inv i = 1)
    (j : ℕ) (live : LabelStock.live r (w+1) 1 j = true)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (positive : 0 < W) :
    let N := rowSwapBlock.tapes+35
    let G := projectorResidual e (reduce M proj) α inv (physicalLabel r (w+1) j)
    let φ := LabelRing.res prime (w+1) (by omega)
    let C := projectorResidual e (reduce prime proj) (φ ∘ α) (φ ∘ inv) (LabelStock.residue r (w+1) 1 j)
    let rows := classPivots C
    ∀ (ports : Fin (N+2) ↪ Fin T) (count src saved tmp : Fin T),
      (∀ j, ports j ≠ src) → [count,src,ports (archivePorts 0 (columnBank 24)),saved,tmp].Nodup →
      ∀ (body : P → Pr P T columnCapacity prime U) (u : HS T columnCapacity prime U) (S : Stacks T prime)
        (tail rest queueTail : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (original word : Fin (M^(d+1)*W) → ZMod 2),
      (∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank) →
      let bank := columnBank.trans (archivePorts 0)
      let dst := ports (bank 24)
      let clean := fun (D : Stacks T prime) => ∀ i : Fin N, 35 ≤ i.val →
        D.L (ports (columnPorts i).castSucc) = [] ∧ D.R (ports (columnPorts i).castSucc) = []
      ShearReady bank H J G tail (fun _ : ZMod 2 => blank) (fun _ => blank) dest 0 q original (embStk ports S) →
      clean S → (∀ x j, word (FlatCoordinateLayout.index (Record.signedAddress (negativeAnchor rows C) x) j) = original (FlatCoordinateLayout.index x j)) →
      S.R src = payloadWord (SparseRoleCircuit.encode ∘ word) ++ queueTail → (S.R count).length = M^(d+1)*W →
      (∀ z, readAt blank (S.L dst) (S.R dst) z = blank) → S.R saved = [] → S.R tmp = [] →
      S.R (ports (Fin.last N).castSucc) = scheduleCode rows ++ orderedScheduleCode (List.finRange (d+1)).reverse rows ++ rest →
      ∃ z F n, z.user = u.user ∧ n ≤ 6*(M^(d+1)*W)+6+(1+signedResidualTime U rows w W H J) ∧
        Exec body (queuedResidual ports count src saved tmp d) (mk u S) n (mk z F) ∧
        ColumnReady bank H J G tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original (fun x => G.mulVec x) (embStk ports F) ∧
        clean F ∧ F.R (ports (Fin.last N).castSucc) = rest ∧ F.R src = queueTail ∧
        F.R (ports (archivePorts 1 (columnBank 34))) = S.R (ports (archivePorts 1 (columnBank 34))) ∧
        F.L src = S.L src ∧
        ∀ j, j ≠ src → (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro N G φ C rows ports count src saved tmp outside separate body u S tail rest queueTail dest q
    original word empty bank dst clean layout free placed queue width blankDst savedFree tmpFree code
  let : Fact prime.Prime := ⟨prime_prime⟩
  obtain ⟨det,lift⟩ := physicalProjector_spec (by omega : 0 < w+1) j live e proj idem adm α inv reciprocal
  change G.det = 1 ∨ G.det = -1 at det
  change φ.mapMatrix G = C at lift
  have unit : IsUnit C.det := by
    rw [← lift,← RingHom.map_det]
    rcases det with h | h <;> simp [h]
  have reduced : Itinerary.Valid rows (φ.mapMatrix G) (d+1) := lift.symm ▸ classPivots_valid C unit
  have valid := (Itinerary.valid_map_iff φ (fun a ha =>
    (LabelRing.isUnit_iff_res prime (w+1) (by omega) a).mpr ha.ne_zero) rows G (d+1)).mpr reduced
  have anchor := anchor_of_itinerary IntegerMultBounds.Networks.Shared50ModularControl.prime_odd
    (by omega : 0 < w+1) rows G valid det
  rw [show (LabelRing.res prime (w+1) (by omega)).mapMatrix G = C from lift] at anchor
  let sign : (ZMod M)ˣ := if negativeAnchor rows C then -1 else 1
  have signed : (Itinerary.run rows G (d+1)).det = (sign : ZMod M) := by
    cases h : negativeAnchor rows C <;> simpa [sign,h] using anchor
  exact queuedResidual_exec ports outside separate rows G valid sign signed H J hm hw positive body u S
    tail rest queueTail dest q empty original word layout free placed queue width blankDst savedFree tmpFree code

open IntegerMultBounds.Machine.FlatCoordinateLayout in
/-- The live output bit of the physical identity scan occurs at the enclosing
weighted child's address, for every trailing position. -/
theorem ScanData.physicalIdentity_bit (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (α inv : Fin r → ZMod M) (inverse : ∀ i, α i * inv i = 1) (j : ℕ)
    (live : LabelStock.live r (w+1) 1 j = true) (x : Fin (d+1) → ZMod M) (k : Fin W) :
    let data := a.physical e 1 α inv
    let result := Weighted.child r α inv (x ∘ e ∘ Sum.inl, x ∘ e ∘ Sum.inr)
    imageWord (data.matrix j) (a.input j) (index (Sum.elim result.1 result.2 ∘ e.symm) k) =
      a.input j (index x k) := by
  intro data result
  have signs := (a.physical_live e 1 (by simp) (IntegerMultBounds.Swap.Modular.admissible_one prime)
    α inv inverse j live).1
  have unit : IsUnit (data.matrix j).det := by rcases signs with h | h <;> rw [h] <;> simp
  have addr : (data.matrix j).mulVec x = Sum.elim result.1 result.2 ∘ e.symm := by
    simpa only [data,ScanData.physical,live,ite_true,result] using
      physicalIdentity_address (by omega : 0 < w+1) e j live α inv x
  rw [← addr]
  simp [imageWord,index,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ unit]

open IntegerMultBounds.Machine IntegerMultBounds.Machine.FlatCoordinateLayout in
/-- At a live record the scan writes the bit at its weighted image. A padding
record writes the same bit at its original address. -/
theorem ScanData.physicalIdentity_record (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (α inv : Fin r → ZMod M) (inverse : ∀ i, α i * inv i = 1) (j : ℕ)
    (x : Fin (d+1) → ZMod M) (k : Fin W) :
    let active := LabelStock.live r (w+1) 1
    let data := a.physical e 1 α inv
    let result := Weighted.child r α inv (x ∘ e ∘ Sum.inl, x ∘ e ∘ Sum.inr)
    let address := if active j then Sum.elim result.1 result.2 ∘ e.symm else x
    (outputRecord active data.matrix a.input j)[(index address k).val]? =
      some (RadixToBinary.binaryEncoding.encode (SparseRoleCircuit.encode (a.input j (index x k)))) := by
  intro active data result address
  have cell {N : ℕ} (word : Fin N → Fin 4) (i : Fin N) :
      (payloadWord word)[i.val]? = some (RadixToBinary.binaryEncoding.encode (word i)) := by
    rw [List.getElem?_eq_getElem (by simpa [payloadWord] using i.isLt)]
    simp [payloadWord]
  unfold outputRecord
  rw [cell]
  cases h : active j with
  | false => simp only [address,h,Bool.false_eq_true,ite_false,Function.comp_apply]
  | true =>
    simp only [address,h,ite_true,Function.comp_apply]
    rw [a.physicalIdentity_bit e α inv inverse j h x k]

private theorem recordQueue_lookup {α : Type*} {width : ℕ} (record : ℕ → List α)
    (length : ∀ j, (record j).length = width) (count j : ℕ) (hj : j < count) (k : Fin width)
    (tail : List α) :
    (((List.range count).flatMap record) ++ tail)[j*width+k.val]? = (record j)[k.val]? := by
  have size (n : ℕ) : ((List.range n).flatMap record).length = n*width := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ,ih,length,Nat.succ_mul]
  induction count generalizing tail with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,List.append_assoc]
    by_cases eq : j = n
    · subst j
      rw [List.getElem?_append_right (by rw [size]; omega),size,Nat.add_sub_cancel_left,
        List.getElem?_append_left (by rw [length]; exact k.isLt)]
    · exact ih (by omega) _

open IntegerMultBounds.Machine IntegerMultBounds.Machine.FlatCoordinateLayout in
theorem ScanData.physicalIdentity_queue (a : ScanData r d w W) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (α inv : Fin r → ZMod M) (inverse : ∀ i, α i * inv i = 1) (j : Fin a.records)
    (x : Fin (d+1) → ZMod M) (k : Fin W) :
    let active := LabelStock.live r (w+1) 1
    let data := a.physical e 1 α inv
    let queue := (List.range a.records).flatMap (outputRecord active data.matrix a.input) ++ a.inputTail
    let result := Weighted.child r α inv (x ∘ e ∘ Sum.inl, x ∘ e ∘ Sum.inr)
    let address := if active j then Sum.elim result.1 result.2 ∘ e.symm else x
    queue[j.val*(M^(d+1)*W)+(index address k).val]? =
      some (RadixToBinary.binaryEncoding.encode (SparseRoleCircuit.encode (a.input j (index x k)))) := by
  intro active data queue result address
  exact (recordQueue_lookup (outputRecord active data.matrix a.input)
    (fun _ => by simp [outputRecord,payloadWord]) _ j j.isLt (index address k) a.inputTail).trans
    (a.physicalIdentity_record e α inv inverse j x k)


end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
