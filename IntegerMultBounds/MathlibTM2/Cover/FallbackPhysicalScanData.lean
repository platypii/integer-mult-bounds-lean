module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanState

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

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host in
/-- Execute a single live projector residual from the pivot codes of its residue
class. Only this record is consumed, so skipped labels need no pivot codes. -/
theorem physicalResidualRecord_exec [M8.Machine.Net] {P U : Type}
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
    let sign : (ZMod M)ˣ := if negativeAnchor rows C then -1 else 1
    let bank := fun n => columnBank.trans (archivePorts n)
    ∀ (body : P → Pr P (N+2) columnCapacity prime U) (u : HS (N+2) columnCapacity prime U)
      (S : Stacks (N+2) prime) (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
      (word : Fin (M^(d+1)*W) → ZMod 2),
      (∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank) →
      let ready := ColumnReady (bank 0) H J G tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q word
      let clean := fun (D : Stacks (N+2) prime) => ∀ i : Fin N, 35 ≤ i.val →
        D.L (columnPorts i).castSucc = [] ∧ D.R (columnPorts i).castSucc = []
      ready (fun x k => ((Fin.cons sign (fun _ => 1) : Fin (d+1) → (ZMod M)ˣ) k : ZMod M)*x k) S →
      clean S → S.R (Fin.last N).castSucc = scheduleCode rows ++
        (orderedScheduleCode (List.finRange (d+1)).reverse rows ++ rest) →
      ∃ z D n, z.user = u.user ∧ n ≤ signedResidualTime U rows w W H J ∧
        Exec body (signedResidual d) (mk u S) n (mk z D) ∧ ready (fun x => G.mulVec x) D ∧
        clean D ∧ D.R (Fin.last N).castSucc = rest ∧ D.R (bank 1 34) = S.R (bank 1 34) := by
  intro N G φ C rows sign bank body u S tail rest dest q word empty ready clean before free code
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
  have signed : (Itinerary.run rows G (d+1)).det = (sign : ZMod M) := by
    cases h : negativeAnchor rows C <;> simpa [sign,h] using anchor
  exact signedResidual_exec rows G valid sign signed H J hm hw positive body u S tail rest dest q empty word before free code

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
