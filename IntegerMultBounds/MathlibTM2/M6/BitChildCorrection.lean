module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildLayout
public import IntegerMultBounds.MathlibTM2.Host.SharedRegisterPlacement
public import IntegerMultBounds.MathlibTM2.Cover.FallbackNextRecord
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPlacedDiagonal
public import IntegerMultBounds.MathlibTM2.Cover.Weighted
public import IntegerMultBounds.MathlibTM2.Cover.FallbackProjectorEntries

/-! Apply the parent-radix weights after an ordinary PR589 child exchange. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Host Stack
open Shared50ModularControl (prime)
open Cover.Fallback

/-- Diagonal correction on the parent's atoms after an ordinary child exchange.
Each active head weight is paired with its inverse on the reversed tail. -/
def childCorrection {m : ℕ} {R : Type*} [CommRing R] (r : ℕ) (weight : Fin m → Rˣ) :
    Fin (m+m) → Rˣ :=
  let active := fun i : Fin m => if i.val < r then weight i else 1
  Fin.addCases active (fun j => (active j.rev)⁻¹)

theorem childCorrection_prod {m : ℕ} {R : Type*} [CommRing R] (r : ℕ) (weight : Fin m → Rˣ) :
    ∏ j, childCorrection r weight j = 1 := by
  let active := fun i : Fin m => if i.val < r then weight i else 1
  rw [Fin.prod_univ_add]
  simp only [childCorrection,Fin.addCases_left,Fin.addCases_right]
  change (∏ i, active i) * (∏ j : Fin m, (active j.rev)⁻¹) = 1
  rw [Finset.prod_inv_distrib]
  have reverse := Equiv.prod_comp (Fin.revPerm (n := m)) active
  simpa only [Fin.revPerm_apply] using (show (∏ i, active i) *
    (∏ j, active (Fin.revPerm j))⁻¹ = 1 by rw [reverse]; simp)

/-- Scaling in the parent's radix gives exactly the weighted child action
without reinterpreting a parent weight at the child's finer precision. -/
theorem childCorrection_apply {m : ℕ} {R : Type*} [CommRing R] (r : ℕ) (weight : Fin m → Rˣ)
    (s : IntegerMultBounds.Swap.Shear.State (Fin m) R) :
    let plain := Weighted.child r (fun _ => 1) (fun _ => 1) s
    let corrected := Weighted.child r (fun i => (weight i : R)) (fun i => ((weight i)⁻¹ : Rˣ)) s
    ∀ j : Fin (m+m), ((childCorrection r weight j : Rˣ) : R) *
      Fin.addCases plain.1 plain.2 j = Fin.addCases corrected.1 corrected.2 j := by
  intro plain corrected j
  cases j using Fin.addCases with
  | left i => by_cases h : i.val < r <;> simp [childCorrection,plain,corrected,Weighted.child,h]
  | right i =>
    simp only [childCorrection,Fin.addCases_right,plain,corrected,Weighted.child]
    by_cases h : i.rev.val < r <;> simp only [h,ite_true,ite_false,one_mul,inv_one,Units.val_one]

/-- Write a matrix from four packed vectors (zero, one, forward weights,
inverse weights). Each entry selects its vector and its index at compile time.
The reader uses the live binary word width and restores every source tape. -/
theorem matrixFromArchives_writes {d T Q A M : ℕ} [NeZero M] {P U : Type}
    (body : P → Pr P T Q A U) (read : Fin 4 → Fin 7 ↪ Fin T) (out : Fin T)
    (shared : ∀ k, read k 3 = out) (length : Fin 4 → ℕ)
    (value : (k : Fin 4) → Fin (length k) → ZMod M)
    (source : Fin d → Fin d → Fin 4) (index : ∀ i j, Fin (length (source i j)))
    (H limit : ℕ) (fits : ∀ i j, (index i j).val ≤ limit) :
    let ok := fun R : Node.Regs T A => ∀ k, R (read k 2) =
      (List.ofFn fun j => binSyms H (value k j).val).flatten ∧
      (R (read k 1)).length = H ∧ ∀ t : Fin 7, t = 0 ∨ 4 ≤ t → R (read k t) = []
    let emit := fun i j => readMatrixWord (index i j).val (read (source i j))
    LabelTraversal.Writes body ok out
      (LabelTraversal.sequence (fun i => LabelTraversal.sequence (emit i) (List.finRange d)) (List.finRange d))
      (matrixWords A H (fun i j => value (source i j) (index i j))) (d*(d*(8*(limit*H)+14*H+22)+1)+1) := by
  intro ok emit
  apply matrixWords_writes
  · intro R xs ready k
    rw [← shared k]
    obtain ⟨archive,width,scratch⟩ := ready k
    refine ⟨(Function.update_of_ne ((read k).injective.ne (by decide : (2 : Fin 7) ≠ 3)) ..).trans archive,?_,?_⟩
    · simpa using width
    · intro t ht
      rw [Function.update_of_ne ((read k).injective.ne (by rcases ht with h | h <;> omega : t ≠ 3))]
      exact scratch t ht
  · intro i j u S ready
    let k := source i j
    let row : Matrix (Fin 1) (Fin (length k)) (ZMod M) := fun _ t => value k t
    obtain ⟨archive,width,scratch⟩ := ready k
    obtain ⟨z,user,run⟩ := readMatrixWord_exec body (read k) row 0 (index i j) H u S []
      (by simpa [row,matrixWords,List.ofFn_succ] using archive) width scratch
    refine ⟨z,8*((index i j).val*H)+14*H+22,user,?_,?_⟩
    · exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 8
        (Nat.mul_le_mul_right H (fits i j))) _) _
    · simpa only [emit,Fin.val_zero,Nat.zero_mul,Nat.zero_add,row,shared] using run

/-- The first two archives contain single constants. The other two contain
exactly the active pivots at the caller's precision. -/
def correctionLength (r : ℕ) : Fin 4 → ℕ := ![1,1,r,r]

def correctionSlot (r : ℕ) (i j : Fin (64+64)) : (k : Fin 4) × Fin (correctionLength r k) :=
  if i = j then Fin.addCases
    (fun k : Fin 64 => if h : k.val < r then ⟨2,⟨k.val,h⟩⟩ else ⟨1,(0 : Fin 1)⟩)
    (fun k : Fin 64 => if h : k.rev.val < r then ⟨3,⟨k.rev.val,h⟩⟩ else ⟨1,(0 : Fin 1)⟩) i
  else ⟨0,(0 : Fin 1)⟩

def correctionValue {R : Type*} [CommRing R] {r : ℕ} (fits : r ≤ 64) (weight : Fin 64 → Rˣ) :
    (k : Fin 4) → Fin (correctionLength r k) → R :=
  fun k => match k with
    | 0 => fun _ => 0
    | 1 => fun _ => 1
    | 2 => fun j => (weight (j.castLE fits) : R)
    | 3 => fun j => ((weight (j.castLE fits))⁻¹ : Rˣ)

theorem correctionValue_slot {R : Type*} [CommRing R] {r : ℕ} (fits : r ≤ 64)
    (weight : Fin 64 → Rˣ) (i j : Fin (64+64)) :
    correctionValue fits weight (correctionSlot r i j).1 (correctionSlot r i j).2 =
      Matrix.diagonal (fun k => (childCorrection r weight k : R)) i j := by
  classical
  by_cases equal : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    cases i using Fin.addCases with
    | left k =>
      by_cases h : k.val < r
      · have eq : correctionSlot r (k.castAdd 64) (k.castAdd 64) = ⟨2,⟨k.val,h⟩⟩ := by simp [correctionSlot,h]
        rw [eq]; simp [childCorrection,h,correctionValue]; rfl
      · have eq : correctionSlot r (k.castAdd 64) (k.castAdd 64) = ⟨1,(0 : Fin 1)⟩ := by simp [correctionSlot,h]
        rw [eq]; simp [childCorrection,h,correctionValue]
    | right k =>
      by_cases h : k.rev.val < r
      · have eq : correctionSlot r (Fin.natAdd 64 k) (Fin.natAdd 64 k) = ⟨3,⟨k.rev.val,h⟩⟩ := by
          simp only [correctionSlot,ite_true,Fin.addCases_right,dif_pos h]
        rw [eq]; simp only [childCorrection,Fin.addCases_right,if_pos h]; rfl
      · have eq : correctionSlot r (Fin.natAdd 64 k) (Fin.natAdd 64 k) = ⟨1,(0 : Fin 1)⟩ := by
          simp only [correctionSlot,ite_true,Fin.addCases_right,dif_neg h]
        rw [eq]; simp only [childCorrection,Fin.addCases_right,if_neg h,inv_one]; rfl
  · have eq : correctionSlot r i j = ⟨0,(0 : Fin 1)⟩ := by simp [correctionSlot,equal]
    rw [eq,Matrix.diagonal_apply_ne _ equal]
    rfl

/-- Assemble the correction matrix using the two packed pivot archives and
the fixed-width zero and one. Reading any selected word skips at most 64 words. -/
theorem childCorrection_writes {T Q A M r : ℕ} [NeZero M] {P U : Type}
    (body : P → Pr P T Q A U) (read : Fin 4 → Fin 7 ↪ Fin T) (out : Fin T)
    (shared : ∀ k, read k 3 = out) (fits : r ≤ 64) (weight : Fin 64 → (ZMod M)ˣ) (H : ℕ) :
    let value := correctionValue fits weight
    let slot := correctionSlot r
    let ok := fun R : Node.Regs T A => ∀ k, R (read k 2) =
      (List.ofFn fun j => binSyms H (value k j).val).flatten ∧
      (R (read k 1)).length = H ∧ ∀ t : Fin 7, t = 0 ∨ 4 ≤ t → R (read k t) = []
    let emit := fun i j => readMatrixWord (slot i j).2.val (read (slot i j).1)
    LabelTraversal.Writes body ok out
      (LabelTraversal.sequence (fun i => LabelTraversal.sequence (emit i) (List.finRange 128)) (List.finRange 128))
      (matrixWords A H (Matrix.diagonal fun k => (childCorrection r weight k : ZMod M)))
      (128*(128*(8*(64*H)+14*H+22)+1)+1) := by
  intro value slot ok emit
  have lengths (k : Fin 4) : correctionLength r k ≤ 64 := by fin_cases k <;> first | exact fits | exact (by decide : 1 ≤ 64)
  have write := matrixFromArchives_writes body read out shared (correctionLength r) value
    (fun i j => (slot i j).1) (fun i j => (slot i j).2) H 64
    (fun i j => (slot i j).2.isLt.le.trans (lengths _))
  have matrix : (fun i j => value (slot i j).1 (slot i j).2) =
      Matrix.diagonal (fun k => (childCorrection r weight k : ZMod M)) := by
    funext i j
    exact correctionValue_slot fits weight i j
  rw [← matrix]
  exact write

/-- Keep the caller's modulus, unit, positive weights and inverses on their
original tapes. Use six private tapes for zero, scratch and matrix output. -/
def callerCorrectionPorts (k : Fin 4) : Fin 7 ↪ Fin 64 :=
  ⟨![59,2,(![58,44,55,56] : Fin 4 → Fin 64) k,60,61,62,63],
    by fin_cases k <;> decide⟩

/-- Install the correction from the rank-sized archives saved by the good
caller. Only the matrix destination changes, including when the rank is zero. -/
theorem callerCorrection_writes {T Q A M r : ℕ} [NeZero M] {P U : Type}
    (body : P → Pr P T Q A U) (bank : Fin 64 ↪ Fin T)
    (fits : r ≤ 64) (pivot : Fin r → (ZMod M)ˣ) (H : ℕ) :
    let weight := fun i : Fin 64 => if h : i.val < r then pivot ⟨i.val,h⟩ else 1
    let read := fun k => (callerCorrectionPorts k).trans bank
    let emit := fun i j => let slot := correctionSlot r i j
                           readMatrixWord slot.2.val (read slot.1)
    LabelTraversal.Writes body (fun R => (R (bank 2)).length = H ∧
      R (bank 44) = binSyms H (1 : ZMod M).val ∧ R (bank 58) = binSyms H 0 ∧
      R (bank 55) = (List.ofFn fun i => binSyms H (pivot i : ZMod M).val).flatten ∧
      R (bank 56) = (List.ofFn fun i => binSyms H (pivot i).inv.val).flatten ∧
      ∀ k ∈ ([59,61,62,63] : List (Fin 64)), R (bank k) = [])
      (bank 60) (LabelTraversal.sequence (fun i => LabelTraversal.sequence (emit i)
        (List.finRange 128)) (List.finRange 128))
      (matrixWords A H (Matrix.diagonal fun k => (childCorrection r weight k : ZMod M)))
      (128*(128*(8*(64*H)+14*H+22)+1)+1) := by
  intro weight read emit u S ⟨width,one,zero,pos,inv,free⟩
  apply childCorrection_writes body read (bank 60) (fun _ => rfl) fits weight H u S
  intro k
  refine ⟨?_,width,?_⟩
  · fin_cases k
    · simpa [read,callerCorrectionPorts,correctionLength,correctionValue,List.ofFn_succ] using zero
    · simpa [read,callerCorrectionPorts,correctionLength,correctionValue,List.ofFn_succ] using one
    · change S.R (bank 55) = (List.ofFn fun i : Fin r => binSyms H (weight (i.castLE fits) : ZMod M).val).flatten
      simpa [weight] using pos
    · change S.R (bank 56) = (List.ofFn fun i : Fin r => binSyms H (weight (i.castLE fits)).inv.val).flatten
      simpa [weight] using inv
  · intro t ht
    exact free _ ((by decide : ∀ (k : Fin 4) (t : Fin 7), t = 0 ∨ 4 ≤ t →
      callerCorrectionPorts k t ∈ ([59,61,62,63] : List (Fin 64))) k t ht)

/-- Make the zero constant from the modulus width, then release its tape
after writing the matrix. The payload and both caller archives are preserved. -/
theorem prepareCorrection_writes {T Q A M r : ℕ} [NeZero M] {P U : Type}
    (body : P → Pr P T Q A U) (bank : Fin 64 ↪ Fin T)
    (fits : r ≤ 64) (pivot : Fin r → (ZMod M)ˣ) (H : ℕ) :
    let weight := fun i : Fin 64 => if h : i.val < r then pivot ⟨i.val,h⟩ else 1
    let emit := fun i j => let slot := correctionSlot r i j
                           readMatrixWord slot.2.val ((callerCorrectionPorts slot.1).trans bank)
    let write := LabelTraversal.sequence (fun i => LabelTraversal.sequence (emit i)
      (List.finRange 128)) (List.finRange 128)
    LabelTraversal.Writes body (fun R => (R (bank 2)).length = H ∧
      R (bank 44) = binSyms H (1 : ZMod M).val ∧
      R (bank 55) = (List.ofFn fun i => binSyms H (pivot i : ZMod M).val).flatten ∧
      R (bank 56) = (List.ofFn fun i => binSyms H (pivot i).inv.val).flatten ∧
      ∀ k ∈ ([58,59,61,62,63] : List (Fin 64)), R (bank k) = [])
      (bank 60) ((bzero (bank 2) (bank 58) (bank 59)).seq (write.seq (bclear (bank 58))))
      (matrixWords A H (Matrix.diagonal fun k => (childCorrection r weight k : ZMod M)))
      (4*H+4+(128*(128*(8*(64*H)+14*H+22)+1)+1+(2*H+2))) := by
  intro weight emit write u S ⟨width,one,pos,inv,free⟩
  obtain ⟨y,same,init⟩ := bzero_exec body (wR := bank 2) (c := bank 58) (t := bank 59)
    (by simp) u S (free 59 (by decide))
  rw [width,free 58 (by decide),List.append_nil] at init
  let D : Stacks T A := {S with R := Function.update S.R (bank 58) (binSyms H 0)}
  obtain ⟨z,n,user,paid,run⟩ := callerCorrection_writes body bank fits pivot H y D
    ⟨by simpa [D] using width,by simpa [D] using one,Function.update_self ..,
      by simpa [D] using pos,by simpa [D] using inv,by
        intro k hk
        have ne : k ≠ 58 := fun eq => by subst k; simp at hk
        rw [show D.R (bank k) = S.R (bank k) from Function.update_of_ne (bank.injective.ne ne) ..]
        exact free _ (List.mem_cons_of_mem _ hk)⟩
  let word := matrixWords A H (Matrix.diagonal fun k => (childCorrection r weight k : ZMod M))
  let F : Stacks T A := {D with R := Function.update D.R (bank 60) (word ++ D.R (bank 60))}
  obtain ⟨out,unchanged,_,clear⟩ := bclear_exec (body := body) (bank 58) z F
  have len : (F.R (bank 58)).length = H := by simp [F,D,length_binSyms]
  rw [len] at clear
  refine ⟨out,_,unchanged.trans (user.trans same),Nat.add_le_add_left (Nat.add_le_add_right paid _) _,
    (Exec.seq init (Exec.seq run clear)).cast rfl ?_⟩
  congr 2
  funext k
  by_cases zero : k = bank 58
  · subst k; simp [free 58 (by decide)]
  · simp [F,D,word,Function.update_apply,zero]

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem replaceColumnRecord {T d w W : ℕ} (col : Fin 35 ↪ Fin T) (H J : ℕ)
    (record tail : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ) (original : Fin ((prime^(w+1))^d*W) → ZMod 2)
    (addr : (Fin d → ZMod (prime^(w+1))) → Fin d → ZMod (prime^(w+1))) (S : Stacks T prime)
    (ready : ColumnRecordReady col H J tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original addr S) :
    ColumnRecordReady col H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original addr
      {S with R := Function.update S.R (col 34) record} := by
  exact ready.replaceArchive rfl (fun i ne => Function.update_of_ne (col.injective.ne ne) ..)
    (Function.update_self ..)

/-- Prepending the correction on the column archive preserves the positioned
child payload and establishes the scaling program's input representation. -/
theorem correctionColumnReady {T d w W : ℕ} (col : Fin 35 ↪ Fin T) (H J : ℕ)
    (matrix : Matrix (Fin d) (Fin d) (ZMod (prime^(w+1)))) (tail : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ) (original : Fin ((prime^(w+1))^d*W) → ZMod 2)
    (addr : (Fin d → ZMod (prime^(w+1))) → Fin d → ZMod (prime^(w+1))) (S : Stacks T prime)
    (ready : ColumnRecordReady col H J tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original addr S) :
    ColumnReady col H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original addr
      {S with R := Function.update S.R (col 34) (matrixWords prime H matrix ++ S.R (col 34))} := by
  obtain ⟨word,frame,reads⟩ := ready
  rw [frame.archive]
  exact replaceColumnRecord col H J _ tail dest q original addr S ⟨word,frame,reads⟩

/-- A returned word with the unweighted child action on its rank fields
supplies the positioned parent record consumed by the correction. -/
theorem ordinaryChild_return {T r g w W : ℕ}
    (col : Fin 35 ↪ Fin T) (H J : ℕ) (tail : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ) (S F : Stacks T prime) :
    let M := prime^(w+1)
    let d := r+g
    ∀ (original before after : Fin (M^(d+d)*W) → ZMod 2)
      (input : (Fin (d+d) → ZMod M) → IntegerMultBounds.Swap.Shear.State (Fin d) (ZMod M)),
      RecordReady (b := prime) (w := w) (W := W) (d := d+d) col H J tail SparseRoleCircuit.encode
        (fun _ => blank) dest 0 q before S →
      (∀ x j, before (FlatCoordinateLayout.index (Fin.append (input x).1 (input x).2) j) =
        original (FlatCoordinateLayout.index x j)) →
      (∀ k : Fin 35, k ≠ 24 → F.L (col k) = S.L (col k) ∧ F.R (col k) = S.R (col k)) →
      (∀ z, RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0
        (List.ofFn (SparseRoleCircuit.encode ∘ after)) z) = readAt blank (F.L (col 24)) (F.R (col 24)) (z-0)) →
      (∀ (hg tg : Fin g → ZMod M) (h d : Fin r → ZMod M) (j : Fin W),
        let addr := fun h d => let t := childFields hg tg (h,fun i => d i.rev)
                               FlatCoordinateLayout.index (Fin.append t.1 t.2) j
        after (addr d h) = before (addr h d)) →
      ColumnRecordReady col H J tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
        (fun x => let t := Weighted.child r (fun _ => 1) (fun _ => 1) (input x); Fin.append t.1 t.2) F := by
  intro M d original before after input layout reads keep returned action
  refine ⟨after,layout.returnPayload keep returned,?_⟩
  intro x j
  apply Eq.trans _ (reads x j)
  apply goodChild_effect (fun _ => 1) (fun _ => 1) before after
  intro hg tg s j
  have cell := action hg tg s.1 (fun i => s.2 i.rev) j
  simpa only [Weighted.child,Fin.isLt,ite_true,one_mul,Fin.rev_rev] using cell

/-- With the correction diagonal installed, the physical pair program
converts the ordinary child address to the weighted one. -/
theorem childCorrection_exec [M8.Machine.Net] {P U : Type} {w W : ℕ}
    (r : ℕ) (weight : Fin 64 → (ZMod (prime^(w+1)))ˣ)
    (H J : ℕ) (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P ((rowSwapBlock.tapes+35)+1) columnCapacity prime U)
    (u : HS ((rowSwapBlock.tapes+35)+1) columnCapacity prime U)
    (S : Stacks ((rowSwapBlock.tapes+35)+1) prime) (tail rest : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+((prime^(w+1))^128*W : ℕ) → dest z = blank)
    (original : Fin ((prime^(w+1))^128*W) → ZMod 2)
    (input : (Fin 128 → ZMod (prime^(w+1))) → IntegerMultBounds.Swap.Shear.State (Fin 64) (ZMod (prime^(w+1)))) :
    let a := childCorrection r weight
    let ready := fun y (D : Stacks ((rowSwapBlock.tapes+35)+1) prime) =>
      ColumnReady columnBank H J (Matrix.diagonal (fun j => (a j : ZMod (prime^(w+1)))))
        tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ j : Fin (rowSwapBlock.tapes+35), 35 ≤ j.val → D.L (columnPorts j) = [] ∧ D.R (columnPorts j) = []) ∧
      D.R (Fin.last (rowSwapBlock.tapes+35)) = rest
    let plain := fun x => Weighted.child r (fun _ => 1) (fun _ => 1) (input x)
    let corrected := fun x => Weighted.child r (fun i => (weight i : ZMod (prime^(w+1))))
      (fun i => ((weight i)⁻¹ : (ZMod (prime^(w+1)))ˣ)) (input x)
    let addr := fun x => Fin.addCases (plain x).1 (plain x).2
    ready addr S → ∃ z F n, z.user = u.user ∧
      n ≤ ((List.finRange 127).map (fun i => pairScalingTime U i.succ 0 i.succ w W H J)).sum+1 ∧
      Exec body (diagonalPairs (List.finRange 127)) (mk u S) n (mk z F) ∧
      ready (fun x => Fin.addCases (corrected x).1 (corrected x).2) F := by
  intro a ready plain corrected addr before
  have anchor : (fun x j => (((Fin.cons 1 (fun _ => 1) : Fin 128 → (ZMod (prime^(w+1)))ˣ) j) : ZMod (prime^(w+1))) * addr x j) = addr := by
    funext x j
    cases j using Fin.cases <;> simp
  obtain ⟨z,F,n,user,paid,run,after⟩ := diagonalPairs_addr_exec (d := 127) a H J hm hw hW
    body u S tail rest dest q empty original 1 (childCorrection_prod r weight) addr (anchor.symm ▸ before)
  have action : (fun x => (Matrix.diagonal (fun j => (a j : ZMod (prime^(w+1))))).mulVec (addr x)) =
      (fun x => Fin.addCases (corrected x).1 (corrected x).2) := by
    funext x j
    rw [Matrix.mulVec_diagonal]
    exact childCorrection_apply r weight (input x) j
  exact ⟨z,F,n,user,paid,run,action ▸ after⟩

/-- The modulus, payload banks, spectator width, padded one, clock and matrix
archive are already on the caller. The column machine owns its other tapes. -/
def correctionColumnSlots : Fin 7 ↪ Fin 35 := ⟨![2,24,25,27,32,33,34],by decide⟩
def correctionCallerSlots : Fin 7 ↪ Fin 64 := ⟨![2,24,25,53,44,45,60],by decide⟩

noncomputable def correctionRole [M8.Machine.Net] (j : Fin ((rowSwapBlock.tapes+35)+1)) : Option (Fin 7) :=
  if h : ∃ k, columnBank (correctionColumnSlots k) = j then some h.choose else none

theorem correctionRole_eq [M8.Machine.Net] {j k} (eq : correctionRole j = some k) :
    columnBank (correctionColumnSlots k) = j := by
  unfold correctionRole at eq
  split at eq
  · rename_i h
    exact Option.some.inj eq ▸ h.choose_spec
  · contradiction

noncomputable def correctionColumnPlacement [M8.Machine.Net] {T : ℕ} (bank : Fin 64 ↪ Fin T)
    (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T) (apart : ∀ i j, work i ≠ bank j) :
    Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T :=
  ⟨sharedRegisterPlacement work (correctionCallerSlots.trans bank) correctionRole,
    sharedRegisterPlacement_injective work work.injective _ (correctionCallerSlots.trans bank).injective
      (fun i j => apart i _) _ (fun _ _ _ h k => (correctionRole_eq h).symm.trans (correctionRole_eq k))⟩

theorem correctionColumnPlacement_shared [M8.Machine.Net] {T : ℕ} (bank : Fin 64 ↪ Fin T)
    (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T) (apart : ∀ i j, work i ≠ bank j) (k : Fin 7) :
    correctionColumnPlacement bank work apart (columnBank (correctionColumnSlots k)) = bank (correctionCallerSlots k) := by
  have h : ∃ i, columnBank (correctionColumnSlots i) = columnBank (correctionColumnSlots k) := ⟨k,rfl⟩
  have eq := correctionColumnSlots.injective (columnBank.injective h.choose_spec)
  simp [correctionColumnPlacement,sharedRegisterPlacement,correctionRole,h,eq]

theorem correctionColumnPlacement_off [M8.Machine.Net] {T : ℕ} (bank : Fin 64 ↪ Fin T)
    (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T) (apart : ∀ i j, work i ≠ bank j)
    (j : Fin 64) (outside : ∀ k, correctionCallerSlots k ≠ j) :
    ∀ i, correctionColumnPlacement bank work apart i ≠ bank j := by
  intro i
  change sharedRegisterPlacement work (correctionCallerSlots.trans bank) correctionRole i ≠ bank j
  cases h : correctionRole i with
  | none => simpa [sharedRegisterPlacement,h] using apart i j
  | some k => simpa [sharedRegisterPlacement,h] using bank.injective.ne (outside k)

/-- Prepare and apply the pivot correction on a common archive port.
The column machine leaves every tape outside its placement unchanged. -/
theorem preparedCorrection_exec [M8.Machine.Net] {T w W r : ℕ} {P U : Type}
    (bank : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ bank j) (fits : r ≤ 64)
    (pivot : Fin r → (ZMod (prime^(w+1)))ˣ) (H J : ℕ)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P T columnCapacity prime U) (u : HS T columnCapacity prime U) (S : Stacks T prime)
    (tail : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+((prime^(w+1))^128*W : ℕ) → dest z = blank)
    (original : Fin ((prime^(w+1))^128*W) → ZMod 2)
    (input : (Fin 128 → ZMod (prime^(w+1))) → IntegerMultBounds.Swap.Shear.State (Fin 64) (ZMod (prime^(w+1)))) :
    let ports := correctionColumnPlacement bank work apart
    let weight := fun i : Fin 64 => if h : i.val < r then pivot ⟨i.val,h⟩ else 1
    let emit := fun i j => let slot := correctionSlot r i j
                           readMatrixWord slot.2.val ((callerCorrectionPorts slot.1).trans bank)
    let write := LabelTraversal.sequence (fun i => LabelTraversal.sequence (emit i) (List.finRange 128)) (List.finRange 128)
    let prep := (bzero (bank 2) (bank 58) (bank 59)).seq (write.seq (bclear (bank 58)))
    let col := columnBank.trans ports
    let ready := fun record y D => ColumnRecordReady col H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D
    let plain := fun x => Weighted.child r (fun _ => 1) (fun _ => 1) (input x)
    let corrected := fun x => Weighted.child r (fun i => (weight i : ZMod (prime^(w+1))))
      (fun i => ((weight i)⁻¹ : (ZMod (prime^(w+1)))ˣ)) (input x)
    let matrix := Matrix.diagonal fun k => (childCorrection r weight k : ZMod (prime^(w+1)))
    let scratch := fun D : Stacks T prime => ∀ j : Fin (rowSwapBlock.tapes+35), 35 ≤ j.val →
      D.L (ports (columnPorts j)) = [] ∧ D.R (ports (columnPorts j)) = []
    S.R (bank 55) = (List.ofFn fun i => binSyms H (pivot i : ZMod (prime^(w+1))).val).flatten →
    S.R (bank 56) = (List.ofFn fun i => binSyms H (pivot i).inv.val).flatten →
    (∀ k ∈ ([58,59,61,62,63] : List (Fin 64)), S.R (bank k) = []) →
    ready tail (fun x (j : Fin (64+64)) => Fin.addCases (plain x).1 (plain x).2 j) S → scratch S →
    ∃ z F n, z.user = u.user ∧
      n ≤ 4*H+4+(128*(128*(8*(64*H)+14*H+22)+1)+1+(2*H+2)) +
        (1+(((List.finRange 127).map (fun i => pairScalingTime U i.succ 0 i.succ w W H J)).sum+1)) + (128*128*(4*H+4)+1) ∧
      Exec body ((prep.seq (placedDiagonalPairs ports 127)).seq (dropWords (col 2) (col 34) (col 0) (128*128))) (mk u S) n (mk z F) ∧
      ready tail (fun x (j : Fin (64+64)) => Fin.addCases (corrected x).1 (corrected x).2 j) F ∧
      scratch F ∧ F.R (ports (Fin.last _)) = S.R (ports (Fin.last _)) ∧ (∀ j : Fin 64, (∀ k, correctionCallerSlots k ≠ j) →
        F.L (bank j) = S.L (bank j) ∧ F.R (bank j) = S.R (bank j)) ∧ ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro ports weight emit write prep col ready plain corrected matrix scratch pos inv free before clean
  have width : (S.R (bank 2)).length = H := by
    have shared : col 2 = bank 2 := correctionColumnPlacement_shared bank work apart 0
    rw [← shared,before.choose_spec.1.modulus,length_binSyms]
  have unit : S.R (bank 44) = binSyms H (1 : ZMod (prime^(w+1))).val := by
    have shared : col 32 = bank 44 := correctionColumnPlacement_shared bank work apart 4
    rw [← shared,before.choose_spec.1.padded]
  obtain ⟨y,t,user,paid,prepare⟩ := prepareCorrection_writes body bank fits pivot H u S ⟨width,unit,pos,inv,free⟩
  let D : Stacks T prime := {S with R := Function.update S.R (col 34) (matrixWords prime H matrix ++ S.R (col 34))}
  have shared : bank 60 = ports (columnBank 34) := (correctionColumnPlacement_shared bank work apart 6).symm
  rw [shared] at prepare
  have live := correctionColumnReady col H J matrix tail dest q original _ S before
  have project y D : ColumnReady col H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ↔
      ColumnReady columnBank H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y (embStk ports D) :=
    (columnReady_project ..).trans (columnReady_project columnBank H J matrix tail SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original y (embStk ports D)).symm
  let cap : 0 < columnCapacity := lt_of_lt_of_le (by decide : 0 < 217) (le_max_left ..)
  have cleanD : scratch D := by
    intro j hj
    have ne : columnPorts j ≠ columnBank 34 := by
      intro eq
      have same := congrArg Fin.val eq
      change j.val = 34 at same
      omega
    simpa [D,col,Function.update_of_ne (ports.injective.ne ne)] using clean j hj
  obtain ⟨v,E,n,same,time,run,done,unused,lastWord⟩ := childCorrection_exec r weight H J hm hw hW
    (P := Empty) Empty.elim (stateLiftDown cap (embDn ports y)) (embStk ports D) tail
    (D.R (ports (Fin.last _))) dest q empty original input ⟨(project ..).1 live,cleanD,rfl⟩
  · obtain ⟨z,_,zu,placed⟩ := statePlaced_exec_normalized ports ports.injective le_rfl cap Empty.elim
      (body' := body) (fun e => nomatch e) y D run
    let F := embOvr ports E.get D
    have eq : embStk ports F = E := embStk_ovr ports.injective _ _
    rw [← eq] at done unused lastWord
    have result := (project ..).2 done
    obtain ⟨word,record,reads⟩ := result
    obtain ⟨out,final,drop⟩ := consumeMatrix_exec col body z F H matrix tail record.archive
      ((congrArg List.length record.modulus).trans (length_binSyms ..)) (record.scratch 0 (by decide)).2
    let G : Stacks T prime := {F with R := Function.update F.R (col 34) tail}
    have frame (j : Fin T) (off : ∀ i, ports i ≠ j) : G.L j = S.L j ∧ G.R j = S.R j := by
      obtain ⟨left,right⟩ := embOvr_off E.get D off
      have ne := (off (columnBank 34)).symm
      exact ⟨left,(Function.update_of_ne ne ..).trans (right.trans (Function.update_of_ne ne ..))⟩
    refine ⟨out,G,_,final.trans (zu.trans (same.trans user)),Nat.add_le_add_right (Nat.add_le_add paid (Nat.add_le_add_left time 1)) _,
      Exec.seq (Exec.seq prepare placed) drop,replaceColumnRecord col H J _ _ dest q original _ F ⟨word,record,reads⟩,?_,?_,
      fun j hj => frame _ (correctionColumnPlacement_off bank work apart j hj),frame⟩
    · intro j hj
      have ne : columnPorts j ≠ columnBank 34 := by
        intro eq
        have same := congrArg Fin.val eq
        change j.val = 34 at same
        omega
      simpa [G,col,Function.update_of_ne (ports.injective.ne ne),embStk] using unused j hj
    · have ne : ports (Fin.last _) ≠ col 34 := by
        intro e
        have same : Fin.last (rowSwapBlock.tapes+35) = columnBank 34 := ports.injective e
        have h := congrArg Fin.val same
        change rowSwapBlock.tapes+35 = 34 at h
        omega
      simpa [G,D,Function.update_of_ne ne,embStk] using lastWord


end IntegerMultBounds.MathlibTM2.M6.BitNode
