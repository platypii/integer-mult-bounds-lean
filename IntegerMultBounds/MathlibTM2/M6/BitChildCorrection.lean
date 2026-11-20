module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDiagonalProgram
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

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

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

end IntegerMultBounds.MathlibTM2.M6.BitNode
