module

public import IntegerMultBounds.Machine.RoleArrayStackMoves
public import IntegerMultBounds.Machine.SparseRoleCircuit

/-! XOR consecutive equal-length records into a reusable accumulator. -/
@[expose] public section
namespace IntegerMultBounds.Machine.LabelRowXor

def rewind (i : Fin 2) : Move := if i = 0 then .stay else .left

def rowProgram (a : ℕ) :=
  seq (PointwiseBinary.program (PointwiseBinary.xorSymbol (a := a)))
    (RoleArrayStackMoves.moveProgram rewind)

private def row {a : ℕ} (v : Tapes 2 a) (K : ℕ) :=
  RoleArrayStackMoves.shifted (PointwiseBinary.result PointwiseBinary.xorSymbol v K) rewind K

private theorem row_hoare {a : ℕ} (v : Tapes 2 a) (bs : List Bool) (K : ℕ) (width : Counter.value bs = K) :
    HoareTime (rowProgram a) (fun w => w = RoleArrayStackMoves.ready v bs)
      (fun w => w = RoleArrayStackMoves.ready (row v K) bs) (14*K+14*bs.length+33) := by
  have scan := PointwiseBinary.apply_hoare PointwiseBinary.xorSymbol v bs K width
  have back := RoleArrayStackMoves.move_hoare (PointwiseBinary.result PointwiseBinary.xorSymbol v K)
    rewind bs K width
  exact (scan.seq back).consequence (fun _ h => h) (fun _ h => h) (by omega)

def program (a : ℕ) := CountedLoopReuseAlphabet.program (rowProgram a)

private def rows {a : ℕ} (v : Tapes 2 a) (K : ℕ) : ℕ → Tapes 2 a
  | 0 => v
  | n+1 => row (rows v K n) K

private theorem heads {a : ℕ} (v : Tapes 2 a) (K n : ℕ) :
    (rows v K n).head 0 = v.head 0 + n*K ∧ (rows v K n).head 1 = v.head 1 := by
  induction n with
  | zero => simp [rows]
  | succ n ih =>
    simp only [rows,row,RoleArrayStackMoves.shifted,PointwiseBinary.heads,ih.1,ih.2]
    simp [rewind,Move.offset,add_mul]
    ring

private theorem source {a : ℕ} (v : Tapes 2 a) (K n : ℕ) :
    (rows v K n).tape 0 = v.tape 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (PointwiseBinary.source _ _ _).trans ih

def bank {a : ℕ} (v : Tapes 2 a) (width count : List Bool) :=
  CountedLoopReuseAlphabet.bank (RoleArrayStackMoves.ready v width) CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary count) 1 1

/-- A fixed six-tape program advances over all records, restores the accumulator
head and both clocks, and keeps the input tape and exterior accumulator intact. -/
theorem run {a : ℕ} (v : Tapes 2 a) (width count : List Bool) (K N : ℕ)
    (hw : Counter.value width = K) (hn : Counter.value count = N)
    (x : Fin N → Fin K → ZMod 2) (y : Fin K → ZMod 2)
    (input : ∀ i j, v.tape 0 (v.head 0 + i.val*K + j.val) = SparseRoleCircuit.encode (x i j))
    (acc : ∀ j, v.tape 1 (v.head 1+j.val) = SparseRoleCircuit.encode (y j)) :
    ∃ out, HoareTime (program a) (fun w => w = bank v width count)
        (fun w => w = bank out width count) (N*(14*K+14*width.length+39)+7*count.length+16) ∧
      out.head 0 = v.head 0 + N*K ∧ out.head 1 = v.head 1 ∧ out.tape 0 = v.tape 0 ∧
      (∀ j : Fin K, out.tape 1 (v.head 1+j.val) = SparseRoleCircuit.encode (y j + ∑ i, x i j)) ∧
      ∀ z, ¬(v.head 1 ≤ z ∧ z < v.head 1+K) → out.tape 1 z = v.tape 1 z := by
  have exec := CountedLoopReuseAlphabet.loop_hoare (rowProgram a) count N
    (fun i => RoleArrayStackMoves.ready (rows v K i) width) (fun _ => 14*K+14*width.length+33)
    hn (fun i _ => row_hoare _ width K hw)
  refine ⟨rows v K N,exec.consequence (fun _ h => h) (fun _ h => h) ?_,(heads _ _ _).1,
    (heads _ _ _).2,source _ _ _,?_,?_⟩
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]
    apply le_of_eq
    ring
  · have prefixSum (n : ℕ) (bound : n ≤ N) (j : Fin K) : (rows v K n).tape 1 (v.head 1+j.val) =
        SparseRoleCircuit.encode (y j + ∑ i : Fin n, x (i.castLE bound) j) := by
      induction n with
      | zero => simpa [rows] using acc j
      | succ n ih =>
        change (PointwiseBinary.result _ (rows v K n) K).tape 1 _ = _
        rw [PointwiseBinary.destination,(heads _ _ _).1,(heads _ _ _).2,source]
        have inside : v.head 1 ≤ v.head 1+j.val ∧ v.head 1+j.val < v.head 1+K := by omega
        rw [ite_eq_left inside]
        rw [show v.head 1+j.val-v.head 1 = (j.val : ℤ) by omega,input ⟨n,by omega⟩ j,
          ih (by omega),SparseRoleCircuit.encode_add,Fin.sum_univ_castSucc]
        congr 1
        rw [add_assoc]
        rfl
    intro j
    simpa using prefixSum N le_rfl j
  · intro z outside
    clear exec input hn x
    induction N with
    | zero => rfl
    | succ n ih =>
      change (PointwiseBinary.result _ (rows v K n) K).tape 1 z = _
      rw [PointwiseBinary.destination,(heads _ _ _).2,ite_eq_right outside]
      exact ih

end IntegerMultBounds.Machine.LabelRowXor
