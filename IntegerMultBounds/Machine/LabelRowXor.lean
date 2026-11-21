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

/-- After one reduction the source already points to the next block.
Advance only the accumulator before starting the next reduction. -/
def advance (i : Fin 2) : Move := if i = 0 then .stay else .right

def blockProgram (a : ℕ) :=
  seq (program a) (extend (RoleArrayStackMoves.moveProgram (a := a) advance) 2)

def blocksProgram (a : ℕ) := CountedLoopReuseAlphabet.program (blockProgram a)

theorem blocks_hoare {a K blocks cost : ℕ} (width count total : List Bool)
    (hw : Counter.value width = K) (hb : Counter.value total = blocks)
    (ready : ℕ → Tapes 2 a → Prop) (v : Tapes 2 a) (start : ready 0 v)
    (step : ∀ i < blocks, ∀ u, ready i u → ∃ F,
      HoareTime (program a) (· = bank u width count) (· = bank F width count) cost ∧
      ready (i+1) (RoleArrayStackMoves.shifted F advance K)) :
    ∃ F, ready blocks F ∧
      HoareTime (blocksProgram a)
        (· = CountedLoopReuseAlphabet.bank (bank v width count) CountedLoopReuseAlphabet.empty
          (CountedLoopReuseAlphabet.binary total) 1 1)
        (· = CountedLoopReuseAlphabet.bank (bank F width count) CountedLoopReuseAlphabet.empty
          (CountedLoopReuseAlphabet.binary total) 1 1)
        (blocks*(cost+7*K+7*width.length+23)+7*total.length+16) := by
  classical
  let next := fun i (u : Tapes 2 a) => if h : i < blocks ∧ ready i u then
    RoleArrayStackMoves.shifted (step i h.1 u h.2).choose advance K else u
  let state := fun i => Nat.rec (motive := fun _ => Tapes 2 a) v next i
  have valid (i) (hi : i ≤ blocks) : ready i (state i) := by
    induction i with
    | zero => exact start
    | succ i ih =>
      have h : i < blocks ∧ ready i (state i) := ⟨by omega,ih (by omega)⟩
      change ready (i+1) (next i (state i))
      simp only [next,dite_eq_left h]
      exact (step i h.1 _ h.2).choose_spec.2
  have run := CountedLoopReuseAlphabet.loop_hoare (blockProgram a) total blocks
    (fun i => bank (state i) width count) (fun _ => cost+7*K+7*width.length+17) hb (by
      intro i hi
      have h := valid i hi.le
      obtain ⟨scan,_⟩ := (step i hi _ h).choose_spec
      have move := hoare_extend_eq (RoleArrayStackMoves.move_hoare (step i hi _ h).choose advance width K hw)
        (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary count) 1 1)
      change HoareTime _ _ (· = bank (next i (state i)) width count) _
      simp only [next,dite_eq_left (And.intro hi h)]
      exact (scan.seq move).consequence (fun _ h => h) (fun _ h => h) (by omega))
  refine ⟨state blocks,valid _ le_rfl,run.consequence (fun _ h => h) (fun _ h => h) ?_⟩
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]
  simp only [Nat.mul_add]; omega

/-- Reduce every consecutive block into its own accumulator record. -/
theorem blocks_run {a K N B : ℕ} (v : Tapes 2 a) (width count total : List Bool)
    (hw : Counter.value width = K) (hn : Counter.value count = N) (hb : Counter.value total = B)
    (x : Fin B → Fin N → Fin K → ZMod 2)
    (input : ∀ b r j, v.tape 0 (v.head 0+b.val*(N*K)+r.val*K+j.val) = SparseRoleCircuit.encode (x b r j))
    (zero : ∀ (b : Fin B) (j : Fin K), v.tape 1 (v.head 1+b.val*K+j.val) = SparseRoleCircuit.encode 0) :
    let frame := fun u => CountedLoopReuseAlphabet.bank (bank u width count) CountedLoopReuseAlphabet.empty
      (CountedLoopReuseAlphabet.binary total) 1 1
    ∃ F, HoareTime (blocksProgram a) (· = frame v) (· = frame F)
      (B*(N*(14*K+14*width.length+39)+7*count.length+16+7*K+7*width.length+23)+7*total.length+16) ∧
      F.head 0 = v.head 0+B*(N*K) ∧ F.head 1 = v.head 1+B*K ∧ F.tape 0 = v.tape 0 ∧
      ∀ b j, F.tape 1 (v.head 1+b.val*K+j.val) = SparseRoleCircuit.encode (∑ r, x b r j) := by
  intro frame
  let ready := fun (i : ℕ) (u : Tapes 2 a) =>
    u.head 0 = v.head 0+i*(N*K) ∧ u.head 1 = v.head 1+i*K ∧ u.tape 0 = v.tape 0 ∧
    ∀ (b : Fin B) (j : Fin K), u.tape 1 (v.head 1+b.val*K+j.val) =
      (if b.val < i then SparseRoleCircuit.encode (∑ r, x b r j) else SparseRoleCircuit.encode 0)
  obtain ⟨F,done,exec⟩ := blocks_hoare width count total hw hb ready v
    (by simpa [ready] using zero) (fun i hi u ⟨hs,hd,src,values⟩ => by
      let b : Fin B := ⟨i,hi⟩
      obtain ⟨D,scan,ss,dd,st,acc,off⟩ := run u width count K N hw hn (x b) (fun _ => 0)
        (fun r j => by rw [src,hs]; exact input b r j)
        (fun j => by rw [hd]; simpa [b] using values b j)
      refine ⟨D,scan,?_,?_,st.trans src,?_⟩
      · simp [RoleArrayStackMoves.shifted,advance,Move.offset,ss,hs,add_mul,add_assoc]
      · simp [RoleArrayStackMoves.shifted,advance,Move.offset,dd,hd,add_mul,add_assoc]
      intro k j
      change D.tape 1 _ = _
      by_cases eqn : k.val = i
      · have same : k = b := Fin.ext eqn
        subst k
        simpa [hd,b] using acc j
      · have gap (m n : ℕ) (lt : m < n) : (m : ℤ)*K+K ≤ (n : ℤ)*K := by
          have h := Nat.mul_le_mul_right K (Nat.succ_le_of_lt lt)
          exact_mod_cast (show m*K+K ≤ n*K by simpa [Nat.succ_mul] using h)
        have outside : ¬(u.head 1 ≤ v.head 1+k.val*K+j.val ∧ v.head 1+k.val*K+j.val < u.head 1+K) := by
          rw [hd]
          rcases lt_or_gt_of_ne eqn with h | h
          · have := gap _ _ h; omega
          · have := gap _ _ h; omega
        rw [off _ outside,values]
        by_cases h : k.val < i <;> simp [h,show (k.val < i+1) ↔ k.val < i by omega])
  obtain ⟨hs,hd,src,values⟩ := done
  exact ⟨F,exec,hs,hd,src,fun b j => by simpa [b.isLt] using values b j⟩

end IntegerMultBounds.Machine.LabelRowXor
