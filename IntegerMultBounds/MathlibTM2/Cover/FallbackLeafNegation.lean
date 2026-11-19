module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackMiddleReturn
public import IntegerMultBounds.Machine.FiberShift
public import IntegerMultBounds.Machine.BlockNegationReuse
public import IntegerMultBounds.Machine.FiberLayoutData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalUnaryHeader

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack

/-- Negate the head coordinate of one prefix fiber. The same block and tail
descriptors serve every prefix, and the scratch tape returns to its input. -/
theorem negateLeafFiber_hoare {P M B : ℕ} (hM : 0 < M) (hB : 0 < B)
    (word : Fin (P*(M*B)) → Fin 4) (i : Fin P)
    (source dest scratch : ℤ → Fin 4) (p q r : ℤ)
    (clean : ∀ z, r ≤ z → z < r+(((M-1)*B : ℕ) : ℤ) → scratch z = blank) :
    let blocks := FiberLayoutData.fiber word i
    let bits := fun n : ℕ => Host.binBits n.size n
    let bank := fun out x y => BlockNegationReuse.bank (putWord source p blocks.flatten) out scratch
      (bits B) (bits ((M-1)*B)) (bits (M-1)) x y r
    HoareTime BlockNegationReuse.program (fun v => v = bank dest p q)
      (fun v => v = bank (putWord dest q (BlockNegationData.negate blocks).flatten)
        (p+((M*B : ℕ) : ℤ)) (q+((M*B : ℕ) : ℤ))) (210*(M*B)+219) := by
  intro blocks bits bank
  have count : blocks.length = M := FiberLayoutData.fiber_length word i
  have uniform : BlockRotationData.Uniform B blocks := FiberLayoutData.fiber_uniform word i
  have volume := BlockRotationData.uniform_volume B blocks uniform
  unfold bank
  cases eq : blocks with
  | nil => simp [eq] at count; omega
  | cons x xs =>
    rw [eq] at count uniform volume
    have tailCount : xs.length = M-1 := by simp at count; omega
    have tailUniform : BlockRotationData.Uniform B xs := fun y hy => uniform y (List.mem_cons_of_mem _ hy)
    have tailLength := BlockRotationData.uniform_volume B xs tailUniform
    rw [tailCount] at tailLength
    rw [count] at volume
    have value (n : ℕ) : Counter.value (bits n) = n :=
      Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self n)
    have run := BlockNegationReuse.negate_hoare_linear source dest scratch p q r x xs B
      (uniform x (by simp)) tailUniform hB (bits B) (bits ((M-1)*B)) (bits (M-1))
      (value B) (tailCount ▸ value _) (tailCount ▸ value _)
      (Mult.PhaseCellToeplitz.binBits_size_canonical _) (Mult.PhaseCellToeplitz.binBits_size_canonical _)
      (Mult.PhaseCellToeplitz.binBits_size_canonical _) (by simpa only [tailLength] using clean)
    simpa only [volume] using run

/-- One counted pass negates the leading coordinate in every prefix fiber. -/
theorem negateLeafStream_hoare {P M B : ℕ} (hM : 0 < M) (hB : 0 < B)
    (word : Fin (P*(M*B)) → Fin 4) (source dest scratch clock : ℤ → Fin 4) (p q r : ℤ)
    (clean : ∀ z, r ≤ z → z < r+(((M-1)*B : ℕ) : ℤ) → scratch z = blank)
    (marker : clock 0 = separator) (stop : clock (1+(Host.binBits P.size P).length) = blank) :
    let bits := fun n : ℕ => Host.binBits n.size n
    let rows := List.ofFn (fun i : Fin P => (BlockNegationData.negate (FiberLayoutData.fiber word i)).flatten)
    let bank := fun out x y => BlockNegationReuse.bank (putWord source p (List.ofFn word)) out scratch
      (bits B) (bits ((M-1)*B)) (bits (M-1)) x y r
    HoareTime (CountedLoop.program BlockNegationReuse.program)
      (fun v => v = CountedLoop.bank (bank dest p q) clock (bits P))
      (fun v => v = CountedLoop.bank (bank (putWord dest q rows.flatten)
        (p+((P*(M*B) : ℕ) : ℤ)) (q+((P*(M*B) : ℕ) : ℤ))) clock (List.replicate (bits P).length true))
      (P*(210*(M*B)+219)+6*P+2*(bits P).length+2) := by
  intro bits rows bank
  let L := M*B
  let state := fun i : ℕ => bank (putWord dest q (rows.take i).flatten)
    (p+((i*L : ℕ) : ℤ)) (q+((i*L : ℕ) : ℤ))
  have width (i : Fin P) : (FiberLayoutData.fiber word i).flatten.length = L := by
    rw [BlockRotationData.uniform_volume B _ (FiberLayoutData.fiber_uniform word i),FiberLayoutData.fiber_length]
  have rowLength : rows.length = P := List.length_ofFn
  have body (i : ℕ) (hi : i < P) : HoareTime BlockNegationReuse.program
      (fun v => v = state i) (fun v => v = state (i+1)) (210*L+219) := by
    let j : Fin P := ⟨i,hi⟩
    let input := (FiberLayoutData.fibers word).map List.flatten
    have size : input.length = P := by simp [input,FiberLayoutData.fibers]
    have src := FiberShift.source_fiber source p input L i (by
      intro x hx
      obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hx
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hf
      exact width k) (size ▸ hi)
    rw [show input.flatten = List.ofFn word from FiberLayoutData.flatten_fibers word] at src
    simp only [input,List.getElem_map,FiberLayoutData.fibers,List.getElem_ofFn] at src
    have run := negateLeafFiber_hoare hM hB word j (putWord source p (List.ofFn word))
      (putWord dest q (rows.take i).flatten) scratch (p+((i*L : ℕ) : ℤ)) (q+((i*L : ℕ) : ℤ)) r clean
    dsimp only at run
    rw [src] at run
    have len : (rows.take i).flatten.length = i*L := by
      rw [BlockRotationData.uniform_volume L _ (by
        intro x hx
        obtain ⟨k,rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hx)
        simpa only [BlockNegationData.payload_length] using width k),
        List.length_take,rowLength,Nat.min_eq_left hi.le]
    have appendRow := putWord_append_forward dest q (rows.take i).flatten (rows[i]'(rowLength ▸ hi))
    rw [len] at appendRow
    have advance : putWord (putWord dest q (rows.take i).flatten) (q+((i*L : ℕ) : ℤ))
        (BlockNegationData.negate (FiberLayoutData.fiber word j)).flatten =
        putWord dest q (rows.take (i+1)).flatten := by
      rw [List.take_succ_eq_append_getElem (rowLength ▸ hi),List.flatten_append]
      simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,rows,List.getElem_ofFn,j] using appendRow
    rw [advance] at run
    simpa only [state,bank,Nat.add_mul,one_mul,Nat.cast_add,← add_assoc,L,bits] using run
  have loop := CountedLoop.loop_hoare BlockNegationReuse.program clock (bits P) P state
    (fun _ => 210*L+219) (Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self P)) marker stop body
  have allRows : rows.take P = rows := rowLength ▸ List.take_length
  simpa [state,L,allRows,putWord] using loop

private theorem negateLeafHead_map {α β : Type*} {P M B : ℕ} (f : α → β)
    (word : Fin (P*(M*B)) → α) :
    negateLeafHead (P := P) (M := M) (B := B) (f ∘ word) = (negateLeafHead word).map f := by
  have mapped (blocks : List (List α)) :
      BlockNegationData.negate (blocks.map (List.map f)) = (BlockNegationData.negate blocks).map (List.map f) := by
    cases blocks <;> simp [BlockNegationData.negate,List.map_reverse]
  unfold negateLeafHead
  rw [List.map_flatten,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  change _ = ((BlockNegationData.negate (FiberLayoutData.fiber word i)).flatten).map f
  rw [List.map_flatten,← mapped]
  simp only [FiberLayoutData.fiber,List.map_ofFn,Function.comp_def]

open Host in
theorem negateLeafStream_exec {P M B A : ℕ} {U F : Type} (hM : 0 < M) (hB : 0 < B)
    (word : Fin (P*(M*B)) → ZMod 2) (clock : ℤ → Fin 4)
    (marker : clock 0 = separator) (stop : clock (1+(binBits P.size P).length) = blank)
    (body : F → Pr F 9 207 A U) (u : HS 9 207 A U) (S : Stacks 9 A) :
    let bits := fun n : ℕ => binBits n.size n
    let enc := RadixToBinary.binaryEncoding (q := A)
    let source := putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ word))
    let bank := fun out x y => BlockNegationReuse.bank source out (fun _ => blank)
      (bits B) (bits ((M-1)*B)) (bits (M-1)) x y 0
    let cost := P*(210*(M*B)+219)+6*P+2*(bits P).length+2
    RepT (Alphabet.mapTapes enc (CountedLoop.bank (bank (fun _ => blank) 0 0) clock (bits P))) S.L S.R →
    ∃ z D n, z.user = u.user ∧ n ≤ cost*14+6 ∧
      Exec body (foreign (Alphabet.program enc (CountedLoop.program BlockNegationReuse.program))) (mk u S) n (mk z D) ∧
      ∀ x, readAt blank (D.L 1) (D.R 1) (x-((P*(M*B) : ℕ) : ℤ)) =
        enc.encode (putWord (fun _ => blank) 0 ((negateLeafHead word).map SparseRoleCircuit.encode) x) := by
  intro bits enc source bank cost rep
  let N := P*(M*B)
  let out : ℤ → Fin 4 := putWord (fun _ => blank) 0 ((negateLeafHead word).map SparseRoleCircuit.encode)
  let finish := CountedLoop.bank (bank out (N : ℤ) (N : ℤ)) clock (List.replicate (bits P).length true)
  have native := negateLeafStream_hoare hM hB (SparseRoleCircuit.encode ∘ word) (fun _ => blank)
    (fun _ => blank) (fun _ => blank) clock 0 0 0 (fun _ _ _ => rfl) marker stop
  change HoareTime _ _ (fun v => v = CountedLoop.bank (bank (putWord _ 0 (negateLeafHead
    (P := P) (M := M) (B := B) (SparseRoleCircuit.encode ∘ word))) (0+(N : ℤ)) (0+(N : ℤ))) clock _) cost at native
  simp only [negateLeafHead_map,zero_add (N : ℤ)] at native
  have run : HoareTime (Alphabet.program enc (CountedLoop.program BlockNegationReuse.program)) (· = Alphabet.mapTapes enc (CountedLoop.bank (bank (fun _ => blank) 0 0) clock (bits P)))
      (· = Alphabet.mapTapes enc finish) cost := by
    apply (Alphabet.map_hoare enc native).consequence _ _ le_rfl
    · rintro _ rfl; exact ⟨_,rfl,rfl⟩
    · rintro _ ⟨_,rfl,rfl⟩; rfl
  obtain ⟨z,D,_,rfl,result,hu,_,_,_,n,hn,exec⟩ := foreign_exec body _ run u S _ rfl rep
  refine ⟨z,D,n,hu,hn,exec,fun x => ?_⟩
  exact (result 1 x).symm

end IntegerMultBounds.MathlibTM2.Cover.Fallback
