module

public import IntegerMultBounds.MathlibTM2.Host.StatePlacement
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
      (∀ x, readAt blank (D.L 0) (D.R 0) (x-((P*(M*B) : ℕ) : ℤ)) = enc.encode (source x)) ∧
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
  refine ⟨z,D,n,hu,hn,exec,fun x => (result 0 x).symm,fun x => ?_⟩
  exact (result 1 x).symm

open Host IntegerMultBounds.Networks.Shared50ModularControl in
theorem initializedNegateLeaf_exec {P M B : ℕ} {U F : Type} (hM : 0 < M) (hB : 0 < B)
    (word : Fin (P*(M*B)) → ZMod 2) (body : F → Pr F 9 207 prime U)
    (u : HS 9 207 prime U) (S : Stacks 9 prime)
    (payload : ∀ x, readAt blank (S.L 0) (S.R 0) x = leafBitTape (List.ofFn word) x)
    (left : ∀ i : Fin 9, i ≠ 0 → S.L i = [])
    (right : ∀ i : Fin 9, i ≠ 0 → S.R i =
      if i = 4 then binSyms B.size B else if i = 5 then binSyms ((M-1)*B).size ((M-1)*B)
      else if i = 7 then binSyms (M-1).size (M-1) else if i = 8 then binSyms P.size P else []) :
    let marks : List (Fin 9) := [3,4,5,6,7,8]
    let prog := foreign (Alphabet.program RadixToBinary.binaryEncoding (CountedLoop.program BlockNegationReuse.program))
    ∃ z D n, z.user = u.user ∧ n ≤ 1+(P*(210*(M*B)+219)+6*P+2*P.size+2)*14+6 ∧
      Exec body (.seq (.act (pushMarkers marks)) prog) (mk u S) n (mk z D) ∧
      (∀ x, readAt blank (D.L 0) (D.R 0) (x-((P*(M*B) : ℕ) : ℤ)) = leafBitTape (List.ofFn word) x) ∧
      ∀ x, readAt blank (D.L 1) (D.R 1) (x-((P*(M*B) : ℕ) : ℤ)) = leafBitTape (negateLeafHead word) x := by
  intro marks prog
  let H : Stacks 9 prime := {S with L := fun i => if i ∈ marks then separator :: S.L i else S.L i}
  have setup := Exec.act (body := body) (pushMarkers marks) (mk u S)
  rw [pushMarkers_run _ (by decide)] at setup
  obtain ⟨z,D,n,hu,hn,run,src,out⟩ := negateLeafStream_exec hM hB word CountedCopyReuse.empty
    (by simp [CountedCopyReuse.empty]) (by simp [CountedCopyReuse.empty]; omega) body u H (by
      intro i k
      have header (xs : List Bool) : RadixZeroFill.encodedBinary (q := prime) xs k =
          readAt blank [separator] (xs.map bitSymbol) (k-1) := by rw [encodedBinary_eq,readAt_single]
      have empty : (blank : Fin (prime+4)) = readAt blank [] [] (k-0) := by rw [readAt_nil_left,wordTape_nil]
      fin_cases i <;> simp [H,marks,left,right,binSyms_eq] <;>
        first | exact header [] | exact header _ | exact empty | change RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ word)) k) = readAt blank (S.L 0) (S.R 0) (k-0); simpa only [leafBitTape,List.map_ofFn,sub_zero] using (payload k).symm)
  refine ⟨z,D,1+n,hu,?_,Exec.seq setup run,?_,out⟩
  · rw [length_binBits] at hn
    omega
  · simpa only [leafBitTape,List.map_ofFn] using src

open Host IntegerMultBounds.Networks.Shared50ModularControl in
theorem returnLeafBits_exec {P M B T : ℕ} {F U : Type} (hP : 0 < P) (hM : 0 < M) (hB : 0 < B)
    (body : F → Pr F T 217 prime U) (r : Fin 8 ↪ Fin T) (v : HS T 217 prime U) (S : Stacks T prime)
    (a xs : List (ZMod 2)) (ha : a.length = P*(M*B)) (hx : xs.length = P*(M*B))
    (dst : ∀ z, readAt blank (S.L (r 0)) (S.R (r 0)) (z-((P*(M*B) : ℕ) : ℤ)) = leafBitTape xs z)
    (src : ∀ z, readAt blank (S.L (r 1)) (S.R (r 1)) (z-((P*(M*B) : ℕ) : ℤ)) = leafBitTape a z)
    (controls : ∀ (i : Fin 6) z, CountedLoopReuseAlphabet.binary
      (![[],binBits B.size B,[],binBits M.size M,[],binBits P.size P] i) z =
      readAt blank (S.L (r (Fin.natAdd 2 i))) (S.R (r (Fin.natAdd 2 i))) (z-1)) :
    ∃ u D n, u.user = v.user ∧ n ≤ (327*(P*(M*B))+2)*13+6 ∧
      Exec body (returnWord r) (mk v S) n (mk u D) ∧
      (∀ z, readAt blank (D.L (r 1)) (D.R (r 1)) z = leafBitTape xs z) ∧
      ∀ j, (∀ i, r i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  let encoded := fun ys : List (ZMod 2) => (ys.map (SparseRoleCircuit.encode (a := 0))).map
    (RadixToBinary.binaryEncoding (q := prime)).encode
  have tape (ys : List (ZMod 2)) : leafBitTape ys = putWord (fun _ => blank) 0 (encoded ys) := by
    change RowPaddingConstructedAlphabet.mapTape (putWord (fun _ => blank) 0 _) = _
    rw [RowPaddingConstructedAlphabet.map_putWord]
    rfl
  have ready := returnWord_ready r S _ _ _ _ _ _ _ dst src controls
  rw [tape xs,tape a] at ready
  obtain ⟨u,D,n,hu,hn,run,rep,off⟩ := returnPackedList_exec body r rfl hP hM hB
    (fun _ => blank) (fun _ => blank) 0 0 (encoded a) (encoded xs) (by simpa [encoded] using ha)
    (by simpa [encoded] using hx) _ _ _
    (Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self _))
    (Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self _))
    (Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self _))
    (Mult.PhaseCellToeplitz.binBits_size_canonical _) (Mult.PhaseCellToeplitz.binBits_size_canonical _)
    (Mult.PhaseCellToeplitz.binBits_size_canonical _) (fun _ _ _ => rfl) v S (by simpa only [zero_add] using ready)
  refine ⟨u,D,n,hu,hn,run,?_,off⟩
  intro z
  rw [tape]
  have read := (rep 1 z).symm
  change readAt blank (D.L (r 1)) (D.R (r 1)) (z-0) = putWord (fun _ => blank) 0 (encoded xs) z at read
  simpa only [sub_zero] using read

def negationReturnPorts : Fin 8 ↪ Fin 15 := ⟨![1,0,9,10,11,12,13,14], by decide⟩

open Host IntegerMultBounds.Networks.Shared50ModularControl in
theorem negateAndReturn_exec {P M B : ℕ} {F U : Type} (hP : 0 < P) (hM : 0 < M) (hB : 0 < B)
    (word : Fin (P*(M*B)) → ZMod 2) (body : F → Pr F 15 217 prime U)
    (u : HS 15 217 prime U) (S : Stacks 15 prime)
    (payload : ∀ x, readAt blank (S.L 0) (S.R 0) x = leafBitTape (List.ofFn word) x)
    (left : ∀ i : Fin 9, i ≠ 0 → S.L (i.castAdd 6) = [])
    (right : ∀ i : Fin 9, i ≠ 0 → S.R (i.castAdd 6) =
      if i = 4 then binSyms B.size B else if i = 5 then binSyms ((M-1)*B).size ((M-1)*B)
      else if i = 7 then binSyms (M-1).size (M-1) else if i = 8 then binSyms P.size P else [])
    (returnLeft : ∀ i : Fin 6, S.L (i.natAdd 9) = [])
    (returnRight : ∀ i : Fin 6, S.R (i.natAdd 9) =
      (![[],binSyms B.size B,[],binSyms M.size M,[],binSyms P.size P] i)) :
    let marks := (List.finRange 6).map (Fin.natAddEmb 9)
    let bank := Fin.castAddEmb (n := 9) 6
    let child : Pr Empty 9 207 prime U := .seq (.act (pushMarkers [3,4,5,6,7,8]))
      (foreign (Alphabet.program RadixToBinary.binaryEncoding (CountedLoop.program BlockNegationReuse.program)))
    let sign := statePlacedNormalized bank (by decide : 207 ≤ 217) (by decide) Empty.elim child
    let N := P*(M*B)
    ∃ z D n, z.user = u.user ∧ n ≤ 2+(1+(P*(210*(M*B)+219)+6*P+2*P.size+2)*14+6)+((327*N+2)*13+6) ∧
      Exec body (.seq (.act (pushMarkers marks)) (sign.seq (returnWord negationReturnPorts))) (mk u S) n (mk z D) ∧
      ∀ x, readAt blank (D.L 0) (D.R 0) x = leafBitTape (negateLeafHead word) x := by
  intro marks bank child sign N
  let I : Stacks 15 prime := {S with L := fun j => if j ∈ marks then separator :: S.L j else S.L j}
  have mark := Exec.act (body := body) (pushMarkers marks) (mk u S)
  rw [pushMarkers_run _ ((List.nodup_finRange 6).map (Fin.natAddEmb 9).injective)] at mark
  have keep (i : Fin 9) : I.L (i.castAdd 6) = S.L (i.castAdd 6) := by
    have off := (by decide : ∀ j : Fin 9, j.castAdd 6 ∉ (List.finRange 6).map (Fin.natAddEmb 9)) i
    simp [I,marks,off]
  have controls (i : Fin 6) (z : ℤ) : CountedLoopReuseAlphabet.binary
      (![[],binBits B.size B,[],binBits M.size M,[],binBits P.size P] i) z =
      readAt blank (I.L (i.natAdd 9)) (I.R (i.natAdd 9)) (z-1) := by
    have on := (by decide : ∀ j : Fin 6, j.natAdd 9 ∈ (List.finRange 6).map (Fin.natAddEmb 9)) i
    simp only [I,marks,ite_eq_left on,returnLeft,returnRight]
    fin_cases i <;> rw [← CountedLoopReuseAlphabet.encoding_binary] <;>
      change RadixZeroFill.encodedBinary _ z = _ <;> rw [encodedBinary_eq,readAt_single] <;> simp only [binSyms_eq] <;> rfl
  obtain ⟨a,H,n,ha,hn,run,src,dst⟩ := initializedNegateLeaf_exec hM hB word (F := Empty) Empty.elim
    (stateLiftDown (by decide : 0 < 207) (embDn bank u)) (embStk bank I) (by
      intro x
      change readAt blank (I.L ((0 : Fin 9).castAdd 6)) _ _ = _
      rw [keep]; exact payload x) (fun i hi => (keep i).trans (left i hi)) right
  obtain ⟨b,_,hb,placed⟩ := statePlaced_exec_normalized bank bank.injective (by decide : 207 ≤ 217)
    (by decide) Empty.elim (body' := body) (fun e => nomatch e) u I run
  let J := embOvr bank H.get I
  have eq : embStk bank J = H := embStk_ovr bank.injective _ _
  rw [← eq] at src dst
  have length : (negateLeafHead word).length = N := by
    unfold negateLeafHead
    rw [BlockRotationData.uniform_volume (M*B) _ (by
      intro xs hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      rw [BlockNegationData.payload_length,BlockRotationData.uniform_volume B _ (FiberLayoutData.fiber_uniform word i),
        FiberLayoutData.fiber_length]),List.length_ofFn]
  obtain ⟨z,D,m,hz,hm,ret,out,_⟩ := returnLeafBits_exec hP hM hB body negationReturnPorts b J
    (List.ofFn word) (negateLeafHead word) List.length_ofFn length dst src (by
      intro i x
      have same := embOvr_off H.get I (j := i.natAdd 9) (e := bank)
        (by intro j; exact (by decide : ∀ (k : Fin 9) (l : Fin 6), k.castAdd 6 ≠ l.natAdd 9) j i)
      have port : negationReturnPorts (Fin.natAdd 2 i) = i.natAdd 9 := (by decide : ∀ j, negationReturnPorts (Fin.natAdd 2 j) = j.natAdd 9) i
      rw [port,same.1,same.2]
      exact controls i x)
  refine ⟨z,D,_,hz.trans (hb.trans ha),?_,Exec.seq mark (Exec.seq placed ret),out⟩
  omega

end IntegerMultBounds.MathlibTM2.Cover.Fallback
