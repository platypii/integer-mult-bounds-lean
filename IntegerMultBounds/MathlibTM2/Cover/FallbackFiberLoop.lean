module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberStep
public import IntegerMultBounds.Machine.TranslationPreparedFamily
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! A single counted program rotates all control fibers of a modular row addition. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host TranslationExecutionReuse
open TranslationStream (blocks fibers)
open TranslationPreparedFamily (outputPrefix)
open Mult.PhaseCellToeplitz (countedLoop countedLoop_exec)
variable {T A : ℕ} {P U : Type}

/-- At boundary x the destination contains exactly the first x rotated fibers. -/
def shearBank (M B c : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (payload : ℕ → ℕ → List (Fin 4)) (bs ms : List Bool) (x : ℕ) :=
  bank (putWord source p (fibers M M payload).flatten)
    (putWord dest q (outputPrefix (fun i => c*i % M) M x payload))
    (p+((x*(M*B) : ℕ) : ℤ)) (q+((x*(M*B) : ℕ) : ℤ)) bs ms []

/-- The full destination prefix sends (x,y,j) to (x,y+c*x,j) modulo M. -/
theorem shear_entry (c M B : ℕ) (payload : ℕ → ℕ → List (Fin 4))
    (hw : ∀ i y, (payload i y).length = B) (x y : Fin M) (j : Fin B) :
    (outputPrefix (fun i => c*i % M) M M payload)[x.val*(M*B)+(((y.val+c*x.val)%M)*B+j.val)]? =
      (payload x.val y.val)[j.val]? := by
  let row := fun i => (BlockRotationData.rotate (c*i % M) (blocks M (payload i))).flatten
  have width : BlockRotationData.Uniform (M*B) ((List.range M).map row) := by
    intro w h
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    unfold row
    rw [BlockRotationData.rotated_volume _ B _ (TranslationPreparedFamily.blocks_uniform M B i payload hw)]
    simp [blocks]
  have hy := Nat.mod_lt (y.val+c*x.val) (Nat.zero_lt_of_lt y.isLt)
  change ((List.range M).map row).flatten[_]? = _
  rw [BlockRotationData.flatten_index (M*B) _ width x.val _ (by simp)
    (by nlinarith [Nat.mul_le_mul_right B (Nat.succ_le_of_lt hy),j.isLt])]
  have uniform := TranslationPreparedFamily.blocks_uniform M B x.val payload hw
  have move := BlockRotationData.payload_destination (c*x.val % M) B _ uniform y.val j.val
    (by simp [blocks]) j.isLt
  rw [BlockRotationData.flatten_index B _ uniform y.val j.val (by simp [blocks]) j.isLt] at move
  simpa [row,blocks,Nat.add_mod_mod] using move

theorem fiberLoop_exec (body : P → Pr P T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (count : Fin T) (hr : ∀ i, r i ≠ count) (ht : ∀ i, call i ≠ count)
    (L c M B : ℕ) (hc : c < M) (hM : M < 2^L) (hB : 0 < B)
    (v : HS T 217 A U) (S : Stacks T A) (ready : FiberReady r L c 0 M S)
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → List (Fin 4))
    (hw : ∀ i y, (payload i y).length = B) (bs ms : List Bool)
    (hb : Counter.value bs = B) (hm : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (ticks : (S.R count).length = M)
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (shearBank M B c source dest p q payload bs ms 0)) (S.L ∘ call) (S.R ∘ call)) :
    ∃ z F n, z.user = v.user ∧ n ≤ M*(48*L*L+162*L+93+(207*(M*B)+241)*25)+2 ∧
      Exec body (countedLoop count (fiberStep r call)) (mk v S) n (mk z F) ∧
      F.R count = [] ∧ FiberReady r L c M M F ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (shearBank M B c source dest p q payload bs ms M)) (F.L ∘ call) (F.R ∘ call) := by
  let W := shearBank M B c source dest p q payload bs ms
  let Inv (i : ℕ) (D : Stacks T A) := FiberReady r L c i M D ∧
    RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (W i)) (D.L ∘ call) (D.R ∘ call)
  let cost := 48*L*L+162*L+90+(207*(M*B)+241)*25
  have run := countedLoop_exec (body := body) count (fiberStep r call) M cost Inv
  have stable : ∀ i D xs, Inv i D → Inv i {D with R := Function.update D.R count xs} := by
    rintro i D xs ⟨h,rep⟩
    refine ⟨⟨?_,?_,?_,?_,h.marker⟩,?_⟩
    · simpa [Function.update_of_ne (hr 0)] using h.coef
    · simpa [Function.update_of_ne (hr 1)] using h.digit
    · simpa [Function.update_of_ne (hr 2)] using h.modulus
    · intro j hj hk; simpa [Function.update_of_ne (hr j)] using h.empty j hj hk
    · intro j k; simpa [Function.comp_apply,Function.update_of_ne (ht j)] using rep j k
  rw [← show cost+3 = 48*L*L+162*L+93+(207*(M*B)+241)*25 by dsimp [cost]; omega]
  apply run stable _ v S ticks ⟨ready,rep⟩
  intro i hi u D h
  let src := putWord source p (fibers M M payload).flatten
  let off := fun i => c*i % M
  let dst := putWord dest q (outputPrefix off M i payload)
  let atHead := fun (k : ℤ) => k+((i*(M*B) : ℕ) : ℤ)
  have hs := TranslationPreparedFamily.source_fiber M B M i source p payload hw hi
  have heq : input src dst (atHead p) (atHead q) (blocks M (payload i)) bs ms [] = W i := by
    simp only [TranslationExecutionReuse.input,src,atHead,hs,W,shearBank,dst,off]
  obtain ⟨z,F,n,he,hn,hnext,hu,_,_,frame,hrp⟩ := fiberStep_exec body r call slot outside
    L c i M B hc hi hM hB u D h.1 src dst (atHead p) (atHead q) (blocks M (payload i)) bs ms
    (by simp [blocks]) (TranslationPreparedFamily.blocks_uniform M B i payload hw)
    hb hm cb cm (heq.symm ▸ h.2)
  refine ⟨z,F,n,hu,hn,he,(frame count ht (hr 1).symm).2,hnext,?_⟩
  have hout : putWord dst (atHead q) (BlockRotationData.rotate (off i) (blocks M (payload i))).flatten =
      putWord dest q (outputPrefix off M (i+1) payload) := by
    unfold dst atHead
    rw [← TranslationPreparedFamily.prefix_length off M B i payload hw,putWord_append_forward,
      TranslationPreparedFamily.prefix_succ]
  have pos (k : ℤ) : atHead k + (M : ℤ)*B = k+(((i+1)*(M*B) : ℕ) : ℤ) := by
    dsimp [atHead]; ring
  have outEq : output M (off i) B src dst (atHead p) (atHead q) (blocks M (payload i)) bs ms [] = W (i+1) := by
    unfold output
    rw [hout,pos,pos]
    simp only [src,atHead,hs,W,shearBank,off]
  exact outEq ▸ hrp

/-- Derive both loop controls from the modulus before visiting the fibers. -/
def shearProgram (r : Fin 13 ↪ Fin T) (call : Fin 12 ↪ Fin T) (count : Fin T) : Pr P T 217 A U :=
  .seq (toUnary (r 2) count (r 4) (r 5) (r 6))
    (.seq (bzero (r 2) (r 1) (r 4)) (countedLoop count (fiberStep r call)))

theorem shear_exec (body : P → Pr P T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (count : Fin T) (hr : ∀ i, r i ≠ count) (ht : ∀ i, call i ≠ count)
    (L c M B : ℕ) (hc : c < M) (hM : M < 2^L) (hB : 0 < B)
    (v : HS T 217 A U) (S : Stacks T A) (coef : S.R (r 0) = binSyms L c)
    (modulus : S.R (r 2) = binSyms L M) (digit : S.R (r 1) = [])
    (scratch : ∀ i : Fin 13, 3 ≤ i → i < 12 → S.R (r i) = [])
    (marker : S.L (r 3) = [separator])
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → List (Fin 4))
    (hw : ∀ i y, (payload i y).length = B) (bs ms : List Bool)
    (hb : Counter.value bs = B) (hm : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (empty : S.R count = [])
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (shearBank M B c source dest p q payload bs ms 0)) (S.L ∘ call) (S.R ∘ call)) :
    ∃ z F n, z.user = v.user ∧ n ≤ 6*M+15*L+10 + M*(48*L*L+162*L+93+(207*(M*B)+241)*25)+2 ∧
      Exec body (shearProgram r call count) (mk v S) n (mk z F) ∧
      F.R count = [] ∧ FiberReady r L c M M F ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (shearBank M B c source dest p q payload bs ms M)) (F.L ∘ call) (F.R ∘ call) := by
  have sep (i : Fin 13) : count ≠ r i := (hr i).symm
  obtain ⟨u,k,hu,hk,init⟩ := toUnary_exec_linear body (a := r 2) (z := count)
    (w := r 4) (t := r 5) (t₂ := r 6) (by simp [List.nodup_cons,r.injective.eq_iff,hr,sep])
    hM v S modulus (scratch 4 (by decide) (by decide)) (scratch 5 (by decide) (by decide))
    (scratch 6 (by decide) (by decide))
  rw [empty,List.append_nil] at init
  let D : Stacks T A := {S with R := Function.update S.R count (List.replicate M Node.tick)}
  obtain ⟨u',hu',zero⟩ := bzero_exec body (wR := r 2) (c := r 1) (t := r 4)
    (by simp [List.nodup_cons,r.injective.eq_iff]) u D
    (by simpa [D,Function.update_of_ne (hr 4)] using scratch 4 (by decide) (by decide))
  have width : (D.R (r 2)).length = L := by simp [D,Function.update_of_ne (hr 2),modulus,length_binSyms]
  have free : D.R (r 1) = [] := by simpa [D,Function.update_of_ne (hr 1)] using digit
  rw [width,free,List.append_nil] at zero
  let E : Stacks T A := {D with R := Function.update D.R (r 1) (binSyms L 0)}
  have ready : FiberReady r L c 0 M E := by
    constructor
    · simp [E,D,r.injective.eq_iff,Function.update_of_ne (hr 0),coef]
    · simp [E]
    · simp [E,D,r.injective.eq_iff,Function.update_of_ne (hr 2),modulus]
    · intro i hi hj
      simp [E,D,Function.update_of_ne (r.injective.ne (show i ≠ 1 by omega)),Function.update_of_ne (hr i),scratch i hi hj]
    · exact marker
  obtain ⟨z,F,n,hz,hn,run,rest,hready,final⟩ := fiberLoop_exec body r call slot outside count hr ht
    L c M B hc hM hB u' E ready source dest p q payload hw bs ms hb hm cb cm
    (by simp [E,D,Function.update_of_ne (sep 1)])
    (by intro i j; simpa [E,D,Function.comp_apply,Function.update_of_ne (ht i),
          Function.update_of_ne (outside 1 (by decide) i)] using rep i j)
  exact ⟨z,F,_,hz.trans (hu'.trans hu),by omega,Exec.seq init (Exec.seq zero run),rest,hready,final⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
