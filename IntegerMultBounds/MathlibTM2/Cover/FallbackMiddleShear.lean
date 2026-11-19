module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixShear
import IntegerMultBounds.Machine.FlatControlledShift
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet
public import IntegerMultBounds.MathlibTM2.Cover.FallbackReturnWord
import IntegerMultBounds.Machine.BinaryDivide
import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixVolume

/-! Shear two equal-radix atoms across an arbitrary inherited middle. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T A M G B P : ℕ} {U F : Type}

/-- The control digit is just above the mixed-radix middle in the prefix
counter. The offset therefore preserves every individual middle value. -/
theorem middleShear_entry (word : Fin ((P*M*G)*(M*B)) → Fin 4) (c : ℕ)
    (pre : Fin P) (h : Fin M) (mid : Fin G) (t : Fin M) (j : Fin B) :
    let row := finProdFinEquiv (finProdFinEquiv (pre,h),mid)
    let off := fun i => c*(i/G%M)%M
    (TranslationPreparedFamily.outputPrefix off M (P*M*G) (FlatControlledShift.payload word))[
      row.val*(M*B)+((t.val+c*h.val)%M)*B+j.val]? = some (word (FiberLayoutData.index row t j)) := by
  intro row off
  rw [FlatControlledShift.output_eq]
  have control : row.val/G%M = h.val := by
    simp [row,finProdFinEquiv, Nat.add_mul_div_left, Nat.div_eq_of_lt mid.isLt,
      Nat.zero_lt_of_lt mid.isLt, Nat.mod_eq_of_lt h.isLt]
  simpa only [off,control,Nat.add_mod_mod] using
    FiberLayoutData.translated_entry word (fun i => off i.val) row t j

/-- Execute with dimensions supplied as binary headers. Neither the program
nor its coefficient depends on a radix decomposition of the middle field. -/
theorem middleShear_exec (body : F → Pr F T 217 A U) (r : Fin 15 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 15, i ≠ 3 → ∀ j, call j ≠ r i)
    (count : Fin T) (hr : ∀ i, r i ≠ count) (ht : ∀ i, call i ≠ count)
    (L K H J c : ℕ) (fits : P*M*G < 2^L) (gapFits : G < 2^K) (gapPos : 0 < G)
    (coefFits : c < M) (modFits : M < 2^H) (suffixFits : B < 2^J) (suffixPos : 0 < B)
    (v : HS T 217 A U) (S : Stacks T A)
    (extent : S.R (r 1) = binSyms L (P*M*G)) (counter : S.R (r 13) = [])
    (gap : S.R (r 14) = binSyms K G) (coef : S.R (r 0) = binSyms H c)
    (modulus : S.R (r 2) = binSyms H M) (scratch : ∀ j : Fin 15, 3 ≤ j → j ≤ 12 → S.R (r j) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin ((P*M*G)*(M*B)) → Fin 4)
    (empty : S.R count = []) (left : ∀ i : Fin 12, i < 10 → S.L (call i) = [])
    (right : ∀ i : Fin 12, i < 10 → S.R (call i) = if i = 5 then binSyms J B else [])
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn word) z) =
      readAt blank (S.L (call 10)) (S.R (call 10)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (call 11)) (S.R (call 11)) (z-q)) :
    let N := P*M*G
    ∃ z D n, z.user = v.user ∧
      n ≤ 6*N+17*L+4*J+10*H+31 + N*(L*(12*(K+H)+78)+22*K+180*H+173+48*H*H+(207*(M*B)+241)*25)+2 ∧
      Exec body (prefixShear r call count) (mk v S) n (mk z D) ∧
      ∀ (pre : Fin P) (h : Fin M) (mid : Fin G) (t : Fin M) (j : Fin B),
        let row := finProdFinEquiv (finProdFinEquiv (pre,h),mid)
        let pos := row.val*(M*B)+((t.val+c*h.val)%M)*B+j.val
        readAt blank (D.L (call 11)) (D.R (call 11)) ((pos : ℤ)-(N*(M*B) : ℕ)) =
          RadixToBinary.binaryEncoding.encode (word (FiberLayoutData.index row t j)) := by
  intro N
  obtain ⟨bs,ms,z,D,n,_,_,_,_,user,time,run,_,_,rep⟩ := prefixShear_exec body r call slot outside count hr ht
    L K H J N G c M B suffixFits fits gapFits gapPos coefFits modFits suffixPos v S extent counter gap coef
    modulus scratch source dest p q (FlatControlledShift.payload word) (FlatControlledShift.payload_length _)
    empty left right (by simpa only [FlatControlledShift.source_eq] using src) dst
  refine ⟨z,D,n,user,time,run,?_⟩
  intro pre h mid t j row pos
  obtain ⟨inside,cell⟩ := List.getElem?_eq_some_iff.mp (middleShear_entry word c pre h mid t j)
  have read := rep 11 (q+pos)
  change RadixToBinary.binaryEncoding.encode (putWord dest q _ (q+pos)) =
    readAt blank (D.L (call 11)) (D.R (call 11)) ((q+pos)-(q+(N*(M*B) : ℕ))) at read
  rw [BinaryDivide.putWord_getElem dest q _ pos inside,cell] at read
  simpa only [add_sub_add_left_eq_sub] using read.symm

open TranslationExecutionReuse TranslationPreparedFamily
open TranslationStream (blocks fibers)
open Mult.PhaseCellToeplitz (countedLoop countedLoop_exec)

def MiddleGroupReady (r : Fin 13 ↪ Fin T) (H c h M : ℕ) (D : Stacks T A) : Prop :=
  D.R (r 0) = binSyms H c ∧ D.R (r 1) = binSyms H h ∧ D.R (r 2) = binSyms H M ∧
    (∀ j : Fin 13, 3 ≤ j → j < 12 → D.R (r j) = []) ∧ D.L (r 3) = [separator]

/-- For a fixed control digit all middle values use the same offset. Retain
that digit through the inner loop so the per-fiber time is independent of
the size of the middle counter. -/
theorem middleGroup_exec (body : F → Pr F T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (count : Fin T) (hr : ∀ i, r i ≠ count) (ht : ∀ i, call i ≠ count)
    (H c h : ℕ) (hc : c < M) (hh : h < M) (hm : M < 2^H) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → List (Fin 4))
    (hw : ∀ i y, (payload i y).length = B) (bs ms : List Bool)
    (hb : Counter.value bs = B) (hmod : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (v : HS T 217 A U) (S : Stacks T A) (ticks : (S.R count).length = G) :
    let off := fun _ : ℕ => c*h%M
    let bank := prefixBank G M B off source dest p q payload bs ms
    let ready := MiddleGroupReady r H c h M
    let inv := fun i D => ready D ∧ RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank i))
      (D.L ∘ call) (D.R ∘ call)
    inv 0 S → ∃ z D n, z.user = v.user ∧ n ≤ G*(48*H*H+158*H+85+(207*(M*B)+241)*25+3)+2 ∧
      Exec body (countedLoop count (fiberProgram r call)) (mk v S) n (mk z D) ∧ D.R count = [] ∧ inv G D ∧
      ∀ j, j ≠ count → (∀ i, call i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  intro off bank ready inv start
  let framed := fun i (D : Stacks T A) => inv i D ∧
    ∀ j, j ≠ count → (∀ i, call i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j
  apply countedLoop_exec (body := body) count (fiberProgram r call) G _ framed _ _ v S ticks
    ⟨start,fun _ _ _ => ⟨rfl,rfl⟩⟩
  · rintro i D xs ⟨⟨⟨c₀,h₀,m₀,free,mark⟩,rep⟩,frame⟩
    refine ⟨?_,fun j ne off => ?_⟩
    case refine_2 => simpa only [Function.update_of_ne ne] using frame j ne off
    refine ⟨⟨?_,?_,?_,?_,mark⟩,?_⟩
    · simpa [Function.update_of_ne (hr 0)] using c₀
    · simpa [Function.update_of_ne (hr 1)] using h₀
    · simpa [Function.update_of_ne (hr 2)] using m₀
    · intro j lo hi
      simpa [Function.update_of_ne (hr j)] using free j lo hi
    · intro j k
      simpa [Function.comp_apply,Function.update_of_ne (ht j)] using rep j k
  · rintro i hi u D ⟨⟨⟨c₀,h₀,m₀,free,mark⟩,rep⟩,prior⟩
    let src := putWord source p (fibers M G payload).flatten
    let dst := putWord dest q (outputPrefix off M i payload)
    let atHead := fun (k : ℤ) => k+((i*(M*B) : ℕ) : ℤ)
    have srcEq := source_fiber M B G i source p payload hw hi
    have eq : input src dst (atHead p) (atHead q) (blocks M (payload i)) bs ms [] = bank i := by
      simp only [TranslationExecutionReuse.input,src,dst,atHead,srcEq,bank,prefixBank]
    obtain ⟨z,E,n,marker,empty,run,cost,user,_,_,frame,next⟩ := fiberProgram_exec body r call slot H c h M
      hc hh hm u D c₀ h₀ m₀ free mark src dst (atHead p) (atHead q) (blocks M (payload i)) bs ms
      (eq.symm ▸ rep) B hB (by simp [blocks]) (blocks_uniform M B i payload hw) hb hmod cb cm
    have keep (j : Fin 13) (ne : j ≠ 3) := (frame _ (outside j ne)).2
    refine ⟨z,E,n,user,cost,run,(frame count ht).2,⟨⟨(keep 0 (by decide)).trans c₀,
      (keep 1 (by decide)).trans h₀,(keep 2 (by decide)).trans m₀,?_,slot ▸ marker⟩,?_⟩,fun j ne off =>
      ⟨(frame j off).1.trans (prior j ne off).1,(frame j off).2.trans (prior j ne off).2⟩⟩
    · intro j lo hi
      by_cases same : j = 3
      · simpa only [same,← slot] using empty
      exact (keep j same).trans (free j lo hi)
    · have out : putWord dst (atHead q) (BlockRotationData.rotate (off i) (blocks M (payload i))).flatten =
          putWord dest q (outputPrefix off M (i+1) payload) := by
        unfold dst atHead
        rw [← prefix_length off M B i payload hw,putWord_append_forward,prefix_succ]
      have pos (k : ℤ) : atHead k + (M : ℤ)*B = k+(((i+1)*(M*B) : ℕ) : ℤ) := by dsimp [atHead]; ring
      have eq' : output M (off i) B src dst (atHead p) (atHead q) (blocks M (payload i)) bs ms [] = bank (i+1) := by
        unfold output
        rw [out,pos,pos]
        simp only [src,atHead,srcEq,bank,prefixBank]
      exact eq' ▸ next

/-- Restore the group clock from its retained copy, scan one group, and
advance the control digit. The saved clock and other caller registers survive. -/
def middleGroupStep (r : Fin 13 ↪ Fin T) (call : Fin 12 ↪ Fin T) (saved count : Fin T) :
    Pr F T 217 A U :=
  .seq (bcopy saved count (r 4) (r 5))
    (.seq (countedLoop count (fiberProgram r call)) (countIter (r 1) (r 4) (r 12)))

theorem middleGroupStep_exec (body : F → Pr F T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (saved count : Fin T) (apart : saved ≠ count)
    (rs : ∀ i, r i ≠ saved) (rc : ∀ i, r i ≠ count)
    (ts : ∀ i, call i ≠ saved) (tc : ∀ i, call i ≠ count)
    (H c h : ℕ) (hc : c < M) (hh : h < M) (hm : M < 2^H) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → List (Fin 4))
    (hw : ∀ i y, (payload i y).length = B) (bs ms : List Bool)
    (hb : Counter.value bs = B) (hmod : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (v : HS T 217 A U) (S : Stacks T A) (ticks : (S.R saved).length = G) (empty : S.R count = [])
    (ready : MiddleGroupReady r H c h M S) :
    let bank := prefixBank G M B (fun _ => c*h%M) source dest p q payload bs ms
    RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank 0)) (S.L ∘ call) (S.R ∘ call) →
    ∃ z D n, z.user = v.user ∧
      n ≤ 6*G+6+(G*(48*H*H+158*H+85+(207*(M*B)+241)*25+3)+2)+(4*H+5) ∧
      Exec body (middleGroupStep r call saved count) (mk v S) n (mk z D) ∧
      MiddleGroupReady r H c (h+1) M D ∧ D.R saved = S.R saved ∧ D.R count = [] ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank G)) (D.L ∘ call) (D.R ∘ call) ∧
      ∀ j, j ≠ count → j ≠ r 1 → (∀ i, call i ≠ j) → D.R j = S.R j := by
  intro bank rep
  obtain ⟨u,hu,copy⟩ := bcopy_exec body (a := saved) (c := count) (t₁ := r 4) (t₂ := r 5)
    (by simp [List.nodup_cons,apart,Ne.symm (rs 4),Ne.symm (rs 5),Ne.symm (rc 4),Ne.symm (rc 5),r.injective.eq_iff])
    v S (ready.2.2.2.1 4 (by decide) (by decide)) (ready.2.2.2.1 5 (by decide) (by decide))
  let E := {S with R := Function.update S.R count (S.R saved ++ S.R count)}
  have keep (j : Fin T) (ne : j ≠ count) : E.R j = S.R j := Function.update_of_ne ne ..
  obtain ⟨y,F',m,hy,cost,run,done,⟨stable,placed⟩,frame⟩ := middleGroup_exec (G := G) body r call slot outside count rc tc
    H c h hc hh hm hB source dest p q payload hw bs ms hb hmod cb cm u E
    (by simp [E,empty,ticks]) (by
      refine ⟨⟨(keep _ (rc 0)).trans ready.1,(keep _ (rc 1)).trans ready.2.1,
        (keep _ (rc 2)).trans ready.2.2.1,fun j lo hi => (keep _ (rc j)).trans (ready.2.2.2.1 j lo hi),
        ready.2.2.2.2⟩,?_⟩
      intro i z
      simpa only [Function.comp_apply,keep _ (tc i)] using rep i z)
  obtain ⟨z,hz,inc⟩ := countIter_exec body (r.injective.ne (by decide : (1 : Fin 13) ≠ 4)) (r 12)
    y F' stable.2.1 (stable.2.2.2.1 4 (by decide) (by decide))
  rw [ticks] at copy
  refine ⟨z,_,_,hz.trans (hy.trans hu),by omega,.seq copy (.seq run inc),?_,?_,?_,?_,?_⟩
  · refine ⟨?_,Function.update_self ..,?_,?_,stable.2.2.2.2⟩
    · simpa [r.injective.eq_iff] using stable.1
    · simpa [r.injective.eq_iff] using stable.2.2.1
    · intro j lo hi
      simp only [Function.update_of_ne (r.injective.ne (by omega : j ≠ 1))]
      exact stable.2.2.2.1 j lo hi
  · simp only [Function.update_of_ne (rs 1).symm]
    exact (frame saved apart ts).2.trans (keep _ apart)
  · simpa [Function.update_of_ne (rc 1).symm] using done
  · intro i k
    simpa only [Function.comp_apply,Function.update_of_ne (outside 1 (by decide) i)] using placed i k
  · intro j ne digit off
    simp only [Function.update_of_ne digit]
    exact (frame j ne off).2.trans (keep j ne)

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime) in
/-- At binary modulus width a complete group, including its clock copy
and control increment, costs a constant per payload cell. -/
theorem middleGroupStep_volume_le (w G B : ℕ) (hG : 0 < G) (hB : 0 < B) :
    let M := prime^(w+1)
    let H := Nat.size M
    6*G+6+(G*(48*H*H+158*H+85+(207*(M*B)+241)*25+3)+2)+(4*H+5) ≤
      (210*(2*(Nat.size prime+1)^2)+11310)*(G*(M*B)) := by
  intro M H
  let c := 2*(Nat.size prime+1)^2
  have field := prefixSetup_volume_le w 0
  change (w+1+M^0)*(H+1)^2 ≤ c*M^(0+1) at field
  simp only [pow_zero,Nat.zero_add,pow_one] at field
  have square : (H+1)^2 ≤ c*(M*B) :=
    ((Nat.le_mul_of_pos_left _ (by omega)).trans field).trans
      (Nat.mul_le_mul_left c (Nat.le_mul_of_pos_right _ hB))
  have vol : 0 < M*B := Nat.mul_pos (pow_pos prime_prime.pos _) hB
  have perGroup : 6 + (48*H*H+158*H+85+(207*(M*B)+241)*25+3) + (13+4*H) ≤
      (210*c+11310)*(M*B) := by nlinarith only [square,vol,Nat.zero_le (H*H)]
  have extra := Nat.le_mul_of_pos_left (13+4*H) hG
  have total := Nat.mul_le_mul_left G perGroup
  change _ ≤ (210*c+11310)*(G*(M*B))
  nlinarith only [extra,total]

/-- Tape contents at the boundary between two successive control digits. -/
def middleSweepBank (M G B c : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (payload : ℕ → ℕ → ℕ → List (Fin 4)) (bs ms : List Bool) (i : ℕ) :=
  let input := (List.range M).flatMap (fun h => (fibers M G (payload h)).flatten)
  let output := (List.range i).flatMap (fun h => outputPrefix (fun _ => c*h%M) M G (payload h))
  let span := G*(M*B)
  TranslationExecutionReuse.bank (putWord source p input) (putWord dest q output)
    (p+((i*span : ℕ) : ℤ)) (q+((i*span : ℕ) : ℤ)) bs ms []

theorem middleSweepBank_group (source dest : ℤ → Fin 4) (p q : ℤ) (c : ℕ)
    (payload : ℕ → ℕ → ℕ → List (Fin 4)) (hw : ∀ h i y, (payload h i y).length = B)
    (bs ms : List Bool) (h : ℕ) (hh : h < M) :
    let span := G*(M*B)
    let rows := (List.range M).map (fun i => (fibers M G (payload i)).flatten)
    let writes := fun i => (List.range i).flatMap (fun j => outputPrefix (fun _ => c*j%M) M G (payload j))
    let localBank := prefixBank G M B (fun _ => c*h%M) (putWord source p rows.flatten)
      (putWord dest q (writes h)) (p+((h*span : ℕ) : ℤ)) (q+((h*span : ℕ) : ℤ)) (payload h) bs ms
    let sweep := middleSweepBank M G B c source dest p q payload bs ms
    localBank 0 = sweep h ∧ localBank G = sweep (h+1) := by
  intro span rows writes localBank sweep
  have uniform : BlockRotationData.Uniform span rows := by
    rintro _ hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact TranslationStream.source_length M B G _ (hw i)
  have sourceEq := FiberShift.source_fiber source p rows span h uniform (by simpa [rows] using hh)
  simp only [rows,List.getElem_map,List.getElem_range] at sourceEq
  have len : (writes h).length = h*span := by
    unfold writes
    rw [List.flatMap_def,BlockRotationData.uniform_volume span]
    · simp
    · rintro _ hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact prefix_length _ M B G _ (hw i)
  have dstEq : putWord (putWord dest q (writes h)) (q+((h*span : ℕ) : ℤ))
      (outputPrefix (fun _ => c*h%M) M G (payload h)) = putWord dest q (writes (h+1)) := by
    rw [← len,putWord_append_forward]
    simp [writes,List.range_succ]
  have pos (z : ℤ) : z+(h*span : ℕ)+(G*(M*B) : ℕ) = z+((h+1)*span : ℕ) := by dsimp [span]; ring
  constructor
  · simp only [localBank,prefixBank,rows,sourceEq,outputPrefix,List.range_zero,List.map_nil,
      List.flatten_nil,putWord,Nat.zero_mul,Nat.cast_zero,add_zero]
    rfl
  · simp only [localBank,prefixBank,rows,sourceEq,dstEq,pos]
    rfl

/-- Reset the exhausted control field to a zero of the same binary width. -/
def resetMiddleDigit (r : Fin 13 ↪ Fin T) : Pr F T 217 A U :=
  .seq (bclear (r 1)) (bzero (r 2) (r 1) (r 4))

theorem resetMiddleDigit_exec (body : F → Pr F T 217 A U) (r : Fin 13 ↪ Fin T)
    (v : HS T 217 A U) (S : Stacks T A) (H c M : ℕ) (ready : MiddleGroupReady r H c M M S) :
    ∃ z, z.user = v.user ∧ Exec body (resetMiddleDigit r) (mk v S) (6*H+6)
      (mk z {S with R := Function.update S.R (r 1) (binSyms H 0)}) := by
  obtain ⟨u,user,_,clear⟩ := bclear_exec body (r 1) v S
  let D := {S with R := Function.update S.R (r 1) []}
  obtain ⟨z,hz,zero⟩ := bzero_exec body (wR := r 2) (c := r 1) (t := r 4)
    (by simp [List.nodup_cons,r.injective.eq_iff]) u D
    (by simpa [D,r.injective.eq_iff] using ready.2.2.2.1 4 (by decide) (by decide))
  have len : (D.R (r 2)).length = H := by simp [D,r.injective.eq_iff,ready.2.2.1,length_binSyms]
  rw [len] at zero
  rw [ready.2.1,length_binSyms] at clear
  refine ⟨z,hz.trans user,?_⟩
  simpa [resetMiddleDigit,D,Function.update_idem,show 2*H+2+(4*H+4) = 6*H+6 by omega] using
    Exec.seq clear zero

def middleSweep (r : Fin 13 ↪ Fin T) (call : Fin 12 ↪ Fin T) (saved count clock : Fin T) :
    Pr F T 217 A U :=
  .seq (toUnary (r 2) clock (r 4) (r 5) (r 6))
    (.seq (countedLoop clock (middleGroupStep r call saved count)) (resetMiddleDigit r))

/-- Process all control digits of one prefix using a single execution on
the shared source and destination tapes. -/
theorem middleSweep_exec (body : F → Pr F T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (saved count clock : Fin T) (apart : saved ≠ count) (sc : saved ≠ clock) (cc : count ≠ clock)
    (rs : ∀ i, r i ≠ saved) (rc : ∀ i, r i ≠ count) (rk : ∀ i, r i ≠ clock)
    (ts : ∀ i, call i ≠ saved) (tc : ∀ i, call i ≠ count) (tk : ∀ i, call i ≠ clock)
    (H c : ℕ) (hc : c < M) (hm : M < 2^H) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → ℕ → List (Fin 4))
    (hw : ∀ h i y, (payload h i y).length = B) (bs ms : List Bool)
    (hb : Counter.value bs = B) (hmod : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (v : HS T 217 A U) (S : Stacks T A) (ticks : (S.R saved).length = G)
    (clockEmpty : S.R clock = []) (empty : S.R count = []) (ready : MiddleGroupReady r H c 0 M S) :
    let bank := middleSweepBank M G B c source dest p q payload bs ms
    let cost := 6*G+6+(G*(48*H*H+158*H+85+(207*(M*B)+241)*25+3)+2)+(4*H+5)
    RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank 0)) (S.L ∘ call) (S.R ∘ call) →
    ∃ z D n, z.user = v.user ∧ n ≤ (6*M+11*H+6)+(M*(cost+3)+2+(6*H+6)) ∧
      Exec body (middleSweep r call saved count clock) (mk v S) n (mk z D) ∧
      D.R clock = [] ∧ MiddleGroupReady r H c 0 M D ∧ D.R saved = S.R saved ∧ D.R count = [] ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank M)) (D.L ∘ call) (D.R ∘ call) ∧
      ∀ j, j ≠ clock → j ≠ count → j ≠ r 1 → (∀ i, call i ≠ j) → D.R j = S.R j := by
  intro bank cost rep
  let inv := fun i (D : Stacks T A) => MiddleGroupReady r H c i M D ∧ D.R saved = S.R saved ∧
    D.R count = [] ∧ RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank i)) (D.L ∘ call) (D.R ∘ call) ∧
    ∀ j, j ≠ clock → j ≠ count → j ≠ r 1 → (∀ i, call i ≠ j) → D.R j = S.R j
  obtain ⟨entry,setup,hu,price,prepare⟩ := toUnary_exec_linear body (a := r 2) (z := clock)
    (w := r 4) (t := r 5) (t₂ := r 6)
    (by simp [List.nodup_cons,rk,fun i => (rk i).symm,r.injective.eq_iff]) hm v S ready.2.2.1
    (ready.2.2.2.1 4 (by decide) (by decide)) (ready.2.2.2.1 5 (by decide) (by decide))
    (ready.2.2.2.1 6 (by decide) (by decide))
  let E := {S with R := Function.update S.R clock (List.replicate M Node.tick ++ S.R clock)}
  have groups : (E.R clock).length = M := by simp [E,clockEmpty]
  have initial : inv 0 E := by
    refine ⟨⟨?_,?_,?_,?_,ready.2.2.2.2⟩,?_,?_,?_,fun j ne _ _ _ => Function.update_of_ne ne ..⟩
    · simpa [E,Function.update_of_ne (rk 0)] using ready.1
    · simpa [E,Function.update_of_ne (rk 1)] using ready.2.1
    · simpa [E,Function.update_of_ne (rk 2)] using ready.2.2.1
    · intro j lo hi
      simpa [E,Function.update_of_ne (rk j)] using ready.2.2.2.1 j lo hi
    · simp [E,Function.update_of_ne sc]
    · simpa [E,Function.update_of_ne cc] using empty
    · intro i k
      simpa only [E,Function.comp_apply,Function.update_of_ne (tk i)] using rep i k
  have sweep : ∃ z D n, z.user = entry.user ∧ n ≤ M*(cost+3)+2 ∧
      Exec body (countedLoop clock (middleGroupStep r call saved count)) (mk entry E) n (mk z D) ∧
      D.R clock = [] ∧ inv M D := by
    apply countedLoop_exec (body := body) clock _ M cost inv _ _ entry E groups initial
    · rintro i D xs ⟨⟨coef,digit,modulus,free,mark⟩,keep,blank,read,prior⟩
      refine ⟨⟨?_,?_,?_,?_,mark⟩,?_,?_,?_,fun j ne hc hd off => (Function.update_of_ne ne ..).trans (prior j ne hc hd off)⟩
      · simpa [Function.update_of_ne (rk 0)] using coef
      · simpa [Function.update_of_ne (rk 1)] using digit
      · simpa [Function.update_of_ne (rk 2)] using modulus
      · intro j lo hi
        simpa [Function.update_of_ne (rk j)] using free j lo hi
      · simpa [Function.update_of_ne sc] using keep
      · simpa [Function.update_of_ne cc] using blank
      · intro j k
        simpa [Function.comp_apply,Function.update_of_ne (tk j)] using read j k
    · rintro h hh u D ⟨layout,keep,blank,read,prior⟩
      obtain ⟨start,finish⟩ := middleSweepBank_group (G := G) source dest p q c payload hw bs ms h hh
      dsimp only [bank] at read
      obtain ⟨z,E,n,user,time,run,next,savedEq,emptyE,placed,frame⟩ := middleGroupStep_exec
        body r call slot outside saved count apart rs rc ts tc H c h hc hh hm hB _ _ _ _ (payload h)
        (hw h) bs ms hb hmod cb cm u D (by rw [keep,ticks]) blank layout (start.symm ▸ read)
      exact ⟨z,E,n,user,time,run,frame clock cc.symm (rk 1).symm tk,next,savedEq.trans keep,emptyE,
        by dsimp only [bank]; rw [← finish]; exact placed,
        fun j hk hc hd off => (frame j hc hd off).trans (prior j hk hc hd off)⟩
  obtain ⟨u,D,n,user,time,run,done,layout,keep,free,read,frame⟩ := sweep
  obtain ⟨z,hz,reset⟩ := resetMiddleDigit_exec body r u D H c M layout
  refine ⟨z,_,_,hz.trans (user.trans hu),Nat.add_le_add price (Nat.add_le_add_right time _),.seq prepare (.seq run reset),?_,?_,?_,?_,?_,fun j hk hc hd off =>
    (Function.update_of_ne hd ..).trans (frame j hk hc hd off)⟩
  · simpa [Function.update_of_ne (rk 1).symm] using done
  · refine ⟨?_,Function.update_self ..,?_,?_,layout.2.2.2.2⟩
    · simpa [r.injective.eq_iff] using layout.1
    · simpa [r.injective.eq_iff] using layout.2.2.1
    · intro j lo hi
      simpa only [Function.update_of_ne (r.injective.ne (by omega : j ≠ 1))] using layout.2.2.2.1 j lo hi
  · simpa [Function.update_of_ne (rs 1).symm] using keep
  · simpa [Function.update_of_ne (rc 1).symm] using free
  · intro i k
    simpa only [Function.comp_apply,Function.update_of_ne (outside 1 (by decide) i)] using read i k


open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime) in
theorem middleSweep_volume_le (w G B : ℕ) (hG : 0 < G) (hB : 0 < B) :
    let M := prime^(w+1)
    let H := Nat.size M
    let group := 6*G+6+(G*(48*H*H+158*H+85+(207*(M*B)+241)*25+3)+2)+(4*H+5)
    (6*M+11*H+6)+(M*(group+3)+2+(6*H+6)) ≤ (210*(2*(Nat.size prime+1)^2)+11350)*(M*(G*(M*B))) := by
  intro M H group
  let C := 210*(2*(Nat.size prime+1)^2)+11310
  let V := G*(M*B)
  have bound : group ≤ C*V := middleGroupStep_volume_le w G B hG hB
  have pos : 0 < M := pow_pos prime_prime.pos _
  have cells : 0 < V := Nat.mul_pos hG (Nat.mul_pos pos hB)
  have bits : H ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have span := Nat.le_mul_of_pos_right M cells
  have scanned := Nat.mul_le_mul_left M bound
  change _ ≤ (C+40)*(M*V)
  nlinarith only [span,bits,scanned,pos]

/-- The boundary between prefixes in the original mixed-radix stream. -/
def middlePrefixBank (P M G B c : ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (payload : ℕ → ℕ → ℕ → ℕ → List (Fin 4)) (bs ms : List Bool) (i : ℕ) :=
  let rows := fun j => (List.range M).flatMap (fun h => (fibers M G (payload j h)).flatten)
  let writes := fun j => (List.range M).flatMap (fun h => outputPrefix (fun _ => c*h%M) M G (payload j h))
  let span := M*(G*(M*B))
  TranslationExecutionReuse.bank (putWord source p ((List.range P).flatMap rows))
    (putWord dest q ((List.range i).flatMap writes))
    (p+((i*span : ℕ) : ℤ)) (q+((i*span : ℕ) : ℤ)) bs ms []

theorem middlePrefixBank_sweep (source dest : ℤ → Fin 4) (p q : ℤ) (c : ℕ)
    (payload : ℕ → ℕ → ℕ → ℕ → List (Fin 4)) (hw : ∀ j h i y, (payload j h i y).length = B)
    (bs ms : List Bool) (i : ℕ) (hi : i < P) :
    let span := M*(G*(M*B))
    let row := fun j => (List.range M).flatMap (fun h => (fibers M G (payload j h)).flatten)
    let out := fun j => (List.range M).flatMap (fun h => outputPrefix (fun _ => c*h%M) M G (payload j h))
    let localBank := middleSweepBank M G B c (putWord source p ((List.range P).flatMap row))
      (putWord dest q ((List.range i).flatMap out)) (p+((i*span : ℕ) : ℤ)) (q+((i*span : ℕ) : ℤ))
      (payload i) bs ms
    let full := middlePrefixBank P M G B c source dest p q payload bs ms
    localBank 0 = full i ∧ localBank M = full (i+1) := by
  intro span row out localBank full
  have flatLen (n L : ℕ) (f : ℕ → List (Fin 4)) (len : ∀ k, (f k).length = L) :
      ((List.range n).flatMap f).length = n*L := by
    rw [List.flatMap_def,BlockRotationData.uniform_volume L]
    · simp
    · intro xs hx
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
      exact len j
  have uniform : BlockRotationData.Uniform span ((List.range P).map row) := by
    intro xs hx
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
    exact flatLen _ _ _ (fun h => TranslationStream.source_length M B G _ (hw j h))
  have src := FiberShift.source_fiber source p _ span i uniform (by simpa using hi)
  simp only [List.getElem_map,List.getElem_range,← List.flatMap_def] at src
  have len := flatLen i span out (fun j => flatLen M _ _ (fun h => prefix_length _ M B G _ (hw j h)))
  have dst : putWord (putWord dest q ((List.range i).flatMap out)) (q+((i*span : ℕ) : ℤ)) (out i) =
      putWord dest q ((List.range (i+1)).flatMap out) := by
    rw [← len,putWord_append_forward]
    simp [List.range_succ]
  have pos (z : ℤ) : z+(i*span : ℕ)+(M*(G*(M*B)) : ℕ) = z+((i+1)*span : ℕ) := by dsimp [span]; ring
  constructor
  · simp only [localBank,middleSweepBank,List.range_zero,List.flatMap_nil,
      putWord,Nat.zero_mul,Nat.cast_zero,add_zero]
    change TranslationExecutionReuse.bank (putWord _ _ (row i)) _ _ _ _ _ _ = _
    rw [src]
    rfl
  · change TranslationExecutionReuse.bank _ _ _ _ _ _ _ = _
    dsimp only [full,middlePrefixBank]
    change TranslationExecutionReuse.bank (putWord _ _ (row i)) (putWord _ _ (out i)) _ _ _ _ _ = _
    rw [src,dst,pos,pos]

theorem middlePrefixes_exec (body : F → Pr F T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (saved count clock : Fin T) (apart : saved ≠ count) (sc : saved ≠ clock) (cc : count ≠ clock)
    (rs : ∀ i, r i ≠ saved) (rc : ∀ i, r i ≠ count) (rk : ∀ i, r i ≠ clock)
    (ts : ∀ i, call i ≠ saved) (tc : ∀ i, call i ≠ count) (tk : ∀ i, call i ≠ clock)
    (prefixClock : Fin T) (rp : ∀ i, r i ≠ prefixClock) (tp : ∀ i, call i ≠ prefixClock)
    (sp : saved ≠ prefixClock) (cp : count ≠ prefixClock) (kp : clock ≠ prefixClock)
    (H c : ℕ) (hc : c < M) (hm : M < 2^H) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → ℕ → ℕ → List (Fin 4))
    (hw : ∀ j h i y, (payload j h i y).length = B) (bs ms : List Bool)
    (hb : Counter.value bs = B) (hmod : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (v : HS T 217 A U) (S : Stacks T A) (heads : (S.R prefixClock).length = P) (ticks : (S.R saved).length = G)
    (clockEmpty : S.R clock = []) (empty : S.R count = []) (ready : MiddleGroupReady r H c 0 M S) :
    let bank := middlePrefixBank P M G B c source dest p q payload bs ms
    let group := 6*G+6+(G*(48*H*H+158*H+85+(207*(M*B)+241)*25+3)+2)+(4*H+5)
    let sweep := (6*M+11*H+6)+(M*(group+3)+2+(6*H+6))
    RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank 0)) (S.L ∘ call) (S.R ∘ call) →
    ∃ z D n, z.user = v.user ∧ n ≤ P*(sweep+3)+2 ∧
      Exec body (countedLoop prefixClock (middleSweep r call saved count clock)) (mk v S) n (mk z D) ∧
      D.R prefixClock = [] ∧ MiddleGroupReady r H c 0 M D ∧ D.R saved = S.R saved ∧
      D.R count = [] ∧ D.R clock = [] ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank P)) (D.L ∘ call) (D.R ∘ call) := by
  intro bank group sweep rep
  let inv := fun i (D : Stacks T A) => MiddleGroupReady r H c 0 M D ∧ D.R saved = S.R saved ∧
    D.R count = [] ∧ D.R clock = [] ∧
    RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank i)) (D.L ∘ call) (D.R ∘ call)
  apply countedLoop_exec (body := body) prefixClock _ P sweep inv _ _ v S heads ⟨ready,rfl,empty,clockEmpty,rep⟩
  · rintro i D xs ⟨⟨coef,digit,modulus,free,mark⟩,keep,countEmpty,clear,read⟩
    refine ⟨⟨?_,?_,?_,?_,mark⟩,?_,?_,?_,?_⟩
    · simpa [Function.update_of_ne (rp 0)] using coef
    · simpa [Function.update_of_ne (rp 1)] using digit
    · simpa [Function.update_of_ne (rp 2)] using modulus
    · intro j lo hi
      simpa [Function.update_of_ne (rp j)] using free j lo hi
    · simpa [Function.update_of_ne sp] using keep
    · simpa [Function.update_of_ne cp] using countEmpty
    · simpa [Function.update_of_ne kp] using clear
    · intro j k
      simpa [Function.comp_apply,Function.update_of_ne (tp j)] using read j k
  · rintro i hi u D ⟨layout,keep,blank,clear,read⟩
    obtain ⟨start,finish⟩ := middlePrefixBank_sweep (G := G) source dest p q c payload hw bs ms i hi
    dsimp only [bank] at read
    obtain ⟨z,E,n,user,time,run,done,next,savedEq,emptyE,placed,frame⟩ := middleSweep_exec
      body r call slot outside saved count clock apart sc cc rs rc rk ts tc tk H c hc hm hB
      _ _ _ _ (payload i) (hw i) bs ms hb hmod cb cm u D (by rw [keep,ticks]) clear blank layout (start.symm ▸ read)
    exact ⟨z,E,n,user,time,run,frame prefixClock kp.symm cp.symm (rp 1).symm tp,next,savedEq.trans keep,emptyE,done,
      by dsimp only [bank]; rw [← finish]; exact placed⟩

def middleShearFromHeaders (r : Fin 13 ↪ Fin T) (call : Fin 12 ↪ Fin T)
    (pre gap saved count clock prefixClock : Fin T) : Pr F T 217 A U :=
  .seq (toUnary pre prefixClock (r 4) (r 5) (r 6))
    (.seq (toUnary gap saved (r 4) (r 5) (r 6))
      (.seq (countedLoop prefixClock (middleSweep r call saved count clock)) (bclear saved)))

theorem middleShearFromHeaders_exec (body : F → Pr F T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (saved count clock : Fin T) (apart : saved ≠ count) (sc : saved ≠ clock) (cc : count ≠ clock)
    (rs : ∀ i, r i ≠ saved) (rc : ∀ i, r i ≠ count) (rk : ∀ i, r i ≠ clock)
    (ts : ∀ i, call i ≠ saved) (tc : ∀ i, call i ≠ count) (tk : ∀ i, call i ≠ clock)
    (prefixClock : Fin T) (rp : ∀ i, r i ≠ prefixClock) (tp : ∀ i, call i ≠ prefixClock)
    (sp : saved ≠ prefixClock) (cp : count ≠ prefixClock) (kp : clock ≠ prefixClock)
    (pre gap : Fin T) (L K : ℕ)
    (preWork : [pre,prefixClock,r 4,r 5,r 6].Nodup) (gapWork : [gap,saved,r 4,r 5,r 6].Nodup)
    (gapOff : gap ≠ prefixClock) (hP : P < 2^L) (hG : G < 2^K)
    (H c : ℕ) (hc : c < M) (hm : M < 2^H) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → ℕ → ℕ → List (Fin 4))
    (hw : ∀ j h i y, (payload j h i y).length = B) (bs ms : List Bool)
    (hb : Counter.value bs = B) (hmod : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (v : HS T 217 A U) (S : Stacks T A) (heads : S.R pre = binSyms L P) (ticks : S.R gap = binSyms K G)
    (prefixEmpty : S.R prefixClock = []) (savedEmpty : S.R saved = [])
    (clockEmpty : S.R clock = []) (empty : S.R count = []) (ready : MiddleGroupReady r H c 0 M S) :
    let bank := middlePrefixBank P M G B c source dest p q payload bs ms
    let group := 6*G+6+(G*(48*H*H+158*H+85+(207*(M*B)+241)*25+3)+2)+(4*H+5)
    let sweep := (6*M+11*H+6)+(M*(group+3)+2+(6*H+6))
    RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank 0)) (S.L ∘ call) (S.R ∘ call) →
    ∃ z D n, z.user = v.user ∧ n ≤ (6*P+11*L+6)+(6*G+11*K+6)+(P*(sweep+3)+2)+(2*G+2) ∧
      Exec body (middleShearFromHeaders r call pre gap saved count clock prefixClock) (mk v S) n (mk z D) ∧
      D.R prefixClock = [] ∧ MiddleGroupReady r H c 0 M D ∧ D.R saved = [] ∧
      D.R count = [] ∧ D.R clock = [] ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (bank P)) (D.L ∘ call) (D.R ∘ call) := by
  intro bank group sweep rep
  obtain ⟨u,m,hu,hm',prep⟩ := toUnary_exec_linear body preWork hP v S heads
    (ready.2.2.2.1 4 (by decide) (by decide)) (ready.2.2.2.1 5 (by decide) (by decide))
    (ready.2.2.2.1 6 (by decide) (by decide))
  let E := {S with R := Function.update S.R prefixClock (List.replicate P Node.tick ++ S.R prefixClock)}
  have unchanged (j : Fin T) (hj : j ≠ prefixClock) : E.R j = S.R j := Function.update_of_ne hj ..
  obtain ⟨y,k,hy,hk,generate⟩ := toUnary_exec_linear body gapWork hG u E ((unchanged _ gapOff).trans ticks)
    ((unchanged _ (rp 4)).trans (ready.2.2.2.1 4 (by decide) (by decide)))
    ((unchanged _ (rp 5)).trans (ready.2.2.2.1 5 (by decide) (by decide)))
    ((unchanged _ (rp 6)).trans (ready.2.2.2.1 6 (by decide) (by decide)))
  let I := {E with R := Function.update E.R saved (List.replicate G Node.tick ++ E.R saved)}
  have keep (j : Fin T) (hs : j ≠ saved) (hp : j ≠ prefixClock) : I.R j = S.R j :=
    (Function.update_of_ne hs ..).trans (unchanged _ hp)
  have readyI : MiddleGroupReady r H c 0 M I :=
    ⟨(keep _ (rs 0) (rp 0)).trans ready.1,(keep _ (rs 1) (rp 1)).trans ready.2.1,
      (keep _ (rs 2) (rp 2)).trans ready.2.2.1,fun j lo hi => (keep _ (rs j) (rp j)).trans
        (ready.2.2.2.1 j lo hi),ready.2.2.2.2⟩
  have stock : (I.R saved).length = G := by simp [I,unchanged _ sp,savedEmpty]
  obtain ⟨z,D,n,hz,time,run,finished,next,retained,countDone,clockDone,read⟩ := middlePrefixes_exec (P := P)
    body r call slot outside saved count clock apart sc cc rs rc rk ts tc tk prefixClock rp tp sp cp kp
    H c hc hm hB source dest p q payload hw bs ms hb hmod cb cm y I
    (by simp [I,E,Function.update_of_ne sp.symm,prefixEmpty]) stock
    ((keep _ sc.symm kp).trans clockEmpty) ((keep _ apart.symm cp).trans empty) readyI
    (fun i k => by simpa only [Function.comp_apply,keep _ (ts i) (tp i)] using rep i k)
  obtain ⟨z',user,_,clear⟩ := bclear_exec body saved z D
  rw [retained,stock] at clear
  refine ⟨z',_,_,user.trans (hz.trans (hy.trans hu)),by dsimp only [sweep,group]; omega,
    .seq prep (.seq generate (.seq run clear)),?_,?_,Function.update_self ..,?_,?_,?_⟩
  · simpa [Function.update_of_ne sp.symm] using finished
  · exact ⟨(Function.update_of_ne (rs 0) ..).trans next.1,(Function.update_of_ne (rs 1) ..).trans next.2.1,
      (Function.update_of_ne (rs 2) ..).trans next.2.2.1,fun j lo hi =>
      (Function.update_of_ne (rs j) ..).trans (next.2.2.2.1 j lo hi),next.2.2.2.2⟩
  · simpa [Function.update_of_ne apart.symm] using countDone
  · simpa [Function.update_of_ne sc.symm] using clockDone
  · intro i k
    simpa only [Function.comp_apply,Function.update_of_ne (ts i)] using read i k

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime) in
/-- Binary clock preparation and final disposal fit the same linear-volume
bound as the payload sweep, including for an arbitrary middle radix. -/
theorem middleShearFromHeaders_volume_le (w P G B : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    let M := prime^(w+1)
    let H := Nat.size M
    let group := 6*G+6+(G*(48*H*H+158*H+85+(207*(M*B)+241)*25+3)+2)+(4*H+5)
    let sweep := (6*M+11*H+6)+(M*(group+3)+2+(6*H+6))
    (6*P+11*Nat.size P+6)+(6*G+11*Nat.size G+6)+(P*(sweep+3)+2)+(2*G+2) ≤
      (210*(2*(Nat.size prime+1)^2)+11405)*(P*(M*(G*(M*B)))) := by
  intro M H group sweep
  let C := 210*(2*(Nat.size prime+1)^2)+11350
  let V := M*(G*(M*B))
  have run : sweep ≤ C*V := middleSweep_volume_le w G B hG hB
  have pos : 0 < M := pow_pos prime_prime.pos _
  have inner : 0 < M*B := Nat.mul_pos pos hB
  have vol : 0 < V := Nat.mul_pos pos (Nat.mul_pos hG inner)
  have outer := Nat.le_mul_of_pos_right P vol
  have gap : G ≤ P*V := ((Nat.le_mul_of_pos_right G inner).trans
    (Nat.le_mul_of_pos_left _ pos)).trans (Nat.le_mul_of_pos_left V hP)
  have plen : Nat.size P ≤ P := Nat.size_le.mpr Nat.lt_two_pow_self
  have glen : Nat.size G ≤ G := Nat.size_le.mpr Nat.lt_two_pow_self
  have total := Nat.mul_le_mul_left P run
  change _ ≤ (C+55)*(P*V)
  nlinarith only [outer,gap,plen,glen,total,hP]

private theorem flatMap_range_mul {α : Type*} (n k : ℕ) (f : ℕ → List α) :
    (List.range (n*k)).flatMap f =
      (List.range n).flatMap (fun j => (List.range k).flatMap (fun i => f (j*k+i))) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.succ_mul,List.range_add,List.flatMap_append,ih,List.range_succ,
      List.flatMap_singleton,List.flatMap_map]

def middlePayload (word : Fin ((P*M*G)*(M*B)) → Fin 4) (j h i : ℕ) :=
  FlatControlledShift.payload word ((j*M+h)*G+i)

theorem middlePayload_input (word : Fin ((P*M*G)*(M*B)) → Fin 4) :
    (List.range P).flatMap (fun j => (List.range M).flatMap (fun h =>
      (fibers M G (middlePayload word j h)).flatten)) = List.ofFn word := by
  rw [← FlatControlledShift.source_eq]
  simp only [fibers,← List.flatMap_def,middlePayload,flatMap_range_mul]

theorem middlePayload_output (word : Fin ((P*M*G)*(M*B)) → Fin 4) (c : ℕ) :
    (List.range P).flatMap (fun j => (List.range M).flatMap (fun h =>
      outputPrefix (fun _ => c*h%M) M G (middlePayload word j h))) =
    outputPrefix (fun i => c*(i/G%M)%M) M (P*M*G) (FlatControlledShift.payload word) := by
  simp only [outputPrefix,← List.flatMap_def,flatMap_range_mul,middlePayload]
  refine List.flatMap_congr fun j _ => List.flatMap_congr fun h hh => List.flatMap_congr fun i hi => ?_
  have hM := List.mem_range.mp hh
  have hG := List.mem_range.mp hi
  have digit : (((j*M+h)*G+i)/G)%M = h := by
    rw [Nat.add_comm ((j*M+h)*G) i,Nat.mul_comm (j*M+h) G,Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt hG),
      Nat.div_eq_of_lt hG,Nat.zero_add,Nat.add_comm (j*M) h,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hM]
  rw [digit]

theorem middlePayload_initial (word : Fin ((P*M*G)*(M*B)) → Fin 4) (c : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs ms : List Bool) :
    middlePrefixBank P M G B c source dest p q (middlePayload word) bs ms 0 =
      TranslationExecutionReuse.bank (putWord source p (List.ofFn word)) dest p q bs ms [] := by
  simp only [middlePrefixBank,List.range_zero,List.flatMap_nil,putWord,
    Nat.zero_mul,Nat.cast_zero,add_zero]
  rw [middlePayload_input word]

/-- Both tapes at the entrance to the return scan, including cells outside the word. -/
theorem middlePayload_final (word : Fin ((P*M*G)*(M*B)) → Fin 4) (c : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs ms : List Bool) :
    middlePrefixBank P M G B c source dest p q (middlePayload word) bs ms P =
      TranslationExecutionReuse.bank (putWord source p (List.ofFn word))
        (putWord dest q (FiberLayoutData.translated word (fun i => c*(i.val/G%M)%M)))
        (p+(((P*M*G)*(M*B) : ℕ) : ℤ)) (q+(((P*M*G)*(M*B) : ℕ) : ℤ)) bs ms [] := by
  simp only [middlePrefixBank,middlePayload_input word,middlePayload_output word c,FlatControlledShift.output_eq]
  simp only [Nat.mul_assoc]

/-- The return scan reuses the two payload heads and five control tapes
of the translation. Its last tape supplies the total number of rows. -/
theorem middleReturn_ready (word : Fin ((P*M*G)*(M*B)) → Fin 4) (c : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs ms ps : List Bool)
    (call : Fin 12 ↪ Fin T) (ports : Fin 8 ↪ Fin T)
    (shared : ∀ i : Fin 7, ports i.castSucc = call (![11,10,4,5,6,7,1] i))
    (S : Stacks T A)
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (middlePrefixBank P M G B c source dest p q (middlePayload word) bs ms P)) (S.L ∘ call) (S.R ∘ call))
    (rows : ∀ z, CountedLoopReuseAlphabet.binary ps z =
      readAt blank (S.L (ports 7)) (S.R (ports 7)) (z-1)) :
    let N := (P*M*G)*(M*B)
    let out := FiberLayoutData.translated word (fun i => c*(i.val/G%M)%M)
    RepT (FlatArrayNormalize.bank
      (fun z => RadixToBinary.binaryEncoding.encode (putWord dest q out z))
      (fun z => RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn word) z))
      (q+(N : ℕ)) (p+(N : ℕ)) bs ms ps) (S.L ∘ ports) (S.R ∘ ports) := by
  rw [middlePayload_final] at rep
  apply returnWord_ready
  · intro z
    rw [show ports 0 = call 11 from shared 0]
    exact (rep 11 z).symm
  · intro z
    rw [show ports 1 = call 10 from shared 1]
    exact (rep 10 z).symm
  intro i z
  fin_cases i
  · change _ = readAt blank (S.L (ports 2)) (S.R (ports 2)) _
    rw [show ports 2 = call 4 from shared 2,← CountedLoopReuseAlphabet.encoding_binary]
    exact rep 4 z
  · change _ = readAt blank (S.L (ports 3)) (S.R (ports 3)) _
    rw [show ports 3 = call 5 from shared 3,← CountedLoopReuseAlphabet.encoding_binary]
    exact rep 5 z
  · change _ = readAt blank (S.L (ports 4)) (S.R (ports 4)) _
    rw [show ports 4 = call 6 from shared 4,← CountedLoopReuseAlphabet.encoding_binary]
    exact rep 6 z
  · change _ = readAt blank (S.L (ports 5)) (S.R (ports 5)) _
    rw [show ports 5 = call 7 from shared 5,← CountedLoopReuseAlphabet.encoding_binary]
    exact rep 7 z
  · change _ = readAt blank (S.L (ports 6)) (S.R (ports 6)) _
    rw [show ports 6 = call 1 from shared 6,← CountedLoopReuseAlphabet.encoding_binary]
    exact rep 1 z
  · exact rows z

theorem middleReturn_exec (body : F → Pr F T 217 A U) (word : Fin ((P*M*G)*(M*B)) → Fin 4) (c : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs ms ps : List Bool)
    (call : Fin 12 ↪ Fin T) (ports : Fin 8 ↪ Fin T)
    (shared : ∀ i : Fin 7, ports i.castSucc = call (![11,10,4,5,6,7,1] i))
    (v : HS T 217 A U) (S : Stacks T A)
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (middlePrefixBank P M G B c source dest p q (middlePayload word) bs ms P)) (S.L ∘ call) (S.R ∘ call))
    (rows : ∀ z, CountedLoopReuseAlphabet.binary ps z =
      readAt blank (S.L (ports 7)) (S.R (ports 7)) (z-1))
    (hb : Counter.value bs = B) (hm : Counter.value ms = M) (hp : Counter.value ps = P*M*G)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (cp : GrowingCounterData.Canonical ps) (hP : 0 < P) (hM : 0 < M) (hG : 0 < G) (hB : 0 < B)
    (empty : ∀ z, q ≤ z → z < q+((P*M*G)*(M*B) : ℕ) → dest z = blank) :
    let N := (P*M*G)*(M*B)
    let out := FiberLayoutData.translated word (fun i => c*(i.val/G%M)%M)
    ∃ u D n, u.user = v.user ∧ n ≤ (327*N+2)*13+6 ∧
      Exec body (returnWord ports) (mk v S) n (mk u D) ∧
      RepT (FlatArrayNormalize.bank (fun z => RadixToBinary.binaryEncoding.encode (dest z))
        (fun z => RadixToBinary.binaryEncoding.encode (putWord source p out z)) q p bs ms ps)
        (D.L ∘ ports) (D.R ∘ ports) ∧
      ∀ j, (∀ i, ports i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  intro N out
  have ready := middleReturn_ready word c source dest p q bs ms ps call ports shared S rep rows
  change RepT (FlatArrayNormalize.bank (RowPaddingConstructedAlphabet.mapTape (putWord dest q out))
    (RowPaddingConstructedAlphabet.mapTape (putWord source p (List.ofFn word)))
    (q+(N : ℕ)) (p+(N : ℕ)) bs ms ps) _ _ at ready
  rw [RowPaddingConstructedAlphabet.map_putWord,RowPaddingConstructedAlphabet.map_putWord] at ready
  change ∃ u D n, _ ∧ _ ∧ _ ∧ RepT (FlatArrayNormalize.bank (RowPaddingConstructedAlphabet.mapTape dest)
    (RowPaddingConstructedAlphabet.mapTape (putWord source p out)) q p bs ms ps) _ _ ∧ _
  rw [RowPaddingConstructedAlphabet.map_putWord]
  apply returnPackedList_exec body ports rfl (Nat.mul_pos (Nat.mul_pos hP hM) hG) hM hB
    _ _ _ _ _ _ (by simp) (by simp only [List.length_map,out,FiberLayoutData.translated_length])
    bs ms ps hb hm hp cb cm cp _ v S ready
  intro z lo hi
  change RadixToBinary.binaryEncoding.encode (dest z) = _
  rw [empty z lo hi]
  rfl

/-- Read the shifted cell on the actual destination tape after the nested scan. -/
theorem middlePayload_read (word : Fin ((P*M*G)*(M*B)) → Fin 4) (c : ℕ)
    (source dest : ℤ → Fin 4) (p q : ℤ) (bs ms : List Bool) (call : Fin 12 ↪ Fin T) (D : Stacks T A)
    (read : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (middlePrefixBank P M G B c source dest p q (middlePayload word) bs ms P)) (D.L ∘ call) (D.R ∘ call))
    (pre : Fin P) (h : Fin M) (mid : Fin G) (t : Fin M) (j : Fin B) :
    let row := finProdFinEquiv (finProdFinEquiv (pre,h),mid)
    let pos := row.val*(M*B)+((t.val+c*h.val)%M)*B+j.val
    readAt blank (D.L (call 11)) (D.R (call 11)) ((pos : ℤ)-(P*(M*(G*(M*B))) : ℕ)) =
      RadixToBinary.binaryEncoding.encode (word (FiberLayoutData.index row t j)) := by
  intro row pos
  obtain ⟨inside,entry⟩ := List.getElem?_eq_some_iff.mp (middleShear_entry word c pre h mid t j)
  have tape := read 11 (q+pos)
  change RadixToBinary.binaryEncoding.encode (putWord dest q
    ((List.range P).flatMap (fun j => (List.range M).flatMap (fun h =>
      outputPrefix (fun _ => c*h%M) M G (middlePayload word j h)))) (q+pos)) =
    readAt blank (D.L (call 11)) (D.R (call 11)) ((q+pos)-(q+(P*(M*(G*(M*B))) : ℕ))) at tape
  rw [middlePayload_output,BinaryDivide.putWord_getElem dest q _ pos inside,entry] at tape
  simpa only [add_sub_add_left_eq_sub] using tape.symm

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
theorem middlePackedShear_exec (body : F → Pr F T 217 A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 13, i ≠ 3 → ∀ j, call j ≠ r i)
    (saved count clock : Fin T) (apart : saved ≠ count) (sc : saved ≠ clock) (cc : count ≠ clock)
    (rs : ∀ i, r i ≠ saved) (rc : ∀ i, r i ≠ count) (rk : ∀ i, r i ≠ clock)
    (ts : ∀ i, call i ≠ saved) (tc : ∀ i, call i ≠ count) (tk : ∀ i, call i ≠ clock)
    (prefixClock : Fin T) (rp : ∀ i, r i ≠ prefixClock) (tp : ∀ i, call i ≠ prefixClock)
    (sp : saved ≠ prefixClock) (cp : count ≠ prefixClock) (kp : clock ≠ prefixClock)
    (pre gap : Fin T) (w : ℕ) (radix : M = prime^(w+1))
    (preWork : [pre,prefixClock,r 4,r 5,r 6].Nodup) (gapWork : [gap,saved,r 4,r 5,r 6].Nodup)
    (gapOff : gap ≠ prefixClock) (hP : 0 < P) (hG : 0 < G)
    (c : ℕ) (hc : c < M) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin ((P*M*G)*(M*B)) → Fin 4)
    (bs ms : List Bool)
    (hb : Counter.value bs = B) (hmod : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (v : HS T 217 A U) (S : Stacks T A) (heads : S.R pre = binSyms (Nat.size P) P) (ticks : S.R gap = binSyms (Nat.size G) G)
    (prefixEmpty : S.R prefixClock = []) (savedEmpty : S.R saved = [])
    (clockEmpty : S.R clock = []) (empty : S.R count = []) (ready : MiddleGroupReady r (Nat.size M) c 0 M S)
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (TranslationExecutionReuse.bank (putWord source p (List.ofFn word)) dest p q bs ms []))
      (S.L ∘ call) (S.R ∘ call)) :
    ∃ z D n, z.user = v.user ∧ n ≤ (210*(2*(Nat.size prime+1)^2)+11405)*(P*(M*(G*(M*B)))) ∧
      Exec body (middleShearFromHeaders r call pre gap saved count clock prefixClock) (mk v S) n (mk z D) ∧
      D.R prefixClock = [] ∧ MiddleGroupReady r (Nat.size M) c 0 M D ∧ D.R saved = [] ∧
      D.R count = [] ∧ D.R clock = [] ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (middlePrefixBank P M G B c source dest p q (middlePayload word) bs ms P)) (D.L ∘ call) (D.R ∘ call) := by
  subst M
  rw [← middlePayload_initial word c] at rep
  obtain ⟨z,D,n,user,time,run,frame⟩ := middleShearFromHeaders_exec body r call slot outside
    saved count clock apart sc cc rs rc rk ts tc tk prefixClock rp tp sp cp kp pre gap _ _
    preWork gapWork gapOff (Nat.lt_size_self P) (Nat.lt_size_self G) _ c hc
    (Nat.lt_size_self _) hB source dest p q (middlePayload word)
    (fun j h i => FlatControlledShift.payload_length word _) bs ms hb hmod cb cm v S heads ticks
    prefixEmpty savedEmpty clockEmpty empty ready rep
  exact ⟨z,D,n,user,time.trans (middleShearFromHeaders_volume_le w P G B hP hG hB),run,frame⟩

def middleArithmetic : Fin 13 ↪ Fin 30 := Fin.castLEEmb (by decide)
def middleTranslation : Fin 12 ↪ Fin 30 := ⟨![13,14,15,16,17,18,19,20,3,21,22,23],by decide⟩

def middleShearAndReturn (bank : Fin 30 ↪ Fin T) (ports : Fin 8 ↪ Fin T) : Pr F T 217 A U :=
  .seq (embProg bank Empty.elim (middleShearFromHeaders middleArithmetic middleTranslation 28 29 24 25 26 27))
    (returnWord ports)

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime) in
theorem middleShearAndReturn_exec (body : F → Pr F T 217 A U)
    (bank : Fin 30 ↪ Fin T) (ports : Fin 8 ↪ Fin T)
    (shared : ∀ i : Fin 7, ports i.castSucc = bank (middleTranslation (![11,10,4,5,6,7,1] i)))
    (parked : ∀ i, bank i ≠ ports 7)
    (w c : ℕ) (radix : M = prime^(w+1)) (hc : c < M) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin ((P*M*G)*(M*B)) → Fin 4)
    (bs ms ps : List Bool) (hb : Counter.value bs = B) (hm : Counter.value ms = M)
    (hp : Counter.value ps = P*M*G) (cb : GrowingCounterData.Canonical bs)
    (cm : GrowingCounterData.Canonical ms) (cp : GrowingCounterData.Canonical ps)
    (v : HS T 217 A U) (S : Stacks T A)
    (heads : S.R (bank 28) = binSyms P.size P) (ticks : S.R (bank 29) = binSyms G.size G)
    (free : ∀ i : Fin 30, 24 ≤ i → i ≤ 27 → S.R (bank i) = [])
    (ready : MiddleGroupReady middleArithmetic M.size c 0 M (embStk bank S))
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (TranslationExecutionReuse.bank (putWord source p (List.ofFn word)) dest p q bs ms []))
      (S.L ∘ bank ∘ middleTranslation) (S.R ∘ bank ∘ middleTranslation))
    (rows : ∀ z, CountedLoopReuseAlphabet.binary ps z = readAt blank (S.L (ports 7)) (S.R (ports 7)) (z-1))
    (empty : ∀ z, q ≤ z → z < q+((P*M*G)*(M*B) : ℕ) → dest z = blank) :
    let N := (P*M*G)*(M*B)
    let out := FiberLayoutData.translated word (fun i => c*(i.val/G%M)%M)
    ∃ u D n, u.user = v.user ∧ n ≤ (210*(2*(Nat.size prime+1)^2)+15688)*N ∧
      Exec body (middleShearAndReturn bank ports) (mk v S) n (mk u D) ∧
      RepT (FlatArrayNormalize.bank (fun z => RadixToBinary.binaryEncoding.encode (dest z))
        (fun z => RadixToBinary.binaryEncoding.encode (putWord source p out z)) q p bs ms ps)
        (D.L ∘ ports) (D.R ∘ ports) := by
  intro N out
  obtain ⟨u,D,n,hu,hn,shear,_,_,_,_,_,tapes⟩ := middlePackedShear_exec
    (F := Empty) Empty.elim middleArithmetic middleTranslation (by decide) (by decide)
    24 25 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) 27 (by decide) (by decide) (by decide) (by decide) (by decide)
    28 29 w radix (by decide) (by decide) (by decide) hP hG c hc hB source dest p q word bs ms
    hb hm cb cm (embDn bank v) (embStk bank S) heads ticks (free 27 (by decide) (by decide))
    (free 24 (by decide) (by decide)) (free 26 (by decide) (by decide)) (free 25 (by decide) (by decide)) ready rep
  obtain ⟨y,E,run,_,hy,eq,keep⟩ := exec_emb (body' := body) (ι := Empty.elim)
    bank.injective (fun e => nomatch e) shear v rfl S rfl
  rw [← eq] at tapes
  obtain ⟨left,right⟩ := keep _ parked
  have hM : 0 < M := radix ▸ pow_pos prime_prime.pos _
  obtain ⟨z,D,m,hz,ht,ret,result,_⟩ := middleReturn_exec body word c source dest p q bs ms ps
    (middleTranslation.trans bank) ports shared y E tapes (by simpa only [left,right] using rows)
    hb hm hp cb cm cp hP hM hG hB empty
  have pos : 0 < N := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hP hM) hG) (Nat.mul_pos hM hB)
  have span : P*(M*(G*(M*B))) = N := by simp [N,Nat.mul_assoc]
  rw [span] at hn
  change m ≤ (327*N+2)*13+6 at ht
  exact ⟨z,D,n+m,hz.trans (hy.trans hu),by nlinarith only [hn,ht,pos],Exec.seq run ret,result⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
