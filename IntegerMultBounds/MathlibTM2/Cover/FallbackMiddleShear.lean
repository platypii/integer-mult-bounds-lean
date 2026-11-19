module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixShear
import IntegerMultBounds.Machine.FlatControlledShift
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

end IntegerMultBounds.MathlibTM2.Cover.Fallback
