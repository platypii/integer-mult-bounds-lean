module

public import IntegerMultBounds.Machine.FlatControlledShift
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixStep
public import IntegerMultBounds.Machine.TranslationPreparedFamily
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! A counted shear over every physical prefix in the original coordinate order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host TranslationExecutionReuse
open TranslationStream (blocks fibers)
open TranslationPreparedFamily (outputPrefix)
open Mult.PhaseCellToeplitz (countedLoop countedLoop_exec)
variable {T A : ℕ} {P U : Type}

def prefixBank (N M B : ℕ) (off : ℕ → ℕ) (source dest : ℤ → Fin 4) (p q : ℤ)
    (payload : ℕ → ℕ → List (Fin 4)) (bs ms : List Bool) (i : ℕ) :=
  bank (putWord source p (fibers M N payload).flatten)
    (putWord dest q (outputPrefix off M i payload))
    (p+((i*(M*B) : ℕ) : ℤ)) (q+((i*(M*B) : ℕ) : ℤ)) bs ms []

structure PrefixReady (r : Fin 15 ↪ Fin T) (L K H stride c M i : ℕ) (D : Stacks T A) : Prop where
  counter : D.R (r 13) = binSyms L i
  gap : D.R (r 14) = binSyms K stride
  coef : D.R (r 0) = binSyms H c
  modulus : D.R (r 2) = binSyms H M
  empty : ∀ j : Fin 15, 1 ≤ j → j ≤ 12 → j ≠ 2 → D.R (r j) = []
  marker : D.L (r 3) = [separator]

theorem prefixLoop_exec (body : P → Pr P T 217 A U) (r : Fin 15 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 15, i ≠ 3 → ∀ j, call j ≠ r i)
    (count : Fin T) (hr : ∀ i, r i ≠ count) (ht : ∀ i, call i ≠ count)
    (L K H N stride c M B : ℕ) (fits : N ≤ 2^L) (hs : stride < 2^K) (ps : 0 < stride) (hc : c < M) (hM : M < 2^H) (hB : 0 < B)
    (v : HS T 217 A U) (S : Stacks T A) (ready : PrefixReady r L K H stride c M 0 S)
    (source dest : ℤ → Fin 4) (p q : ℤ) (payload : ℕ → ℕ → List (Fin 4))
    (hw : ∀ i y, (payload i y).length = B) (bs ms : List Bool)
    (hb : Counter.value bs = B) (hm : Counter.value ms = M)
    (cb : GrowingCounterData.Canonical bs) (cm : GrowingCounterData.Canonical ms)
    (ticks : (S.R count).length = N)
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (prefixBank N M B (fun i => c*(i/stride%M)%M) source dest p q payload bs ms 0)) (S.L ∘ call) (S.R ∘ call)) :
    ∃ z F n, z.user = v.user ∧ n ≤ N*(L*(12*(K+H)+78)+22*K+180*H+173+48*H*H+(207*(M*B)+241)*25)+2 ∧
      Exec body (countedLoop count (prefixStep r call)) (mk v S) n (mk z F) ∧
      F.R count = [] ∧ PrefixReady r L K H stride c M N F ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (prefixBank N M B (fun i => c*(i/stride%M)%M) source dest p q payload bs ms N)) (F.L ∘ call) (F.R ∘ call) := by
  let W := prefixBank N M B (fun i => c*(i/stride%M)%M) source dest p q payload bs ms
  let Inv (i : ℕ) (D : Stacks T A) := PrefixReady r L K H stride c M i D ∧
    RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding (W i)) (D.L ∘ call) (D.R ∘ call)
  let cost := L*(12*(K+H)+78)+22*K+180*H+170+48*H*H+(207*(M*B)+241)*25
  have run := countedLoop_exec (body := body) count (prefixStep r call) N cost Inv
  have stable : ∀ i D xs, Inv i D → Inv i {D with R := Function.update D.R count xs} := by
    rintro i D xs ⟨h,rep⟩
    refine ⟨⟨?_,?_,?_,?_,?_,h.marker⟩,?_⟩
    · simpa [Function.update_of_ne (hr 13)] using h.counter
    · simpa [Function.update_of_ne (hr 14)] using h.gap
    · simpa [Function.update_of_ne (hr 0)] using h.coef
    · simpa [Function.update_of_ne (hr 2)] using h.modulus
    · intro j hj hk hl; simpa [Function.update_of_ne (hr j)] using h.empty j hj hk hl
    · intro j k; simpa [Function.comp_apply,Function.update_of_ne (ht j)] using rep j k
  rw [← show cost+3 = L*(12*(K+H)+78)+22*K+180*H+173+48*H*H+(207*(M*B)+241)*25 by dsimp [cost]; omega]
  apply run stable _ v S ticks ⟨ready,rep⟩
  intro i hi u D h
  let src := putWord source p (fibers M N payload).flatten
  let off := fun i => c*(i/stride%M)%M
  let dst := putWord dest q (outputPrefix off M i payload)
  let atHead := fun (k : ℤ) => k+((i*(M*B) : ℕ) : ℤ)
  have sourceEq := TranslationPreparedFamily.source_fiber M B N i source p payload hw hi
  have heq : input src dst (atHead p) (atHead q) (blocks M (payload i)) bs ms [] = W i := by
    simp only [TranslationExecutionReuse.input,src,atHead,sourceEq,W,prefixBank,dst,off]
  obtain ⟨z,F,n,hu,hn,he,next,empty,mark,frame,hrp⟩ := prefixStep_exec body r call slot outside
    L K H i stride c M B (hi.trans_le fits) hs hM ps hc hB u D h.1.counter h.1.gap h.1.coef
    h.1.modulus h.1.empty h.1.marker src dst (atHead p) (atHead q) (blocks M (payload i)) bs ms
    (by simp [blocks]) (TranslationPreparedFamily.blocks_uniform M B i payload hw)
    hb hm cb cm (heq.symm ▸ h.2)
  have keep (j : Fin 15) (hj : j ≠ 3) (hp : j ≠ 13) :=
    (frame (r j) (outside j hj) (r.injective.ne hp)).1
  refine ⟨z,F,n,hu,hn,he,(frame count ht (hr 13).symm).1,⟨next,
    (keep 14 (by decide) (by decide)).trans h.1.gap,(keep 0 (by decide) (by decide)).trans h.1.coef,
    (keep 2 (by decide) (by decide)).trans h.1.modulus,?_,slot ▸ mark⟩,?_⟩
  · intro j hj hk hl
    by_cases h3 : j = 3
    · simpa [slot,h3] using empty
    · exact (keep j h3 (by omega)).trans (h.1.empty j hj hk hl)
  · have hout : putWord dst (atHead q) (BlockRotationData.rotate (off i) (blocks M (payload i))).flatten =
        putWord dest q (outputPrefix off M (i+1) payload) := by
      unfold dst atHead
      rw [← TranslationPreparedFamily.prefix_length off M B i payload hw,putWord_append_forward,
        TranslationPreparedFamily.prefix_succ]
    have pos (k : ℤ) : atHead k + (M : ℤ)*B = k+(((i+1)*(M*B) : ℕ) : ℤ) := by
      dsimp [atHead]; ring
    have outEq : output M (off i) B src dst (atHead p) (atHead q) (blocks M (payload i)) bs ms [] = W (i+1) := by
      unfold output
      rw [hout,pos,pos]
      simp only [src,atHead,sourceEq,W,prefixBank,off]
    exact outEq ▸ hrp

open FlatCoordinateLayout

/-- With the original row-major payload the loop's completed prefix is the
ordered shear, including all intervening coordinates and suffix symbols. -/
theorem prefixLoop_entry {d M W : ℕ} [NeZero M] (t k : Fin d) (hk : k < t)
    (c : ZMod M) (a : Fin (M^d*W) → Fin 4) (x : Fin d → ZMod M) (j : Fin W) :
    let off := fun i => c.val*((i/M^(t.val-1-k.val))%M)%M
    (outputPrefix off M (prefixSize (Q := M) t) (FlatControlledShift.payload (fiberView a t)))[
      (index (Function.update x t (x t + c*x k)) j).val]? = some (a (index x j)) := by
  dsimp only
  rw [FlatControlledShift.output_eq]
  refine shift_transport a _ t k c (fun p => c.val*((p.val/M^(t.val-1-k.val))%M)%M) ?_ ?_ x j
  · intro y
    simp only [earlier_control y t k hk,ZMod.val_mul]
  · exact FiberLayoutData.translated_entry _ _

end IntegerMultBounds.MathlibTM2.Cover.Fallback
