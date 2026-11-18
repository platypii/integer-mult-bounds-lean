module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackWord
public import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.BinaryDivide

/-! The physical row addition on the original flat array, for arbitrary earlier control. -/
public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {T A M d W : ℕ} [NeZero M] {P U : Type} (k t : Fin d)
local notation "N" => prefixSize (Q := M) t
local notation "B" => suffixSize (Q := M) (W := W) t
local notation "stride" => M^(t.val-1-k.val)

/-- Canonical suffix and modulus counters retained on the translation tapes. -/
@[expose] def ShearCounters (suffixWidth modulus : ℕ) (r : Fin 12 → Fin T) (S : Stacks T A) : Prop :=
  ∃ bs ms : List Bool, Counter.value bs = suffixWidth ∧ Counter.value ms = modulus ∧
    GrowingCounterData.Canonical bs ∧ GrowingCounterData.Canonical ms ∧
    (∀ z, CountedLoopReuseAlphabet.binary [] z = readAt blank (S.L (r 1)) (S.R (r 1)) (z-1)) ∧
    ∀ (i : Fin 4) z, CountedLoopReuseAlphabet.binary (![[],bs,[],ms] i) z =
      readAt blank (S.L (r (Fin.castAdd 4 (Fin.natAdd 4 i)))) (S.R (r (Fin.castAdd 4 (Fin.natAdd 4 i)))) (z-1)

theorem rowShear_exec (hk : k < t) (c : ZMod M) (body : P → Pr P T 217 A U)
    (r : Fin 15 ↪ Fin T) (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (outside : ∀ i : Fin 15, i ≠ 3 → ∀ j, call j ≠ r i)
    (count : Fin T) (hr : ∀ i, r i ≠ count) (ht : ∀ i, call i ≠ count)
    (L K H J : ℕ) (fits : N < 2^L) (hs : stride < 2^K) (hm : M < 2^H) (hb : B < 2^J)
    (hW : 0 < W) (v : HS T 217 A U) (S : Stacks T A)
    (extent : S.R (r 1) = binSyms L N) (counter : S.R (r 13) = [])
    (gap : S.R (r 14) = binSyms K stride) (coef : S.R (r 0) = binSyms H c.val)
    (modulus : S.R (r 2) = binSyms H M) (scratch : ∀ i : Fin 15, 3 ≤ i → i ≤ 12 → S.R (r i) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (a : Fin (M^d*W) → Fin 4)
    (empty : S.R count = []) (left : ∀ i : Fin 12, i < 10 → S.L (call i) = [])
    (right : ∀ i : Fin 12, i < 10 → S.R (call i) = if i = 5 then binSyms J B else [])
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn a) z) =
      readAt blank (S.L (call 10)) (S.R (call 10)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (call 11)) (S.R (call 11)) (z-q)) :
    ∃ z F n, z.user = v.user ∧
      n ≤ 6*N+17*L+4*J+10*H+31 + N*(L*(12*(K+H)+78)+22*K+180*H+173+48*H*H+(207*(M*B)+241)*25)+2 ∧
      Exec body (prefixShear r call count) (mk v S) n (mk z F) ∧
      F.R count = [] ∧ PrefixReady r L K H stride c.val M N F ∧
      ShearCounters B M call F ∧
      (∀ pos : ℤ, readAt blank (F.L (call 10)) (F.R (call 10)) (pos-(p+(M^d*W : ℕ))) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn a) pos)) ∧
      (∀ pos : ℤ, pos < q ∨ q+(M^d*W : ℕ) ≤ pos →
        readAt blank (F.L (call 11)) (F.R (call 11)) (pos-(q+(M^d*W : ℕ))) =
          RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∀ (x : Fin d → ZMod M) (j : Fin W),
        let y := (RowOp.shear k t hk c).apply x
        readAt blank (F.L (call 11)) (F.R (call 11)) (((index y j).val : ℤ) - (M^d*W : ℕ)) =
          RadixToBinary.binaryEncoding.encode (a (index x j)) := by
  let payload := FlatControlledShift.payload (fiberView a t)
  obtain ⟨bs,ms,z,F,n,hb',hm',cb,cm,hu,hn,run,rest,ready,rep⟩ := prefixShear_exec body r call slot outside count hr ht
    L K H J N stride c.val M B hb fits hs (pow_pos (NeZero.pos M) _) c.val_lt hm
    (Nat.mul_pos (pow_pos (NeZero.pos M) _) hW) v S extent counter gap coef modulus scratch source dest p q
    payload (FlatControlledShift.payload_length _) empty left right
    (by simpa only [payload,FlatControlledShift.source_eq,fiberView_word] using src) dst
  refine ⟨z,F,n,hu,hn,run,rest,ready,?_,?_,?_,?_⟩
  · refine ⟨bs,ms,hb',hm',cb,cm,?_,?_⟩
    · intro z
      rw [← CountedLoopReuseAlphabet.encoding_binary]
      exact rep 1 z
    intro i z
    rw [← CountedLoopReuseAlphabet.encoding_binary]
    fin_cases i <;> first | exact rep 4 z | exact rep 5 z | exact rep 6 z | exact rep 7 z
  · intro pos
    have tape := rep 10 pos
    change RadixToBinary.binaryEncoding.encode (putWord source p (TranslationStream.fibers M N payload).flatten pos) =
      readAt blank (F.L (call 10)) (F.R (call 10)) (pos-(p+((N*(M*B) : ℕ) : ℤ))) at tape
    rw [← split_volume t] at tape
    simpa only [payload,FlatControlledShift.source_eq,fiberView_word] using tape.symm
  · intro pos outsideWord
    have tape := rep 11 pos
    let off := fun i => c.val*((i/stride)%M)%M
    let out := TranslationPreparedFamily.outputPrefix off M N payload
    change RadixToBinary.binaryEncoding.encode (putWord dest q out pos) =
      readAt blank (F.L (call 11)) (F.R (call 11)) (pos-(q+((N*(M*B) : ℕ) : ℤ))) at tape
    have len : out.length = M^d*W := (TranslationPreparedFamily.prefix_length off M B N payload
      (FlatControlledShift.payload_length _)).trans (split_volume t).symm
    rw [putWord_outside _ _ _ _ (by simpa only [len] using outsideWord),← split_volume t] at tape
    exact tape.symm
  intro x j
  let addr := (index ((RowOp.shear k t hk c).apply x) j).val
  have entry := prefixLoop_entry t k hk c a x j
  obtain ⟨inside,he⟩ := List.getElem?_eq_some_iff.mp entry
  have cell := BinaryDivide.putWord_getElem dest q _ addr inside
  have readCell := cell.trans he
  have tape := rep 11 (q+addr)
  change RadixToBinary.binaryEncoding.encode (putWord dest q _ (q+addr)) =
    readAt blank (F.L (call 11)) (F.R (call 11)) ((q+addr)-(q+((N*(M*B) : ℕ) : ℤ))) at tape
  rw [readCell,← split_volume t] at tape
  rw [show (q+addr)-(q+((M^d*W : ℕ) : ℤ)) = (addr : ℤ)-(M^d*W : ℕ) by omega] at tape
  exact tape.symm

end IntegerMultBounds.MathlibTM2.Cover.Fallback
