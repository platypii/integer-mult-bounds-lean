module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackReverseShear
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet

/-! Apply a live coefficient to the flat payload and return both heads to their origins. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {T A M d W : ℕ} [NeZero M] {P U : Type} (k t : Fin d)
local notation "N" => prefixSize (Q := M) t
local notation "B" => suffixSize (Q := M) (W := W) t

def weightedShear (bank : Fin 29 ↪ Fin T) : Pr P T 217 A U :=
  .seq (scheduledShear k t bank) (finishShear bank)

theorem weightedShear_exec (hk : k < t) {α : Type*} (sym : α → Fin 4) (c : ZMod M) (body : P → Pr P T 217 A U)
    (bank : Fin 29 ↪ Fin T) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T 217 A U) (S : Stacks T A)
    (base : S.R (bank 2) = binSyms H M) (one : S.R (bank 28) = binSyms 1 1)
    (width : S.R (bank 27) = binSyms J W) (coef : S.R (bank 0) = binSyms H c.val)
    (free : ∀ i : Fin 29, 1 ≤ i → i ≤ 26 → i ≠ 2 → i ≠ 24 → i ≠ 25 → S.R (bank i) = [])
    (left : ∀ i : Fin 12, i < 10 → S.L (bank (shearTranslation i)) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (a : Fin (M^d*W) → α)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ a)) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    let g := t.val-1-k.val
    let s := d-1-t.val
    let L := t.val*H+1
    let K := g*H+1
    let V := s*H+J
    ∃ z F n, z.user = v.user ∧
      n ≤ dimensionTime H 1 t.val + dimensionTime H 1 g + dimensionTime H J s +
        (6*N+17*L+4*V+10*H+31 + N*(L*(12*(K+H)+78)+22*K+180*H+173+48*H*H+(207*(M*B)+241)*25)+2) +
        (10*(t.val*H+1)+12+((327*(M^d*W)+2)*13+6)) ∧
      Exec body (weightedShear k t bank) (mk v S) n (mk z F) ∧
      F.R (bank 2) = S.R (bank 2) ∧ (∀ i : Fin 29, 27 ≤ i → F.R (bank i) = S.R (bank i)) ∧
      (∀ pos, readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-q) = RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∃ word : Fin (M^d*W) → α, (∀ pos, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ word)) pos)) ∧
        ∀ x j, word (index ((RowOp.shear k t hk c).apply x) j) = a (index x j) := by
  obtain ⟨u,D,n,hu,hn,run,modulus,headers,prefixReady,counters,sourceTape,frame,effect⟩ :=
    scheduledShear_exec k t hk c body bank H J hm hw hW v S base one width coef free left
      source dest p q (sym ∘ a) src dst
  obtain ⟨word,out,perm⟩ := shear_output_tape k t sym hk c a dest q _ _ frame effect
  open RowPaddingConstructedAlphabet in
  obtain ⟨z,F,l,hz,hl,finish,result,clean,keep⟩ := finishShear_exec body bank t hW
    (mapTape source) (mapTape dest) p q (mapArray (sym ∘ a)) (mapArray (sym ∘ word))
    (by intro pos lo hi; change RadixToBinary.binaryEncoding.encode (dest pos) = _; rw [empty pos lo hi]; rfl)
    _ u D prefixReady counters
    (fun pos => (out pos).trans (congrFun (map_array_word dest q (sym ∘ word)) pos))
    (fun pos => (sourceTape pos).trans (congrFun (map_array_word source p (sym ∘ a)) pos))
  refine ⟨z,F,n+l,hz.trans hu,Nat.add_le_add hn hl,Exec.seq run finish,?_,?_,clean,word,?_,perm⟩
  · exact (keep _ (fun i => bank.injective.ne ((by decide : ∀ i, returnPorts i ≠ 2) i))).trans modulus
  · intro i hi
    have off : ∀ j, returnPorts j ≠ i := (by decide : ∀ i : Fin 29, 27 ≤ i → ∀ j, returnPorts j ≠ i) i hi
    exact (keep _ (fun j => bank.injective.ne (off j))).trans (headers i hi)
  · intro pos
    exact (result pos).trans (congrFun (RowPaddingConstructedAlphabet.map_array_word source p (sym ∘ word)) pos).symm

end IntegerMultBounds.MathlibTM2.Cover.Fallback
