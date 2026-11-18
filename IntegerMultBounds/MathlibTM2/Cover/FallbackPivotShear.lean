module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackProductShear
public import IntegerMultBounds.MathlibTM2.Cover.Itinerary

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotInverse


/-! Undo a forward column-clearing addition from the pivot and the entry to clear. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {T A d W : ℕ} {P U : Type} (k t : Fin d)
variable (b w : ℕ) [NeZero (b^(w+1))]
local notation "M" => b^(w+1)
local notation "N" => prefixSize (Q := M) t
local notation "B" => suffixSize (Q := M) (W := W) t


def inverseShearPorts : Fin 16 ↪ Fin 34 :=
  ⟨![30,1,3,4,2,5,6,7,8,9,10,11,12,13,31,32],by decide⟩

def pivotShear (bank : Fin 34 ↪ Fin T) : Pr P T 217 A U :=
  .seq (pivotInverse b (inverseShearPorts.trans bank) (bank 33))
    (productShear k t ((Fin.castLEEmb (by decide)).trans bank))

def pivotShearTime (H J : ℕ) : ℕ :=
  let g := t.val-1-k.val
  let s := d-1-t.val
  let L := t.val*H+1
  let K := g*H+1
  let V := s*H+J
  let product := 48*H*H+152*H+66
  let inverse := 14*H+16+(b-2)*product+product+w*(12*H+15+b*product)
  let dimensions := dimensionTime H 1 t.val + dimensionTime H 1 g + dimensionTime H J s
  let pass := 6*N+17*L+4*V+10*H+31 + N*(L*(12*(K+H)+78)+22*K+180*H+173+48*H*H+(207*(M*B)+241)*25)
  inverse + (48*H*H+150*H+64 + (dimensions + (pass+2)))

theorem pivotShear_exec (hk : k < t) (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (pivot col row : Fin d)
    (hb : b.Prime) (unit : IsUnit (matrix pivot col)) (body : P → Pr P T 217 A U)
    (bank : Fin 34 ↪ Fin T) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T 217 A U) (S : Stacks T A)
    (base : S.R (bank 2) = binSyms H M) (one : S.R (bank 28) = binSyms 1 1)
    (width : S.R (bank 27) = binSyms J W) (coeffBlank : S.R (bank 0) = [])
    (entry : S.R (bank 29) = binSyms H (matrix row col).val)
    (pivotWord : S.R (bank 31) = binSyms H (matrix pivot col).val)
    (paddedOne : S.R (bank 32) = binSyms H (1 : ZMod M).val)
    (ticks : (S.R (bank 33)).length = w) (blankInv : S.R (bank 30) = [])
    (free : ∀ i : Fin 34, 1 ≤ i → i ≤ 26 → i ≠ 2 → i ≠ 24 → i ≠ 25 → S.R (bank i) = [])
    (left : ∀ i : Fin 12, i < 10 → S.L (bank ((Fin.castLEEmb (by decide : 29 ≤ 34)) (shearTranslation i))) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (a : Fin (M^d*W) → Fin 4)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn a) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    ∃ z F n, z.user = v.user ∧ n ≤ pivotShearTime (W := W) k t b w H J ∧
      Exec body (pivotShear k t b bank) (mk v S) n (mk z F) ∧
      PrefixCopyReady (bank 13) (bank 3) (bank 4) (bank 5) (t.val*H+1) (prefixSize (Q := M) t) F ∧
      ShearCounters (suffixSize (Q := M) (W := W) t) M (bank ∘ (Fin.castLEEmb (by decide : 29 ≤ 34)) ∘ shearTranslation) F ∧
      (∀ pos : ℤ, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-(p+(M^d*W : ℕ))) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn a) pos)) ∧
      (∀ pos : ℤ, pos < q ∨ q+(M^d*W : ℕ) ≤ pos →
        readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-(q+(M^d*W : ℕ))) =
          RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∀ (x : Fin d → ZMod M) (j : Fin W),
        let y := (RowOp.shear k t hk (matrix row col * Ring.inverse (matrix pivot col))).apply x
        readAt blank (F.L (bank 25)) (F.R (bank 25)) (((index y j).val : ℤ) - (M^d*W : ℕ)) =
          RadixToBinary.binaryEncoding.encode (a (index x j)) := by
  let ports : Fin 31 ↪ Fin 34 := Fin.castLEEmb (by decide)
  have disjoint : ∀ i, inverseShearPorts i ≠ 33 := by decide
  have scratch : ∀ i : Fin 16, i ≠ 0 → i ≠ 4 → i < 13 →
      1 ≤ inverseShearPorts i ∧ inverseShearPorts i ≤ 26 ∧ inverseShearPorts i ≠ 2 ∧
      inverseShearPorts i ≠ 24 ∧ inverseShearPorts i ≠ 25 := by decide
  obtain ⟨u,D,m,hu,hm',invRun,_,invWord,hL,_,_,frame⟩ := pivotInverse_exec body b w hb
    (matrix pivot col) unit (inverseShearPorts.trans bank) (bank 33)
    (fun i => bank.injective.ne (disjoint i)) H hm v S ticks pivotWord paddedOne base (by
      intro i hi hj
      by_cases h : i = 0
      · subst i; exact blankInv
      · obtain ⟨a,c,e,f,g⟩ := scratch i h hi hj
        exact free _ a c e f g)
  have kept (i : Fin 31) (h : i < 30) : D.R (bank (ports i)) = S.R (bank (ports i)) := by
    apply frame <;> apply bank.injective.ne
    · change ports i ≠ 30; intro eq; have e := congrArg Fin.val eq; change i.val = 30 at e; omega
    · intro eq; have e := congrArg Fin.val eq; change i.val = 33 at e; omega
  obtain ⟨z,F,n,hz,hn,run,read⟩ := productShear_exec k t hk matrix pivot col row _
    (Ring.mul_inverse_cancel _ unit) body (ports.trans bank) H J hm hw hW u D
    ((kept 2 (by decide)).trans base) ((kept 28 (by decide)).trans one)
    ((kept 27 (by decide)).trans width) ((kept 0 (by decide)).trans coeffBlank)
    ((kept 29 (by decide)).trans entry) invWord
    (fun i lo hi h2 h24 h25 => (kept i (by omega)).trans (free _ lo hi
      (fun h => h2 (ports.injective h)) (fun h => h24 (ports.injective h))
      (fun h => h25 (ports.injective h))))
    (by rw [hL]; exact left) source dest p q a
    (by change ∀ j, _ = readAt blank _ (D.R (bank (ports 24))) _; rw [hL,kept 24 (by decide)]; exact src)
    (by change ∀ j, _ = readAt blank _ (D.R (bank (ports 25))) _; rw [hL,kept 25 (by decide)]; exact dst)
  exact ⟨z,F,m+n,hz.trans hu,Nat.add_le_add hm' hn,Exec.seq invRun run,read⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
