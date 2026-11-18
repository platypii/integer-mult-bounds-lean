module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackScheduledShear
public import IntegerMultBounds.MathlibTM2.Cover.Itinerary

public import IntegerMultBounds.MathlibTM2.Cover.FallbackWord


/-! Undo a forward column-clearing addition from a matrix entry and a pivot reciprocal. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {T A M d W : ℕ} [NeZero M] {P U : Type} (k t : Fin d)
local notation "N" => prefixSize (Q := M) t
local notation "B" => suffixSize (Q := M) (W := W) t

def productShear (bank : Fin 31 ↪ Fin T) : Pr P T 217 A U :=
  .seq (bmodmul (bank 29) (bank 30) (bank 2) (bank 0) (bank 4) (bank 5) (bank 6)
    (bank 7) (bank 8) (bank 9) (bank 10) (bank 11) (bank 12))
    (scheduledShear k t ((Fin.castLEEmb (by decide)).trans bank))

theorem productShear_exec (hk : k < t) (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (pivot col row : Fin d)
    (inv : ZMod M) (hinv : matrix pivot col * inv = 1) (body : P → Pr P T 217 A U)
    (bank : Fin 31 ↪ Fin T) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T 217 A U) (S : Stacks T A)
    (base : S.R (bank 2) = binSyms H M) (one : S.R (bank 28) = binSyms 1 1)
    (width : S.R (bank 27) = binSyms J W) (coeffBlank : S.R (bank 0) = [])
    (entry : S.R (bank 29) = binSyms H (matrix row col).val)
    (reciprocal : S.R (bank 30) = binSyms H inv.val)
    (free : ∀ i : Fin 31, 1 ≤ i → i ≤ 26 → i ≠ 2 → i ≠ 24 → i ≠ 25 → S.R (bank i) = [])
    (left : ∀ i : Fin 12, i < 10 → S.L (bank ((Fin.castLEEmb (by decide : 29 ≤ 31)) (shearTranslation i))) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (a : Fin (M^d*W) → Fin 4)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn a) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    let g := t.val-1-k.val
    let s := d-1-t.val
    let L := t.val*H+1
    let K := g*H+1
    let V := s*H+J
    ∃ z F n, z.user = v.user ∧
      n ≤ 48*H*H+150*H+64 + (dimensionTime H 1 t.val + dimensionTime H 1 g + dimensionTime H J s +
        (6*N+17*L+4*V+10*H+31 + N*(L*(12*(K+H)+78)+22*K+180*H+173+48*H*H+(207*(M*B)+241)*25)+2)) ∧
      Exec body (productShear k t bank) (mk v S) n (mk z F) ∧
      PrefixCopyReady (bank 13) (bank 3) (bank 4) (bank 5) (t.val*H+1) (prefixSize (Q := M) t) F ∧
      ShearCounters (suffixSize (Q := M) (W := W) t) M (bank ∘ (Fin.castLEEmb (by decide : 29 ≤ 31)) ∘ shearTranslation) F ∧
      (∀ pos : ℤ, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-(p+(M^d*W : ℕ))) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn a) pos)) ∧
      (∀ pos : ℤ, pos < q ∨ q+(M^d*W : ℕ) ≤ pos →
        readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-(q+(M^d*W : ℕ))) =
          RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∀ (x : Fin d → ZMod M) (j : Fin W),
        let y := (RowOp.shear k t hk (matrix row col * Ring.inverse (matrix pivot col))).apply x
        readAt blank (F.L (bank 25)) (F.R (bank 25)) (((index y j).val : ℤ) - (M^d*W : ℕ)) =
          RadixToBinary.binaryEncoding.encode (a (index x j)) := by
  let a₀ := matrix row col
  let c := a₀*inv
  have zero (i : Fin 31) (h : 4 ≤ i) (h' : i ≤ 11) :=
    free i (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨u,m,hu,hm',mul⟩ := bmodmul_exec body
    (a := bank 29) (b := bank 30) (m := bank 2) (c := bank 0) (p := bank 4)
    (qq := bank 5) (s := bank 6) (rr := bank 7) (t := bank 8) (tx := bank 9)
    (ty := bank 10) (tz := bank 11) (cy := bank 12)
    (by simp [List.nodup_cons,bank.injective.eq_iff]) (bank.injective.ne (by decide))
    (bank.injective.ne (by decide)) (bank.injective.ne (by decide))
    (a₀.val_lt.trans hm) (inv.val_lt.trans hm) hm (NeZero.pos M) v S entry reciprocal base
    (zero _ (by decide) (by decide)) (zero _ (by decide) (by decide)) (zero _ (by decide) (by decide))
    (zero _ (by decide) (by decide)) (zero _ (by decide) (by decide)) (zero _ (by decide) (by decide))
    (zero _ (by decide) (by decide)) (zero _ (by decide) (by decide))
  rw [coeffBlank,List.append_nil,← ZMod.val_mul] at mul
  let D : Stacks T A := {S with R := Function.update S.R (bank 0) (binSyms H c.val)}
  have keep (i : Fin 31) (h : i ≠ 0) : D.R (bank i) = S.R (bank i) :=
    Function.update_of_ne (bank.injective.ne h) _ _
  let ports : Fin 29 ↪ Fin 31 := Fin.castLEEmb (by decide)
  obtain ⟨z,F,n,hz,hn,run,read⟩ := scheduledShear_exec k t hk c body (ports.trans bank)
    H J hm hw hW u D ((keep 2 (by decide)).trans base) ((keep 28 (by decide)).trans one)
    ((keep 27 (by decide)).trans width) (by change D.R (bank 0) = _; simp [D])
    (by
      intro i lo hi h2 h24 h25
      apply (keep (ports i) _).trans (free _ lo hi _ _ _)
      all_goals intro h; have e := congrArg Fin.val h; simp [ports] at e; omega)
    left source dest p q a
    (by change ∀ j, _ = readAt blank _ (D.R (bank 24)) _; rw [keep 24 (by decide)]; exact src)
    (by change ∀ j, _ = readAt blank _ (D.R (bank 25)) _; rw [keep 25 (by decide)]; exact dst)
  refine ⟨z,F,m+n,hz.trans hu,Nat.add_le_add (by nlinarith only [hm']) hn,Exec.seq mul run,?_⟩
  rw [Itinerary.inverse_unique hinv]
  exact read

end IntegerMultBounds.MathlibTM2.Cover.Fallback
