module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackMatrixRead

/-! Undo one forward addition directly from the packed elimination matrix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {T A d W : ℕ} {P U : Type} (k t : Fin d) (b w : ℕ) [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def matrixReadPorts : Fin 8 ↪ Fin 35 := ⟨![0,2,34,31,4,5,6,29],by decide⟩

def matrixShear (pivot : Fin d) (bank : Fin 35 ↪ Fin T)
    (col : Fin d := k) (row : Fin d := Equiv.swap k pivot t) : Pr P T 217 A U :=
  .seq (readColumnPair col row pivot (matrixReadPorts.trans bank))
    (pivotShear k t b ((Fin.castLEEmb (by decide)).trans bank))

theorem matrixShear_exec (hk : k < t) (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (pivot col row : Fin d)
    (hb : b.Prime) (unit : IsUnit (matrix pivot col)) (body : P → Pr P T 217 A U)
    (bank : Fin 35 ↪ Fin T) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T 217 A U) (S : Stacks T A)
    (base : S.R (bank 2) = binSyms H M) (one : S.R (bank 28) = binSyms 1 1)
    (width : S.R (bank 27) = binSyms J W) (coeffBlank : S.R (bank 0) = [])
    (tail : List (Fin (A+4))) (packed : S.R (bank 34) = matrixWords A H matrix ++ tail)
    (entryBlank : S.R (bank 29) = []) (pivotBlank : S.R (bank 31) = [])
    (paddedOne : S.R (bank 32) = binSyms H (1 : ZMod M).val)
    (ticks : (S.R (bank 33)).length = w) (blankInv : S.R (bank 30) = [])
    (free : ∀ i : Fin 35, 1 ≤ i → i ≤ 26 → i ≠ 2 → i ≠ 24 → i ≠ 25 → S.R (bank i) = [])
    (left : ∀ i : Fin 12, i < 10 → S.L (bank ((Fin.castLEEmb (by decide : 29 ≤ 35)) (shearTranslation i))) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (a : Fin (M^d*W) → Fin 4)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn a) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    ∃ z F n, z.user = v.user ∧ n ≤ (8*((pivot.val*d+col.val)*H)+14*H+22 + (8*((row.val*d+col.val)*H)+14*H+22)) + pivotShearTime (W := W) k t b w H J ∧
      Exec body (matrixShear k t b pivot bank col row) (mk v S) n (mk z F) ∧
      PrefixCopyReady (bank 13) (bank 3) (bank 4) (bank 5) (t.val*H+1) (prefixSize (Q := M) t) F ∧
      ShearCounters (suffixSize (Q := M) (W := W) t) M (bank ∘ (Fin.castLEEmb (by decide : 29 ≤ 35)) ∘ shearTranslation) F ∧
      (∀ pos : ℤ, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-(p+(M^d*W : ℕ))) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn a) pos)) ∧
      (∀ pos : ℤ, pos < q ∨ q+(M^d*W : ℕ) ≤ pos →
        readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-(q+(M^d*W : ℕ))) =
          RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∀ (x : Fin d → ZMod M) (j : Fin W),
        let y := (RowOp.shear k t hk (matrix row col * Ring.inverse (matrix pivot col))).apply x
        readAt blank (F.L (bank 25)) (F.R (bank 25)) (((index y j).val : ℤ) - (M^d*W : ℕ)) =
          RadixToBinary.binaryEncoding.encode (a (index x j)) := by
  have fresh (i : Fin 8) (h1 : i ≠ 1) (h2 : i ≠ 2) : S.R (bank (matrixReadPorts i)) = [] := by
    fin_cases i <;> first | contradiction | exact coeffBlank | exact pivotBlank | exact entryBlank |
      exact free _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨u,hu,read⟩ := readColumnPair_exec body (matrixReadPorts.trans bank) matrix col row pivot H v S
    tail packed (by change (S.R (bank 2)).length = H; simp [base,length_binSyms]) fresh
  let D : Stacks T A := {S with R := Function.update (Function.update S.R (bank 31)
    (binSyms H (matrix pivot col).val)) (bank 29) (binSyms H (matrix row col).val)}
  have keep (i : Fin 35) (h : i ≠ 29) (h' : i ≠ 31) : D.R (bank i) = S.R (bank i) :=
    (Function.update_of_ne (bank.injective.ne h) _ _).trans (Function.update_of_ne (bank.injective.ne h') _ _)
  let ports : Fin 34 ↪ Fin 35 := Fin.castLEEmb (by decide)
  obtain ⟨z,F,n,hz,hn,run,result⟩ := pivotShear_exec k t b w hk matrix pivot col row hb unit body (ports.trans bank)
    H J hm hw hW u D ((keep 2 (by decide) (by decide)).trans base)
    ((keep 28 (by decide) (by decide)).trans one) ((keep 27 (by decide) (by decide)).trans width)
    ((keep 0 (by decide) (by decide)).trans coeffBlank)
    (by change D.R (bank 29) = _; simp [D]) (by change D.R (bank 31) = _; simp [D,bank.injective.eq_iff])
    ((keep 32 (by decide) (by decide)).trans paddedOne)
    (by change (D.R (bank 33)).length = w; rw [keep 33 (by decide) (by decide),ticks])
    ((keep 30 (by decide) (by decide)).trans blankInv)
    (by
      intro i lo hi h2 h24 h25
      apply (keep (ports i) _ _).trans (free _ lo hi (fun h => h2 (ports.injective h))
        (fun h => h24 (ports.injective h)) (fun h => h25 (ports.injective h)))
      all_goals intro eq; have e := congrArg Fin.val eq; change i.val = _ at e; omega)
    left source dest p q a
    (by change ∀ j, _ = readAt blank _ (D.R (bank 24)) _; rw [keep 24 (by decide) (by decide)]; exact src)
    (by change ∀ j, _ = readAt blank _ (D.R (bank 25)) _; rw [keep 25 (by decide) (by decide)]; exact dst)
  exact ⟨z,F,_,hz.trans hu,Nat.add_le_add_left hn _,Exec.seq read run,result⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
