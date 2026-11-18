module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotStream
public import IntegerMultBounds.MathlibTM2.Cover.FallbackMatrixShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearReturn
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet
import IntegerMultBounds.Machine.BinaryDivide

/-! Read the reverse pivot from tape and apply its lower shear to the payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout
variable {T A d W : ℕ} {P U : Type} (k t : Fin d) (b w : ℕ) [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

/-- Pull the source word back by the inverse shear to describe every output cell. -/
private theorem shear_output_word {α β : Type*} (encode : α → β) {m : ℕ} [NeZero m] (hk : k < t) (c : ZMod m)
    (a : Fin (m^d*W) → α) (read : Fin (m^d*W) → β)
    (cells : ∀ x j, read (index ((RowOp.shear k t hk c).apply x) j) =
      encode (a (index x j))) :
    ∃ word : Fin (m^d*W) → α,
      (∀ n, read n = encode (word n)) ∧
      ∀ x j, word (index ((RowOp.shear k t hk c).apply x) j) = a (index x j) := by
  let undo := fun x : Fin d → ZMod m => Function.update x t (x t-c*x k)
  have cancel (x : Fin d → ZMod m) : undo ((RowOp.shear k t hk c).apply x) = x := by
    ext i
    by_cases h : i = t <;> simp [h,undo,RowOp.apply,hk.ne]
  have restore (x : Fin d → ZMod m) : (RowOp.shear k t hk c).apply (undo x) = x := by
    ext i
    by_cases h : i = t <;> simp [h,undo,RowOp.apply,hk.ne]
  let word := fun n : Fin (m^d*W) =>
    let part := finProdFinEquiv.symm n
    a (index (undo (coordinates part.1)) part.2)
  have atIndex (x : Fin d → ZMod m) (j : Fin W) : word (index x j) = a (index (undo x) j) := by
    simp only [word,index,Equiv.symm_apply_apply,coordinates_rank]
  refine ⟨word,?_,fun x j => by rw [atIndex,cancel]⟩
  intro n
  obtain ⟨⟨r,j⟩,rfl⟩ := finProdFinEquiv.surjective n
  have eq : finProdFinEquiv (r,j) = index (coordinates r : Fin d → ZMod m) j := by simp [index]
  rw [eq,atIndex]
  simpa only [restore] using cells (undo (coordinates r)) j

/-- For an upper addition the caller exchanges the two fields before and after the shear.
The archived coefficient always comes from the original elimination column. -/
theorem reverseMatrixShear_exec {α : Type*} (sym : α → Fin 4) (col target : Fin d) (hk : k < t) (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (rows : Fin d → Fin d)
    (hb : b.Prime) (unit : IsUnit (matrix (rows col) col)) (body : P → Pr P T 217 A U)
    (bank : Fin 35 ↪ Fin T) (stream : Fin T) (apart : ∀ i, bank i ≠ stream) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T 217 A U) (S : Stacks T A)
    (rest : List (Fin (A+4)))
    (code : S.R stream = orderedScheduleCode (((List.finRange d).take (col.val+1)).reverse) rows ++ rest)
    (base : S.R (bank 2) = binSyms H M) (one : S.R (bank 28) = binSyms 1 1)
    (width : S.R (bank 27) = binSyms J W) (coeffBlank : S.R (bank 0) = [])
    (tail : List (Fin (A+4))) (packed : S.R (bank 34) = matrixWords A H matrix ++ tail)
    (entryBlank : S.R (bank 29) = []) (pivotBlank : S.R (bank 31) = [])
    (paddedOne : S.R (bank 32) = binSyms H (1 : ZMod M).val)
    (ticks : (S.R (bank 33)).length = w) (blankInv : S.R (bank 30) = [])
    (free : ∀ i : Fin 35, 1 ≤ i → i ≤ 26 → i ≠ 2 → i ≠ 24 → i ≠ 25 → S.R (bank i) = [])
    (left : ∀ i : Fin 12, i < 10 → S.L (bank ((Fin.castLEEmb (by decide : 29 ≤ 35)) (shearTranslation i))) = [])
    (source dest : ℤ → Fin 4) (p q : ℤ) (a : Fin (M^d*W) → α)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ a)) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    ∃ z F n, z.user = v.user ∧ n ≤ (2*((rows col).val+1) + ((8*(((rows col).val*d+col.val)*H)+14*H+22 + (8*(((Equiv.swap col (rows col) target).val*d+col.val)*H)+14*H+22)) + pivotShearTime (W := W) k t b w H J)) + (10*(t.val*H+1)+12+((327*(M^d*W)+2)*13+6)) ∧
      Exec body (.seq (selectPivot stream (fun i => matrixShear k t b i bank col (Equiv.swap col i target)) (List.finRange d))
        (finishShear ((Fin.castLEEmb (by decide)).trans bank))) (mk v S) n (mk z F) ∧
      (∀ pos, readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-q) = RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∃ word : Fin (M^d*W) → α,
        (∀ pos, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-p) =
          RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ word)) pos)) ∧
        ∀ (x : Fin d → ZMod M) (j : Fin W),
          let y := (RowOp.shear k t hk (matrix (Equiv.swap col (rows col) target) col * Ring.inverse (matrix (rows col) col))).apply x
          word (index y j) = a (index x j) := by
  let D : Stacks T A := {S with R := Function.update S.R stream (orderedScheduleCode (((List.finRange d).take col.val).reverse) rows ++ rest)}
  have keep (i) : D.R (bank i) = S.R (bank i) := Function.update_of_ne (apart i) _ _
  obtain ⟨z,F,n,hz,hn,run,prefixReady,counters,sourceTape,frame,effect⟩ := matrixShear_exec k t b w hk matrix (rows col) col (Equiv.swap col (rows col) target) hb unit body bank H J hm hw hW
    {v with flag := false} D (by rwa [keep]) (by rwa [keep]) (by rwa [keep]) (by rwa [keep]) tail
    (by rwa [keep]) (by rwa [keep]) (by rwa [keep]) (by rwa [keep]) (by rwa [keep]) (by rwa [keep])
    (fun i a c e f g => (keep i).trans (free i a c e f g)) left source dest p q (sym ∘ a)
    (by simpa only [keep] using src) (by simpa only [keep] using dst)
  obtain ⟨word,cells,perm⟩ := shear_output_word k t (RadixToBinary.binaryEncoding.encode ∘ sym) hk
    (matrix (Equiv.swap col (rows col) target) col * Ring.inverse (matrix (rows col) col)) a
    (fun n => readAt blank (F.L (bank 25)) (F.R (bank 25)) ((n.val : ℤ) - (M^d*W : ℕ))) effect
  have dispatch := reversePivot_exec body stream (fun i => matrixShear k t b i bank col (Equiv.swap col i target))
    rows col v S rest code run
  have out (pos : ℤ) : readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-(q+(M^d*W : ℕ))) =
      RadixToBinary.binaryEncoding.encode (putWord dest q (List.ofFn (sym ∘ word)) pos) := by
    by_cases outsideWord : pos < q ∨ q+(M^d*W : ℕ) ≤ pos
    · rw [putWord_outside _ _ _ _ (by simpa using outsideWord)]
      exact frame pos outsideWord
    · let i : Fin (M^d*W) := ⟨(pos-q).toNat,by omega⟩
      have addr : pos = q+i.val := by dsimp [i]; omega
      rw [addr,BinaryDivide.putWord_getElem _ _ _ i.val (by simp),List.getElem_ofFn]
      simpa only [Function.comp_apply,add_sub_add_left_eq_sub] using cells i
  let ports : Fin 29 ↪ Fin T := (Fin.castLEEmb (by decide : 29 ≤ 35)).trans bank
  open RowPaddingConstructedAlphabet in
  obtain ⟨u,G,l,hu,hl,finish,result,clean⟩ := finishShear_exec body ports t hW
    (mapTape source) (mapTape dest) p q (mapArray (sym ∘ a)) (mapArray (sym ∘ word))
    (by intro pos lo hi; change RadixToBinary.binaryEncoding.encode (dest pos) = _; rw [empty pos lo hi]; rfl)
    _ z F prefixReady counters
    (fun pos => (out pos).trans (congrFun (map_array_word dest q (sym ∘ word)) pos))
    (fun pos => (sourceTape pos).trans (congrFun (map_array_word source p (sym ∘ a)) pos))
  exact ⟨u,G,_,hu.trans hz,Nat.add_le_add (Nat.add_le_add_left hn _) hl,Exec.seq dispatch finish,
    clean,word,fun pos => (result pos).trans (congrFun (RowPaddingConstructedAlphabet.map_array_word source p (sym ∘ word)) pos).symm,perm⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
