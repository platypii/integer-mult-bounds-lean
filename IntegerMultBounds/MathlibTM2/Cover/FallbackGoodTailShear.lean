module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodTailAdapter

/-! Execute a reversed row addition from the pivot reciprocal and the archived upper row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout LabelTraversal GoodForm
variable {P U α : Type} {T A d M W : ℕ} [NeZero M]

def tailShearAt (k i : Fin d) {n : ℕ} (src dst : Fin n) (coeff : Fin 14 ↪ Fin T) (bank : Fin 29 ↪ Fin T) : Pr P T 217 A U :=
  .seq (weightedEntry (k.val*d+i.val) coeff)
    (embProg bank Empty.elim (weightedShear src dst (Function.Embedding.refl _)))

theorem tailShearAt_exec (body : P → Pr P T 217 A U) (G : Matrix (Fin d) (Fin d) (ZMod M))
    (rank : ℕ) (hr : rank ≤ d) (minor : ∀ n (hn : n < rank), IsUnit (lead (n+1) (lt_of_lt_of_le hn hr) G).det)
    (a : Fin rank) (i : Fin d) (lt : a.castLE hr < i) (negative : Bool)
    {dim : ℕ} (r t : Fin dim) (hrt : r < t)
    (coeff : Fin 14 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (shared : coeff 3 = bank 0)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T 217 A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (modulus : S.R (coeff 2) = binSyms H M)
    (work : ∀ j : Fin 14, j = 1 ∨ 4 ≤ j ∧ j < 12 → S.R (coeff j) = [])
    (fresh : S.R (bank 0) = [])
    (base : S.R (bank 2) = binSyms H M)
    (one : S.R (bank 28) = binSyms 1 1) (width : S.R (bank 27) = binSyms J W)
    (free : ∀ j : Fin 29, 1 ≤ j → j ≤ 26 → j ≠ 2 → j ≠ 24 → j ≠ 25 → S.R (bank j) = [])
    (left : ∀ j : Fin 12, j < 10 → S.L (bank (shearTranslation j)) = [])
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^dim*W) → α)
    (empty : ∀ z, q ≤ z → z < q+(M^dim*W : ℕ) → dest z = blank)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ word)) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    let k := a.castLE hr
    let stage := (stageAt G rank hr minor a.val a.isLt.le).M
    let pivotInv := Ring.inverse ((stageAt G rank hr minor rank le_rfl).M k k)
    let entry := elimU k stage (Ring.inverse (stage k k)) i
    let c := if negative then -entry else entry
    S.R (coeff 13) = matrixWords A H stage ++ tail →
    S.R (coeff 0) = binSyms H (if negative then -pivotInv else pivotInv).val →
    ∃ z F n, z.user = v.user ∧ n ≤ (8*((k.val*d+i.val)*H)+48*H*H+166*H+88) +
      weightedShearTime r t M W H J ∧ Exec body (tailShearAt k i r t coeff bank) (mk v S) n (mk z F) ∧
      (∀ j, (∀ a, bank a ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      F.R (bank 2) = S.R (bank 2) ∧ (∀ j : Fin 29, 27 ≤ j → F.R (bank j) = S.R (bank j)) ∧
      (∀ pos, readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-q) = RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∃ out : Fin (M^dim*W) → α, (∀ pos, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ out)) pos)) ∧
        ∀ x j, out (index ((RowOp.shear r t hrt c).apply x) j) = word (index x j) := by
  intro k stage pivotInv entry c matrix pivot
  let weight := if negative then -pivotInv else pivotInv
  obtain ⟨u,l,hu,ht,load⟩ := weightedEntry_writes body coeff stage k i weight H hm tail v S
    ⟨matrix,pivot,modulus,work⟩
  have diag : (stageAt G rank hr minor rank le_rfl).M k k = stage k k :=
    archivedPivot_eq G rank hr minor a rank le_rfl a.isLt.le
  have ne : i ≠ k := lt.ne'
  have value : weight * stage k i = c := by
    cases negative <;> simp [weight,c,entry,pivotInv,diag,elimU,ne]
  rw [shared,fresh,List.append_nil,value] at load
  exact loadedShear_exec body r t hrt c bank _ _ H J hm hw hW v S
    ⟨u,l,hu,ht,load⟩ base one width free left sym source dest p q word empty src dst

/-- Shifting the two physical ports into the suffix performs one tail shear
across every head address in the same pass. -/
theorem tailShear_append {R : Type*} [CommRing R] {a : ℕ} (i k : Fin d) (lt : i < k) (c : R)
    (x : Fin a → R) (y : Fin d → R) :
    (RowOp.shear (i.natAdd a) (k.natAdd a) (by simpa using lt) c).apply (Fin.append x y) =
      Fin.append x ((RowOp.shear i k lt c).apply y) := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun r => ?_) j
  · have ne : l.castAdd d ≠ k.natAdd a := by
      intro eq
      have := congrArg Fin.val eq
      simp only [Fin.val_castAdd,Fin.val_natAdd] at this
      omega
    simp [RowOp.apply,Function.update_of_ne ne]
  · by_cases eq : r = k
    · subst r; simp [RowOp.apply]
    · have ne : r.natAdd a ≠ k.natAdd a := by simpa using eq
      simp [RowOp.apply,Function.update_of_ne ne,Function.update_of_ne eq]

def goodTailShear (k i : Fin d) (coeff : Fin 14 ↪ Fin T) (bank : Fin 29 ↪ Fin T) : Pr P T 217 A U :=
  tailShearAt k i i.rev k.rev coeff bank

theorem goodTailShear_exec (body : P → Pr P T 217 A U) (G : Matrix (Fin d) (Fin d) (ZMod M))
    (rank : ℕ) (hr : rank ≤ d) (minor : ∀ n (hn : n < rank), IsUnit (lead (n+1) (lt_of_lt_of_le hn hr) G).det)
    (a : Fin rank) (i : Fin d) (lt : a.castLE hr < i) (negative : Bool)
    (coeff : Fin 14 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (shared : coeff 3 = bank 0)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T 217 A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (modulus : S.R (coeff 2) = binSyms H M)
    (work : ∀ j : Fin 14, j = 1 ∨ 4 ≤ j ∧ j < 12 → S.R (coeff j) = [])
    (fresh : S.R (bank 0) = [])
    (base : S.R (bank 2) = binSyms H M)
    (one : S.R (bank 28) = binSyms 1 1) (width : S.R (bank 27) = binSyms J W)
    (free : ∀ j : Fin 29, 1 ≤ j → j ≤ 26 → j ≠ 2 → j ≠ 24 → j ≠ 25 → S.R (bank j) = [])
    (left : ∀ j : Fin 12, j < 10 → S.L (bank (shearTranslation j)) = [])
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^d*W) → α)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ word)) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    let k := a.castLE hr
    let stage := (stageAt G rank hr minor a.val a.isLt.le).M
    let pivotInv := Ring.inverse ((stageAt G rank hr minor rank le_rfl).M k k)
    let entry := elimU k stage (Ring.inverse (stage k k)) i
    let c := if negative then -entry else entry
    S.R (coeff 13) = matrixWords A H stage ++ tail →
    S.R (coeff 0) = binSyms H (if negative then -pivotInv else pivotInv).val →
    ∃ z F n, z.user = v.user ∧ n ≤ (8*((k.val*d+i.val)*H)+48*H*H+166*H+88) +
      weightedShearTime i.rev k.rev M W H J ∧ Exec body (goodTailShear k i coeff bank) (mk v S) n (mk z F) ∧
      (∀ j, (∀ a, bank a ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      F.R (bank 2) = S.R (bank 2) ∧ (∀ j : Fin 29, 27 ≤ j → F.R (bank j) = S.R (bank j)) ∧
      (∀ pos, readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-q) = RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∃ out : Fin (M^d*W) → α, (∀ pos, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ out)) pos)) ∧
        ∀ x j, out (index ((RowOp.shear i.rev k.rev (Fin.rev_lt_rev.mpr lt) c).apply x) j) = word (index x j) := by
  exact tailShearAt_exec body G rank hr minor a i lt negative i.rev (a.castLE hr).rev
    (Fin.rev_lt_rev.mpr lt) coeff bank shared H J hm hw hW v S tail modulus work fresh base one width
    free left sym source dest p q word empty src dst

end IntegerMultBounds.MathlibTM2.Cover.Fallback
