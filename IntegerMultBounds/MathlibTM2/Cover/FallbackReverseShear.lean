module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackMatrixShear
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearCleanup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearReturn
import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet
import IntegerMultBounds.Machine.BinaryDivide

/-! Apply a selected pivot shear and return the word to its original role tape. -/
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

def shearAndReturn (col target pivot : Fin d) (bank : Fin 35 ↪ Fin T) : Pr P T 217 A U :=
  .seq (matrixShear k t b pivot bank col (Equiv.swap col pivot target))
    (finishShear ((Fin.castLEEmb (by decide)).trans bank))

/-- A single push bound for all physical row shears in the fixed dimension.
The compiled instructions are independent of the modulus precision and payload width. -/
noncomputable def shearPushBound [Fintype P] (d b : ℕ) (bank : Fin 35 ↪ Fin T)
    (body : P → Pr P T 217 A U) : ℕ :=
  max (Fast.Main.mnPushC body) (Finset.univ.sup fun ix : Fin 5 → Fin d =>
    Fast.Main.mnProgPush (shearAndReturn (P := P) (A := A) (U := U) (ix 0) (ix 1) b (ix 2) (ix 3) (ix 4) bank))

theorem shear_cleanup_time [Fintype P] (col target pivot : Fin d) (bank : Fin 35 ↪ Fin T)
    (body : P → Pr P T 217 A U) {v u : HS T 217 A U} {S G : Stacks T A} {n : ℕ}
    (run : Exec body (shearAndReturn k t b col target pivot bank) (mk v S) n (mk u G)) :
    let tapes := shearWork.map bank
    n+((tapes.map fun i => 4*(G.L i).length+2*(G.R i).length+4).sum+1) ≤
      (tapes.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum+1+
        (1+6*shearWork.length*shearPushBound d b bank body)*n := by
  intro tapes
  let push := shearPushBound d b bank body
  have prog : Fast.Main.mnProgPush (shearAndReturn k t b col target pivot bank : Pr P T 217 A U) ≤ push :=
    (Finset.le_sup (f := fun ix : Fin 5 → Fin d =>
      Fast.Main.mnProgPush (shearAndReturn (P := P) (A := A) (U := U) (ix 0) (ix 1) b (ix 2) (ix 3) (ix 4) bank))
      (Finset.mem_univ ![k,t,col,target,pivot])).trans (le_max_right ..)
  have bound := cleanup_cost_le tapes run prog (fun f => (Fast.Main.mn_progPush_le_pushC body f).trans (le_max_left ..))
  rw [show tapes.length = shearWork.length by simp [tapes]] at bound
  change _ ≤ _ + (1+6*shearWork.length*push)*n
  nlinarith only [bound]

/-- After the preceding row has cleared its work tapes, no previous row contributes
to the running time of this one. -/
theorem shear_cleanup_time_of_empty [Fintype P] (col target pivot : Fin d) (bank : Fin 35 ↪ Fin T)
    (body : P → Pr P T 217 A U) {v u : HS T 217 A U} {S G : Stacks T A} {n limit : ℕ}
    (run : Exec body (shearAndReturn k t b col target pivot bank) (mk v S) n (mk u G))
    (time : n ≤ limit) (empty : ∀ i ∈ shearWork.map bank, S.L i = [] ∧ S.R i = []) :
    n+(((shearWork.map bank).map fun i => 4*(G.L i).length+2*(G.R i).length+4).sum+1) ≤
      4*shearWork.length+1+(1+6*shearWork.length*shearPushBound d b bank body)*limit := by
  have cost := shear_cleanup_time k t b col target pivot bank body run
  have init : ((shearWork.map bank).map fun i => 4*(S.L i).length+2*(S.R i).length+4) =
      (shearWork.map bank).map (fun _ => 4) := by
    apply List.map_congr_left
    intro i hi
    simp [(empty i hi).1,(empty i hi).2]
  simp only [init,List.map_const',List.length_map,List.sum_replicate_nat] at cost
  exact cost.trans (by rw [Nat.mul_comm 4 shearWork.length]; gcongr)

def reverseMatrixShear (col target pivot : Fin d) (bank : Fin 35 ↪ Fin T) : Pr P T 217 A U :=
  .seq (shearAndReturn k t b col target pivot bank) (clearWorkTapes (shearWork.map bank))

/-- For an upper addition the caller exchanges the two fields before and after the shear.
The archived coefficient always comes from the original elimination column. -/
theorem reverseMatrixShear_exec {α : Type*} (sym : α → Fin 4) (col target : Fin d) (hk : k < t) (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (pivot : Fin d)
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
    (source dest : ℤ → Fin 4) (p q : ℤ) (a : Fin (M^d*W) → α)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ a)) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    ∃ u G n z F, z.user = v.user ∧ n ≤ ((8*((pivot.val*d+col.val)*H)+14*H+22 + (8*(((Equiv.swap col pivot target).val*d+col.val)*H)+14*H+22)) + pivotShearTime (W := W) k t b w H J) + (10*(t.val*H+1)+12+((327*(M^d*W)+2)*13+6)) ∧
      Exec body (shearAndReturn k t b col target pivot bank) (mk v S) n (mk u G) ∧
      Exec body (reverseMatrixShear k t b col target pivot bank) (mk v S)
        (n+(((shearWork.map bank).map fun i => 4*(G.L i).length+2*(G.R i).length+4).sum+1)) (mk z F) ∧
      F.R (bank 34) = S.R (bank 34) ∧
      (∀ i : Fin 35, (i ≤ 26 ∧ i ≠ 2 ∧ i ≠ 24 ∧ i ≠ 25) ∨ (29 ≤ i ∧ i ≤ 31) →
        F.L (bank i) = [] ∧ F.R (bank i) = []) ∧
      (∀ pos, readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-q) = RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∃ word : Fin (M^d*W) → α,
        (∀ pos, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-p) =
          RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ word)) pos)) ∧
        ∀ (x : Fin d → ZMod M) (j : Fin W),
          let y := (RowOp.shear k t hk (matrix (Equiv.swap col pivot target) col * Ring.inverse (matrix pivot col))).apply x
          word (index y j) = a (index x j) := by
  obtain ⟨z,F,n,hz,hn,run,archive,prefixReady,counters,sourceTape,frame,effect⟩ := matrixShear_exec k t b w hk matrix pivot col (Equiv.swap col pivot target) hb unit body bank H J hm hw hW
    v S base one width coeffBlank tail packed entryBlank pivotBlank paddedOne ticks blankInv free left
    source dest p q (sym ∘ a) src dst
  obtain ⟨word,cells,perm⟩ := shear_output_word k t (RadixToBinary.binaryEncoding.encode ∘ sym) hk
    (matrix (Equiv.swap col pivot target) col * Ring.inverse (matrix pivot col)) a
    (fun n => readAt blank (F.L (bank 25)) (F.R (bank 25)) ((n.val : ℤ) - (M^d*W : ℕ))) effect
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
  obtain ⟨u,G,l,hu,hl,finish,result,clean,retFrame⟩ := finishShear_exec body ports t hW
    (mapTape source) (mapTape dest) p q (mapArray (sym ∘ a)) (mapArray (sym ∘ word))
    (by intro pos lo hi; change RadixToBinary.binaryEncoding.encode (dest pos) = _; rw [empty pos lo hi]; rfl)
    _ z F prefixReady counters
    (fun pos => (out pos).trans (congrFun (map_array_word dest q (sym ∘ word)) pos))
    (fun pos => (sourceTape pos).trans (congrFun (map_array_word source p (sym ∘ a)) pos))
  obtain ⟨y,D,hy,clear,freeD,frameD⟩ := clearShear_exec body bank u G
  have keep (i : Fin 35) (hi : i ∉ shearWork) := frameD (bank i) (by
    simpa only [List.mem_map,bank.injective.eq_iff,exists_eq_right] using hi)
  have srcKeep := keep 24 (by decide)
  have dstKeep := keep 25 (by decide)
  refine ⟨u,G,_,y,D,hy.trans (hu.trans hz),Nat.add_le_add hn hl,Exec.seq run finish,
    Exec.seq (Exec.seq run finish) clear,?_,freeD,?_,word,?_,perm⟩
  · apply (keep 34 (by decide)).2.trans
    apply Eq.trans _ archive
    apply retFrame
    intro i
    apply bank.injective.ne
    intro h
    have e := congrArg Fin.val h
    change i.val = 34 at e
    omega
  · intro pos
    rw [dstKeep.1,dstKeep.2]
    exact clean pos
  · intro pos
    rw [srcKeep.1,srcKeep.2]
    exact (result pos).trans (congrFun (RowPaddingConstructedAlphabet.map_array_word source p (sym ∘ word)) pos).symm

end IntegerMultBounds.MathlibTM2.Cover.Fallback
