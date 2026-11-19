module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearCleanup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodAdapter
public import IntegerMultBounds.MathlibTM2.Cover.FallbackWeightedEntry
public import IntegerMultBounds.MathlibTM2.Cover.FallbackWeightedShear

/-! Run one head-adapter shear from an archived elimination entry, the row
weight and the signed reciprocal of the pivot's child weight. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host FlatCoordinateLayout LabelTraversal
variable {P U α : Type} {T Q A d M W : ℕ} [NeZero M]

open GoodForm in
/-- The packed final pivot at coordinate k is the pivot actually used when
the elimination archive was at stage k. -/
theorem archivedPivot_eq {R : Type*} [CommRing R] (G : Matrix (Fin d) (Fin d) R)
    (rank : ℕ) (hr : rank ≤ d) (minor : ∀ n (hn : n < rank),
      IsUnit (lead (n+1) (lt_of_lt_of_le hn hr) G).det) (k : Fin rank) (n : ℕ)
    (hn : n ≤ rank) (lo : k.val ≤ n) :
    let i := k.castLE hr
    (stageAt G rank hr minor n hn).M i i = (stageAt G rank hr minor k.val k.isLt.le).M i i := by
  intro i
  have same (a b : ℕ) (ha : a ≤ rank) (hb : b ≤ rank) (eq : a = b) :
      (stageAt G rank hr minor a ha).M i i = (stageAt G rank hr minor b hb).M i i := by subst b; rfl
  induction n with
  | zero =>
    have eq : k.val = 0 := by omega
    exact same _ _ _ _ eq.symm
  | succ n ih =>
    by_cases eq : k.val = n+1
    · exact same _ _ _ _ eq.symm
    · let S := stageAt G rank hr minor n (by omega)
      let p : Fin d := ⟨n,lt_of_lt_of_le hn hr⟩
      change elimM p S.M (Ring.inverse (S.M p p)) i i = _
      rw [elim_diag p S.cleared _ i (by change k.val < n+1; omega)]
      exact ih (by omega) (by omega)

open GoodForm in
/-- The sign chooses the incoming shear or its outgoing inverse. Both use
the reciprocal read from the final child-weight tape. -/
theorem goodHeadCoefficient_eq {R : Type*} [CommRing R] (G : Matrix (Fin d) (Fin d) R)
    (rank : ℕ) (hr : rank ≤ d) (minor : ∀ n (hn : n < rank),
      IsUnit (lead (n+1) (lt_of_lt_of_le hn hr) G).det) (k : Fin rank) (i : Fin d)
    (α α' : Fin d → R) (negative : Bool) :
    let p := k.castLE hr
    let stage := (stageAt G rank hr minor k.val k.isLt.le).M
    let pivot := (stageAt G rank hr minor rank le_rfl).M p p
    let reciprocal := α' p * Ring.inverse pivot
    let c := α i * (stage i p * Ring.inverse (stage p p)) * α' p
    α i * stage i p * (if negative then -reciprocal else reciprocal) = if negative then -c else c := by
  dsimp only
  rw [archivedPivot_eq G rank hr minor k rank le_rfl k.isLt.le]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring

def headScalePorts : Fin 13 ↪ Fin 16 := ⟨![14,3,2,15,4,5,6,7,8,9,10,11,12],by decide⟩

def headCoefficient (offset : ℕ) (bank : Fin 16 ↪ Fin T) : Pr P T Q A U :=
  scaleEntry (weightedEntry offset ((Fin.castLEEmb (by decide)).trans bank)) (headScalePorts.trans bank)

theorem headCoefficient_writes (body : P → Pr P T Q A U) (bank : Fin 16 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (k i : Fin d) (rowWeight pivotInv : ZMod M)
    (H : ℕ) (hm : M < 2^H) (tail : List (Fin (A+4))) :
    Writes body (fun R => R (bank 13) = matrixWords A H G ++ tail ∧
      R (bank 0) = binSyms H rowWeight.val ∧ R (bank 14) = binSyms H pivotInv.val ∧
      R (bank 2) = binSyms H M ∧ ∀ j : Fin 16, j = 1 ∨ 3 ≤ j ∧ j ≤ 11 → R (bank j) = [])
      (bank 15) (headCoefficient (i.val*d+k.val) bank) (binSyms H (rowWeight*G i k*pivotInv).val)
      (8*((i.val*d+k.val)*H)+96*H*H+318*H+154) := by
  intro v S ⟨matrix,row,pivot,modulus,free⟩
  let read := (Fin.castLEEmb (by decide : 14 ≤ 16)).trans bank
  have first := weightedEntry_writes body read G i k rowWeight H hm tail
  have emit := scaleEntry_writes body (headScalePorts.trans bank) _ _ (rowWeight*G i k) pivotInv H _ hm first
  have small : ∀ j : Fin 14, j = 1 ∨ 4 ≤ j ∧ j < 12 →
      j.castLE (by decide : 14 ≤ 16) = 1 ∨ 3 ≤ j.val ∧ j.val ≤ 11 := by decide
  have work : ∀ j : Fin 13, j = 1 ∨ 4 ≤ j ∧ j < 12 →
      headScalePorts j = 1 ∨ 3 ≤ headScalePorts j ∧ headScalePorts j ≤ 11 := by decide
  obtain ⟨z,l,user,time,run⟩ := emit v S
    ⟨⟨matrix,row,modulus,fun j h => free _ (small j h)⟩,pivot,modulus,fun j h => free _ (work j h)⟩
  rw [mul_comm pivotInv] at run
  exact ⟨z,l,user,by nlinarith only [time],run⟩

def headParentRead : Fin 7 ↪ Fin 17 := ⟨![1,2,16,0,4,5,6],by decide⟩

def packedHeadCoefficient (row offset : ℕ) (bank : Fin 17 ↪ Fin T) : Pr P T Q A U :=
  .seq (readMatrixWord row (headParentRead.trans bank))
    (.seq (headCoefficient offset ((Fin.castLEEmb (by decide)).trans bank)) (bclear (bank 0)))

theorem packedHeadCoefficient_writes (body : P → Pr P T Q A U) (bank : Fin 17 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (k i : Fin d) (weights : Fin d → ZMod M)
    (pivotInv : ZMod M) (H : ℕ) (hm : M < 2^H) (tail rest : List (Fin (A+4))) :
    Writes body (fun R => R (bank 13) = matrixWords A H G ++ tail ∧
      R (bank 16) = (List.ofFn fun j => binSyms H (weights j).val).flatten ++ rest ∧
      R (bank 14) = binSyms H pivotInv.val ∧ R (bank 2) = binSyms H M ∧
      ∀ j : Fin 17, j ≤ 1 ∨ 3 ≤ j ∧ j ≤ 11 → R (bank j) = [])
      (bank 15) (packedHeadCoefficient i.val (i.val*d+k.val) bank) (binSyms H (weights i*G i k*pivotInv).val)
      (8*(i.val*H)+14*H+22+(8*((i.val*d+k.val)*H)+96*H*H+318*H+154)+(2*H+2)) := by
  intro v S ⟨matrix,parent,pivot,modulus,free⟩
  let row : Matrix (Fin 1) (Fin d) (ZMod M) := fun _ j => weights j
  have small : ∀ j : Fin 7, j = 0 ∨ 4 ≤ j → headParentRead j ≤ 1 ∨ 3 ≤ headParentRead j ∧ headParentRead j ≤ 11 := by decide
  obtain ⟨u,hu,read⟩ := readMatrixWord_exec body (headParentRead.trans bank) row 0 i H v S rest
    (by change S.R (bank 16) = matrixWords A H row ++ rest; simpa only [matrixWords,row,List.ofFn_succ,List.ofFn_zero,List.flatten_cons,List.flatten_nil,List.append_nil] using parent)
    ((congrArg List.length modulus).trans (length_binSyms ..)) (fun j h => free _ (small j h))
  simp only [Fin.val_zero,Nat.zero_mul,Nat.zero_add] at read
  change Exec _ _ _ _ (mk u {S with R := Function.update S.R (bank 0) (_ ++ S.R (bank 0))}) at read
  rw [free 0 (by decide),List.append_nil] at read
  let D := {S with R := Function.update S.R (bank 0) (binSyms H (weights i).val)}
  have keep (j : Fin 17) (h : j ≠ 0) : D.R (bank j) = S.R (bank j) :=
    Function.update_of_ne (bank.injective.ne h) _ _
  have valid : ∀ j : Fin 16, j = 1 ∨ 3 ≤ j ∧ j ≤ 11 →
      let k := j.castLE (by decide : 16 ≤ 17)
      k ≠ 0 ∧ (k ≤ 1 ∨ 3 ≤ k ∧ k ≤ 11) := by decide
  obtain ⟨y,n,hy,ht,emit⟩ := headCoefficient_writes body ((Fin.castLEEmb (by decide)).trans bank) G k i
    (weights i) pivotInv H hm tail u D ⟨(keep 13 (by decide)).trans matrix,Function.update_self ..,
      (keep 14 (by decide)).trans pivot,(keep 2 (by decide)).trans modulus,
      fun j h => (keep _ (valid j h).1).trans (free _ (valid j h).2)⟩
  let word := binSyms (A := A) H (weights i*G i k*pivotInv).val ++ S.R (bank 15)
  let E := {D with R := Function.update D.R (bank 15) word}
  change Exec _ _ _ _ (mk y {D with R := Function.update D.R (bank 15) (_ ++ D.R (bank 15))}) at emit
  rw [keep 15 (by decide)] at emit
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (bank 0) y E
  have finish : Function.update E.R (bank 0) [] = Function.update S.R (bank 15) word := by
    funext j
    by_cases a : j = bank 0 <;> by_cases b : j = bank 15 <;>
      simp_all [E,D,Function.update_of_ne,bank.injective.eq_iff]
  refine ⟨z,_,hz.trans (hy.trans hu),?_,(Exec.seq read (Exec.seq emit clear)).cast rfl ?_⟩
  · simp [E,D,bank.injective.eq_iff,length_binSyms]
    omega
  · rw [← finish]

/-- Run an archived coefficient reader followed by a physical payload shear. -/
theorem loadedShear_exec (body : P → Pr P T 217 A U) (k i : Fin d) (lt : k < i)
    (c : ZMod M) (bank : Fin 29 ↪ Fin T) (reader : Pr P T 217 A U) (cost : ℕ)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T 217 A U) (S : Stacks T A)
    (loadWord : ∃ u l, u.user = v.user ∧ l ≤ cost ∧ Exec body reader (mk v S) l
      (mk u {S with R := Function.update S.R (bank 0) (binSyms H c.val)}))
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
    ∃ z F n, z.user = v.user ∧ n ≤ cost + weightedShearTime k i M W H J ∧
      Exec body (.seq reader (embProg bank Empty.elim (weightedShear k i (Function.Embedding.refl _)))) (mk v S) n (mk z F) ∧
      (∀ j, (∀ a, bank a ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      F.R (bank 2) = S.R (bank 2) ∧ (∀ j : Fin 29, 27 ≤ j → F.R (bank j) = S.R (bank j)) ∧
      (∀ pos, readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-q) = RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∃ out : Fin (M^d*W) → α, (∀ pos, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ out)) pos)) ∧
        ∀ x j, out (index ((RowOp.shear k i lt c).apply x) j) = word (index x j) := by
  obtain ⟨u,l,hu,ht,load⟩ := loadWord
  let D := {S with R := Function.update S.R (bank 0) (binSyms H c.val)}
  have keep (j : Fin 29) (h : j ≠ 0) : D.R (bank j) = S.R (bank j) :=
    Function.update_of_ne (bank.injective.ne h) _ _
  obtain ⟨z,F,t,hz,time,run,post⟩ := weightedShear_exec k i lt sym c (P := Empty) Empty.elim
    (Function.Embedding.refl _) H J hm hw hW (embDn bank u) (embStk bank D)
    ((keep 2 (by decide)).trans base) ((keep 28 (by decide)).trans one) ((keep 27 (by decide)).trans width)
    (Function.update_self ..) (fun j lo hi ne a b => (keep j (by omega)).trans (free j lo hi ne a b))
    left source dest p q word empty (by simpa only [embStk_L,embStk_R,Function.Embedding.refl_apply,keep 24 (by decide)] using src)
    (by simpa only [embStk_L,embStk_R,Function.Embedding.refl_apply,keep 25 (by decide)] using dst)
  obtain ⟨y,E,placed,_,hy,eq,frame⟩ := exec_emb (body' := body) (ι := Empty.elim)
    bank.injective (fun e => nomatch e) run u rfl D rfl
  rw [← eq] at post
  obtain ⟨modWord,headers,clean,out⟩ := post
  refine ⟨y,E,l+t,hy.trans (hz.trans hu),Nat.add_le_add ht time,Exec.seq load placed,?_,modWord.trans (keep 2 (by decide)),
    fun j h => (headers j h).trans (keep j (by omega)),clean,out⟩
  intro j outside
  exact ⟨(frame j outside).1,(frame j outside).2.trans (Function.update_of_ne (outside 0).symm _ _)⟩

def goodHeadShear (k i : Fin d) (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) : Pr P T 217 A U :=
  .seq (packedHeadCoefficient i.val (i.val*d+k.val) coeff) (embProg bank Empty.elim (weightedShear k i (Function.Embedding.refl _)))

open GoodForm in
theorem goodHeadShear_exec (body : P → Pr P T 217 A U) (G : Matrix (Fin d) (Fin d) (ZMod M))
    (rank : ℕ) (hr : rank ≤ d) (minor : ∀ n (hn : n < rank),
      IsUnit (lead (n+1) (lt_of_lt_of_le hn hr) G).det)
    (pivotIndex : Fin rank) (i : Fin d) (lt : pivotIndex.castLE hr < i)
    (αw αw' : Fin d → ZMod M) (negative : Bool)
    (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) (shared : coeff 15 = bank 0)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T 217 A U) (S : Stacks T A) (tail rest : List (Fin (A+4)))
    (modulus : S.R (coeff 2) = binSyms H M)
    (work : ∀ j : Fin 17, j ≤ 1 ∨ 3 ≤ j ∧ j ≤ 11 → S.R (coeff j) = [])
    (fresh : S.R (bank 0) = []) (base : S.R (bank 2) = binSyms H M)
    (one : S.R (bank 28) = binSyms 1 1) (width : S.R (bank 27) = binSyms J W)
    (free : ∀ j : Fin 29, 1 ≤ j → j ≤ 26 → j ≠ 2 → j ≠ 24 → j ≠ 25 → S.R (bank j) = [])
    (left : ∀ j : Fin 12, j < 10 → S.L (bank (shearTranslation j)) = [])
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^d*W) → α)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (src : ∀ z, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ word)) z) =
      readAt blank (S.L (bank 24)) (S.R (bank 24)) (z-p))
    (dst : ∀ z, RadixToBinary.binaryEncoding.encode (dest z) =
      readAt blank (S.L (bank 25)) (S.R (bank 25)) (z-q)) :
    let k := pivotIndex.castLE hr
    let stage := (stageAt G rank hr minor pivotIndex.val pivotIndex.isLt.le).M
    let finalPivot := (stageAt G rank hr minor rank le_rfl).M k k
    let childInv := αw' k * Ring.inverse finalPivot
    let reciprocal := if negative then -childInv else childInv
    S.R (coeff 13) = matrixWords A H stage ++ tail →
    S.R (coeff 16) = (List.ofFn fun j => binSyms H (αw j).val).flatten ++ rest → S.R (coeff 14) = binSyms H reciprocal.val →
    let product := αw i * (stage i k * Ring.inverse (stage k k)) * αw' k
    let c := if negative then -product else product
    ∃ z F n, z.user = v.user ∧ n ≤ (8*(i.val*H)+14*H+22+(8*((i.val*d+k.val)*H)+96*H*H+318*H+154)+(2*H+2)) +
      weightedShearTime k i M W H J ∧ Exec body (goodHeadShear k i coeff bank) (mk v S) n (mk z F) ∧
      (∀ j, (∀ a, bank a ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      F.R (bank 2) = S.R (bank 2) ∧ (∀ j : Fin 29, 27 ≤ j → F.R (bank j) = S.R (bank j)) ∧
      (∀ pos, readAt blank (F.L (bank 25)) (F.R (bank 25)) (pos-q) = RadixToBinary.binaryEncoding.encode (dest pos)) ∧
      ∃ out : Fin (M^d*W) → α, (∀ pos, readAt blank (F.L (bank 24)) (F.R (bank 24)) (pos-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ out)) pos)) ∧
        ∀ x j, out (index ((RowOp.shear k i lt c).apply x) j) = word (index x j) := by
  intro k stage finalPivot childInv reciprocal matrix row pivot product c
  have coefficient : αw i * stage i k * reciprocal = c :=
    goodHeadCoefficient_eq G rank hr minor pivotIndex i αw αw' negative
  obtain ⟨u,l,hu,ht,load⟩ := packedHeadCoefficient_writes body coeff stage k i αw reciprocal H hm tail rest v S
    ⟨matrix,row,pivot,modulus,work⟩
  rw [shared,fresh,List.append_nil,coefficient] at load
  exact loadedShear_exec body k i lt c bank _ _ H J hm hw hW v S ⟨u,l,hu,ht,load⟩
    base one width free left sym source dest p q word empty src dst

/-- The two payload tapes and three read-only headers survive between shears. -/
def headShearWork : List (Fin 29) :=
  (List.finRange 29).filter fun j => decide (j ≤ 26 ∧ j ≠ 2 ∧ j ≠ 24 ∧ j ≠ 25)

def cleanGoodHeadShear (k i : Fin d) (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T) :
    Pr P T 217 A U :=
  .seq (goodHeadShear k i coeff bank) (clearWorkTapes (headShearWork.map bank))

/-- Restore both stacks of every scratch tape. The cleanup charge depends only on
the shear time and the host push bound, so archived words incur no cleanup charge. -/
theorem cleanGoodHeadShear_of_exec (body : P → Pr P T 217 A U)
    (k i : Fin d) (coeff : Fin 17 ↪ Fin T) (bank : Fin 29 ↪ Fin T)
    {v u : HS T 217 A U} {S D : Stacks T A} {n push : ℕ}
    (run : Exec body (goodHeadShear k i coeff bank) (mk v S) n (mk u D))
    (hp : Fast.Main.mnProgPush (goodHeadShear k i coeff bank : Pr P T 217 A U) ≤ push)
    (hb : ∀ f, Fast.Main.mnProgPush (body f) ≤ push)
    (empty : ∀ j ∈ headShearWork, S.L (bank j) = [] ∧ S.R (bank j) = []) :
    let tapes := headShearWork.map bank
    ∃ z F t, z.user = u.user ∧ t ≤ 4*tapes.length+1+(1+6*tapes.length*push)*n ∧
      Exec body (cleanGoodHeadShear k i coeff bank) (mk v S) t (mk z F) ∧
      (∀ j ∈ headShearWork, F.L (bank j) = [] ∧ F.R (bank j) = []) ∧
      ∀ j, j ∉ tapes → F.L j = D.L j ∧ F.R j = D.R j := by
  intro tapes
  have distinct : tapes.Nodup := (by decide : headShearWork.Nodup).map bank.injective
  obtain ⟨z,hz,finish⟩ := clearWorkTapes_exec body tapes distinct u D
  have bound := cleanup_cost_le tapes run hp hb
  have init : (tapes.map fun j => 4*(S.L j).length+2*(S.R j).length+4) = tapes.map (fun _ => 4) := by
    apply List.map_congr_left
    intro j hj
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hj
    simp [(empty a ha).1,(empty a ha).2]
  rw [init,List.map_const',List.sum_replicate_nat] at bound
  refine ⟨z,_,_,hz,?_,Exec.seq run finish,?_,?_⟩
  · calc
      _ ≤ n + _ := Nat.add_le_add_left bound n
      _ = _ := by ring
  · intro j hj
    have h : bank j ∈ tapes := List.mem_map.mpr ⟨j,hj,rfl⟩
    simp [h]
  · intro j hj
    simp [hj]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
