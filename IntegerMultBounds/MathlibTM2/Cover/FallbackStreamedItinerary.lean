module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackUndoItinerary
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotStream

/-! Run every column from a single physical pivot record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A d : ℕ} {P U : Type}

def streamedItinerary (d p : ℕ) (r : Fin 23 ↪ Fin T) (src : Fin T) : ℕ → Pr P T Q A U
  | 0 => .act .done
  | n+1 => if h : n < d then .seq (streamedItinerary d p r src n)
      (liveColumn p (⟨n,h⟩ : Fin d) (stageBank r n) src) else streamedItinerary d p r src n

theorem streamedItinerary_exec (body : P → Pr P T Q A U) (r : Fin 23 ↪ Fin T) (src : Fin T) (apart : ∀ i, r i ≠ src) (p w H : ℕ) (hp : p.Prime)
    [NeZero (p^(w+1))] (m : Matrix (Fin d) (Fin d) (ZMod (p^(w+1)))) (pivot : Fin d → Fin d)
    (hm : p^(w+1) < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H m ++ tail) (modulus : S.R (r 2) = binSyms H (p^(w+1)))
    (one : S.R (r 20) = binSyms H (1 : ZMod (p^(w+1))).val) (ticks : (S.R (r 22)).length = w)
    (free : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (r i) = [])
    (n : ℕ) (hn : n ≤ d) (valid : Itinerary.Valid pivot m n)
    (rest : List (Fin (A+4))) (code : S.R src = ((List.finRange d).take n).flatMap (fun k => pivotCode (pivot k).val) ++ rest) :
    ∃ z F l suffix, z.user = v.user ∧ l ≤ n*(2*d+(4*w+4+columnTime d p w H))+1 ∧
      Exec body (streamedItinerary d p r src n) (mk v S) l (mk z F) ∧
      F.R (stageBank r n 15) = matrixWords A H (Itinerary.run pivot m n) ++ suffix ∧
      (F.R (stageBank r n 15),F.R (stageBank r n 16)) =
        matrixArchive (fun j => matrixWords A H (Itinerary.run pivot m j)) (S.R (r 15)) (S.R (r 16)) n ∧
      F.R src = rest ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      ∀ i, i ≠ src → i ≠ stageBank r n 15 → i ≠ stageBank r n 16 → F.R i = S.R i := by
  have outside (j : ℕ) (i : Fin 23) : stageBank r j i ≠ src := by
    induction j generalizing i with
    | zero => exact apart i
    | succ j ih => exact ih _
  induction n generalizing rest with
  | zero => exact ⟨v,S,1,tail,rfl,by simp,Exec.act (body := body) .done _,matrix,rfl,by simpa using code,rfl,rfl,rfl,fun _ _ _ _ => rfl⟩
  | succ n ih =>
    have h : n < d := hn
    let k : Fin d := ⟨n,h⟩
    let b := stageBank r n
    obtain ⟨prev,unit⟩ := (Itinerary.valid_succ pivot m n).mp valid
    have pos : n < (List.finRange d).length := by simpa using h
    rw [List.take_succ_eq_append_getElem pos,List.flatMap_append,List.flatMap_singleton,List.append_assoc] at code
    obtain ⟨u,D,l,suffix,hu,hl,run,packed,archive,remaining,hL,hin,hout,frame⟩ := ih h.le prev _ code
    have keep (i : Fin 23) (hi : i ≠ 15) (hj : i ≠ 16) : D.R (b i) = S.R (r i) :=
      (frame _ (outside n i) (b.injective.ne hi) (b.injective.ne hj)).trans (congrArg S.R (stageBank_fixed r n i hi hj))
    obtain ⟨z,t,hz,ht,col⟩ := liveColumn_exec body b src (outside n) p w H hp (Itinerary.run pivot m n) k (pivot k)
      (unit h).2 hm u D suffix rest (by simpa [k] using remaining) packed ((keep 2 (by decide) (by decide)).trans modulus)
      ((keep 20 (by decide) (by decide)).trans one) (by rw [keep 22 (by decide) (by decide),ticks])
      (fun i hi => (keep i (by omega) (by omega)).trans (free i hi))
    have next := (clearColumn_eq p w hp k (pivot k) (Itinerary.run pivot m n) (unit h).2).trans
      (Itinerary.run_succ pivot m n h).symm
    rw [next] at col
    have inputPort : stageBank r (n+1) 15 = b 16 := by simp [stageBank,b]
    have dst : stageBank r (n+1) 16 = b 15 := by simp [stageBank,b]
    refine ⟨z,{D with R := Function.update (Function.update D.R src rest) (b 16) (matrixWords A H (Itinerary.run pivot m (n+1)) ++ D.R (b 16))},l+t,D.R (b 16),hz.trans hu,?_,?_,?_,?_,?_,hL,hin,hout,?_⟩
    · rw [Nat.succ_mul]; omega
    · simpa only [streamedItinerary,dite_eq_left h] using Exec.seq run col
    · simp [inputPort]
    · rw [matrixArchive,← archive,inputPort,dst]
      simp [b.injective.eq_iff,Function.update_of_ne (show b 15 ≠ src from outside n 15),b]
    · exact (Function.update_of_ne (show src ≠ b 16 from (outside n 16).symm) _ _).trans (Function.update_self ..)
    · intro i hs hi hj
      rw [inputPort] at hi
      rw [dst] at hj
      exact (Function.update_of_ne hi _ _).trans ((Function.update_of_ne hs _ _).trans (frame _ hs hj hi))

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ prime_prime.ne_zero⟩

/-- At a live label, consume its schedule in physical record order and expose the unit
diagonal. Its product agrees with the independently emitted anchor bit for that record. -/
theorem recordDiagonalize_exec {m : ℕ} (body : P → Pr P T Q A U) (r : Fin 23 ↪ Fin T)
    (src : Fin T) (apart : ∀ i, r i ≠ src) (w H : ℕ) (hm : prime^(w+1) < 2^H)
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin d) (Fin d) (ZMod prime))
    (g : LabelPadding.Label m (w+1)) (G : Matrix (Fin d) (Fin d) (ZMod (prime^(w+1))))
    (sign : G.det = 1 ∨ G.det = -1)
    (lift : (LabelRing.res prime (w+1) (by omega)).mapMatrix G = table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    (block N : ℕ) (index : block*(prime^(w+1))^(m*m)+(LabelAddress.address g).val < N)
    (v : HS T Q A U) (S : Stacks T A) (tail rest : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H G ++ tail) (modulus : S.R (r 2) = binSyms H (prime^(w+1)))
    (one : S.R (r 20) = binSyms H (1 : ZMod (prime^(w+1))).val) (ticks : (S.R (r 22)).length = w)
    (free : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (r i) = []) :
    let j := block*(prime^(w+1))^(m*m)+(LabelAddress.address g).val
    let code := fun t =>
      let pivots := classPivots (table (LabelStock.residue m (w+1) 1 t))
      scheduleCode (A := A) pivots ++ orderedScheduleCode (List.finRange d).reverse pivots
    let rows := classPivots (table (LabelStock.residue m (w+1) 1 j))
    let undo := undoItinerary rows G d
    S.R src = ((List.range N).drop j).flatMap code ++ rest →
    ∃ z F l suffix, ∃ a : Fin d → ZMod (prime^(w+1)), ∃ negative, z.user = v.user ∧ l ≤ d*(2*d+(4*w+4+columnTime d prime w H))+1 ∧
      Exec body (streamedItinerary d prime r src d) (mk v S) l (mk z F) ∧
      F.R src = orderedScheduleCode (List.finRange d).reverse rows ++ (((List.range N).drop (j+1)).flatMap code ++ rest) ∧
      F.R (stageBank r d 15) = matrixWords A H (Matrix.diagonal a) ++ suffix ∧
      (F.R (stageBank r d 15),F.R (stageBank r d 16)) =
        matrixArchive (fun n => matrixWords A H (Itinerary.run rows G n)) (S.R (r 15)) (S.R (r 16)) d ∧
      (∀ i, i ≠ src → i ≠ stageBank r d 15 → i ≠ stageBank r d 16 → F.R i = S.R i) ∧
      Itinerary.Valid rows G d ∧ Itinerary.run rows G d = Matrix.diagonal a ∧
      (∀ i, IsUnit (a i)) ∧ (signStream (A := A) table (w+1) N)[j]? = some (bitSymbol negative) ∧
      (∏ i, a i) = (if negative then -1 else 1) ∧
      (undo.map RowOp.children).sum ≤ d*(6*(d-1)+3) ∧
      ∀ x, undo.foldl (fun y op => op.apply y) ((Matrix.diagonal a).mulVec x) = G.mulVec x := by
  intro j code rows undo source
  let pivots := classPivots (table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
  obtain ⟨neg,bit,valid,det⟩ := signStream_at (A := A) table (by omega) g G block N sign lift index
  have hj : j < (List.range N).length := by simpa [j] using index
  have head := (List.getElem_cons_drop hj).symm
  simp only [List.getElem_range] at head
  rw [head,List.flatMap_cons,List.append_assoc] at source
  have addr := LabelStock.residue_at (by omega : 0 < w+1) block 1 0 (by decide) g
  simp only [Nat.mul_one,Nat.add_zero] at addr
  have first : code j = scheduleCode (A := A) pivots ++ orderedScheduleCode (List.finRange d).reverse rows := by
    simp only [code,rows,j,addr,pivots]
  rw [first,List.append_assoc] at source
  obtain ⟨z,F,l,suffix,hz,hl,run,packed,archive,remaining,_,_,_,frame⟩ := streamedItinerary_exec body r src apart prime w H
    prime_prime G pivots hm v S tail matrix modulus one ticks free d le_rfl valid _ (by rw [List.take_of_length_le (by simp)]; exact source)
  obtain ⟨_,_,_,clear,units⟩ := Itinerary.run_spec pivots G d le_rfl valid
  let a := fun i => Itinerary.run pivots G d i i
  have diag : Itinerary.run pivots G d = Matrix.diagonal a := by
    ext i k
    by_cases h : i = k
    · subst k; simp [a]
    · rw [Matrix.diagonal_apply_ne _ h]; exact clear i k k.isLt h
  refine ⟨z,F,l,suffix,a,neg,hz,hl,run,remaining,diag ▸ packed,?_,frame,?_,?_,fun i => units i i.isLt,bit,?_,undoItinerary_children ..,?_⟩
  · simpa only [rows,j,addr,pivots] using archive
  · simpa only [rows,j,addr,pivots] using valid
  · simpa only [rows,j,addr,pivots] using diag
  · simpa only [← Matrix.det_diagonal,← diag] using det
  · intro x
    simpa only [undo,rows,j,addr,← diag,pivots] using undoItinerary_apply pivots G d x

end IntegerMultBounds.MathlibTM2.Cover.Fallback
