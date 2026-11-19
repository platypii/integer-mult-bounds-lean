module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackStreamedItinerary
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPayloadWeights

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders

/-! Produce the payload pair weights from a physical fallback record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q A n : ℕ} {P U : Type}
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

def weightReadPorts : Fin 7 ↪ Fin 23 := ⟨![0,2,15,14,3,4,5],by decide⟩

noncomputable def goodWeights {d : ℕ} (p : ℕ) (rank : ℕ) (hr : rank ≤ d) (r : Fin 23 ↪ Fin T) :
    Pr P T Q A U :=
  .seq (goodProgram (d := d) p r rank)
    (gatherMatrix (Fin.castLE hr) (Fin.castLE hr) (weightReadPorts.trans (stageBank r rank)))

theorem goodWeights_exec {d : ℕ} (body : P → Pr P T Q A U) (r : Fin 23 ↪ Fin T) (p w H : ℕ) (hp : p.Prime)
    [NeZero (p^(w+1))] (m : Matrix (Fin d) (Fin d) (ZMod (p^(w+1))))
    (hm : p^(w+1) < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H m ++ tail) (modulus : S.R (r 2) = binSyms H (p^(w+1)))
    (one : S.R (r 20) = binSyms H (1 : ZMod (p^(w+1))).val) (ticks : (S.R (r 22)).length = w)
    (free : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (r i) = [])
    (ranks : ℕ) (hr : ranks ≤ d)
    (minor : ∀ k (hk : k < ranks), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk hr) m).det) :
    let stage := GoodForm.stageAt m ranks hr minor ranks le_rfl
    let weights := List.ofFn fun i : Fin ranks => binSyms (A := A) H
      (stage.M (i.castLE hr) (i.castLE hr)).val
    ∃ z F l, z.user = v.user ∧ l ≤ ranks*(4*w+4+columnTime d p w H)+1 +
      (ranks*(8*(d*d*H)+14*H+22)+1) ∧
      Exec body (goodWeights p ranks hr r) (mk v S) l (mk z F) ∧
      F.R (r 14) = weights.flatten ∧
      (∀ i : Fin ranks, IsUnit (stage.M (i.castLE hr) (i.castLE hr))) ∧
      (F.R (stageBank r ranks 15), F.R (stageBank r ranks 16)) =
        matrixArchive (fun j => if hj : j ≤ ranks then
          matrixWords A H (GoodForm.stageAt m ranks hr minor j hj).M else [])
          (S.R (r 15)) (S.R (r 16)) ranks ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      ∀ i, i ≠ r 14 → i ≠ stageBank r ranks 15 → i ≠ stageBank r ranks 16 → F.R i = S.R i := by
  intro stage weights
  obtain ⟨u,D,l,suffix,hu,hl,run,packed,archive,hL,hin,hout,frame⟩ := goodProgram_exec body r p w H hp m hm v S tail
    matrix modulus one ticks free ranks hr minor ranks le_rfl
  let bank := stageBank r ranks
  have keep (i : Fin 23) (h : i ≠ 15) (h' : i ≠ 16) : D.R (bank i) = S.R (r i) :=
    (frame _ (bank.injective.ne h) (bank.injective.ne h')).trans (congrArg S.R (stageBank_fixed r ranks i h h'))
  have fresh : ∀ i : Fin 7, i = 0 ∨ 4 ≤ i → weightReadPorts i < 15 ∧ weightReadPorts i ≠ 2 := by decide
  obtain ⟨z,t,hz,ht,emit⟩ := gatherMatrix_exec body (weightReadPorts.trans bank) stage.M
    (Fin.castLE hr) (Fin.castLE hr) H u D suffix packed
    (by change (D.R (bank 2)).length = H; simp [keep 2 (by decide) (by decide),modulus,length_binSyms])
    (by intro i hi; obtain ⟨lo,h2⟩ := fresh i hi
        exact (keep _ (by omega) (by omega)).trans (free _ (.inl ⟨lo,h2⟩)))
  have blank : D.R ((weightReadPorts.trans bank) 3) = [] :=
    (keep 14 (by decide) (by decide)).trans (free 14 (by decide))
  rw [blank,List.append_nil] at emit
  have slot : (weightReadPorts.trans bank) 3 = r 14 := stageBank_fixed r ranks 14 (by decide) (by decide)
  rw [slot] at emit
  refine ⟨z,_,l+t,hz.trans hu,Nat.add_le_add hl ht,Exec.seq run emit,Function.update_self ..,
    fun i => stage.unit _ i.isLt,?_,hL,hin,hout,?_⟩
  · have mid : bank 14 = r 14 := slot
    have h15 : bank 15 ≠ r 14 := mid ▸ bank.injective.ne (by decide)
    have h16 : bank 16 ≠ r 14 := mid ▸ bank.injective.ne (by decide)
    change (Function.update D.R (r 14) _ (bank 15), Function.update D.R (r 14) _ (bank 16)) = _
    rwa [Function.update_of_ne h15, Function.update_of_ne h16]
  · intro i hw ha hb
    exact (Function.update_of_ne hw _ _).trans (frame i ha hb)

noncomputable def recordWeights (n : ℕ) (r : Fin 23 ↪ Fin T) (src : Fin T) : Pr P T Q A U :=
  .seq (streamedItinerary (n+1) prime r src (n+1))
    (gatherMatrix (n := n) Fin.succ Fin.succ (weightReadPorts.trans (stageBank r (n+1))))

theorem recordWeights_exec {m : ℕ} (body : P → Pr P T Q A U) (r : Fin 23 ↪ Fin T)
    (src : Fin T) (apart : ∀ i, r i ≠ src) (w H : ℕ) (hm : prime^(w+1) < 2^H)
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin (n+1)) (Fin (n+1)) (ZMod prime))
    (g : LabelPadding.Label m (w+1)) (G : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod (prime^(w+1))))
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
      scheduleCode (A := A) pivots ++ orderedScheduleCode (List.finRange (n+1)).reverse pivots
    let rows := classPivots (table (LabelStock.residue m (w+1) 1 j))
    let undo := undoItinerary rows G (n+1)
    S.R src = ((List.range N).drop j).flatMap code ++ rest →
    ∃ z F l, ∃ weights : Fin n → (ZMod (prime^(w+1)))ˣ, ∃ negative,
      z.user = v.user ∧ l ≤ (n+1)*(2*(n+1)+(4*w+4+columnTime (n+1) prime w H))+1 +
        (n*(8*((n+1)*(n+1)*H)+14*H+22)+1) ∧
      Exec body (recordWeights n r src) (mk v S) l (mk z F) ∧
      F.R src = orderedScheduleCode (List.finRange (n+1)).reverse rows ++ (((List.range N).drop (j+1)).flatMap code ++ rest) ∧
      F.R (r 14) = (List.ofFn fun i => binSyms H (weights i : ZMod (prime^(w+1))).val).flatten ∧
      (F.R (stageBank r (n+1) 15), F.R (stageBank r (n+1) 16)) =
        matrixArchive (fun k => matrixWords A H (Itinerary.run rows G k)) (S.R (r 15)) (S.R (r 16)) (n+1) ∧
      (∀ i, i ≠ src → i ≠ r 14 → i ≠ stageBank r (n+1) 15 → i ≠ stageBank r (n+1) 16 → F.R i = S.R i) ∧
      (undo.map RowOp.children).sum ≤ (n+1)*(6*n+3) ∧
      (signStream (A := A) table (w+1) N)[j]? = some (bitSymbol negative) ∧
      (∃ a : Fin (n+1) → (ZMod (prime^(w+1)))ˣ, Itinerary.Valid rows G (n+1) ∧
        Itinerary.run rows G (n+1) = Matrix.diagonal (fun i => (a i : ZMod (prime^(w+1)))) ∧
        (∏ i, a i) = (if negative then -1 else 1) ∧ ∀ i, weights i = a i.succ) ∧
      ∀ b (x : Fin b → Fin (n+1) → ZMod (prime^(w+1))),
        fallbackBank b (if negative then -1 else 1) weights undo (bankFields (List.finRange (n+1)) x) =
          bankFields (List.finRange (n+1)) (fun k => G.mulVec (x k)) := by
  intro j code rows undo source
  obtain ⟨u,D,l,suffix,a,neg,hu,hl,run,remaining,packed,archive,frame,valid,diag,units,bit,prod,children,action⟩ :=
    recordDiagonalize_exec body r src apart w H hm table g G sign lift block N index v S tail rest matrix modulus one ticks free source
  let bank := stageBank r (n+1)
  have keep (i : Fin 23) (h : i ≠ 15) (h' : i ≠ 16) : D.R (bank i) = S.R (r i) := by
    have eq := stageBank_fixed r (n+1) i h h'
    exact (frame _ (eq ▸ apart i) (bank.injective.ne h) (bank.injective.ne h')).trans (congrArg S.R eq)
  have fresh : ∀ i : Fin 7, i = 0 ∨ 4 ≤ i → weightReadPorts i < 15 ∧ weightReadPorts i ≠ 2 := by decide
  obtain ⟨z,t,weights,hz,ht,emit,entries,effect⟩ := payloadWeights_exec body (weightReadPorts.trans bank) H a units neg prod undo G action
    u D suffix packed (by change (D.R (bank 2)).length = H; simp [keep 2 (by decide) (by decide),modulus,length_binSyms])
    (by intro i h; obtain ⟨lo,h2⟩ := fresh i h
        exact (keep _ (by omega) (by omega)).trans (free _ (.inl ⟨lo,h2⟩)))
  have slot : (weightReadPorts.trans bank) 3 = r 14 := stageBank_fixed r (n+1) 14 (by decide) (by decide)
  have blank : D.R (r 14) = [] := by
    simpa [bank,stageBank_fixed r (n+1) 14 (by decide) (by decide)] using
      (keep 14 (by decide) (by decide)).trans (free 14 (by decide))
  rw [slot,blank,List.append_nil] at emit
  refine ⟨z,_,l+t,weights,neg,hz.trans hu,Nat.add_le_add hl ht,Exec.seq run emit,?_,?_,?_,?_,by simpa using children,bit,?_,effect⟩
  · exact (Function.update_of_ne (apart 14).symm _ _).trans remaining
  · exact Function.update_self ..
  · have mid : bank 14 = r 14 := slot
    have h15 : bank 15 ≠ r 14 := mid ▸ bank.injective.ne (by decide)
    have h16 : bank 16 ≠ r 14 := mid ▸ bank.injective.ne (by decide)
    change (Function.update D.R (r 14) _ (bank 15), Function.update D.R (r 14) _ (bank 16)) = _
    rwa [Function.update_of_ne h15, Function.update_of_ne h16]
  · intro i hs hw ha hb
    exact (Function.update_of_ne hw _ _).trans (frame i hs ha hb)

  · let u := fun i => (units i).unit
    have val (i) : (u i : ZMod (prime^(w+1))) = a i := (units i).unit_spec
    refine ⟨u,valid,by simpa only [val] using diag,?_,fun i => Units.ext ((entries i).trans (val i.succ).symm)⟩
    apply Units.ext
    cases neg <;> simpa [Units.coe_prod,val] using prod

/-- Copy the resident padded one ahead of the extracted pivots. The ordinary exchange reads
entry zero, and the weighted exchange for row `i` reads entry `i.succ`. -/
theorem prependPivotOne_exec (body : P → Pr P T Q A U) (r : Fin 23 ↪ Fin T) (w H : ℕ)
    (weights : Fin n → (ZMod (prime^(w+1)))ˣ) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (one : S.R (r 20) = binSyms H (1 : ZMod (prime^(w+1))).val)
    (packed : S.R (r 14) = (List.ofFn fun i => binSyms H (weights i : ZMod (prime^(w+1))).val).flatten ++ tail)
    (tmp : S.R (r 3) = []) (saved : S.R (r 4) = []) :
    let pivot : Fin (n+1) → ZMod (prime^(w+1)) := Fin.cons (1 : ZMod (prime^(w+1))) (fun i => (weights i : ZMod (prime^(w+1))))
    ∃ z, z.user = v.user ∧ Exec body (Mult.PhaseCellToeplitz.copyWordHeader (r 20) (r 14) (r 3) (r 4))
      (mk v S) (6*H+6) (mk z {S with R := Function.update S.R (r 14) ((List.ofFn fun i => binSyms H (pivot i).val).flatten ++ tail)}) := by
  intro pivot
  obtain ⟨z,hz,run⟩ := Mult.PhaseCellToeplitz.copyWordHeader_exec (body := body) (r 20) (r 14) (r 3) (r 4)
    (by simp [r.injective.eq_iff]) v S tmp saved
  refine ⟨z,hz,?_⟩
  rw [one,packed] at run
  simpa [pivot,List.ofFn_succ,List.append_assoc,length_binSyms] using run

theorem preparedRecordWeights_exec {m : ℕ} (body : P → Pr P T Q A U) (r : Fin 23 ↪ Fin T)
    (src : Fin T) (apart : ∀ i, r i ≠ src) (w H : ℕ) (hm : prime^(w+1) < 2^H)
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin (n+1)) (Fin (n+1)) (ZMod prime))
    (g : LabelPadding.Label m (w+1)) (G : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod (prime^(w+1))))
    (sign : G.det = 1 ∨ G.det = -1)
    (lift : (LabelRing.res prime (w+1) (by omega)).mapMatrix G = table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    (block N : ℕ) (index : block*(prime^(w+1))^(m*m)+(LabelAddress.address g).val < N)
    (v : HS T Q A U) (S : Stacks T A) (tail rest : List (Fin (A+4)))
    (parentTape : Fin T) (parent : Fin n → (ZMod (prime^(w+1)))ˣ)
    (outside : ∀ i, r i ≠ parentTape) (separate : parentTape ≠ src)
    (parents : S.R parentTape = (List.ofFn fun i => binSyms H (parent i : ZMod (prime^(w+1))).val).flatten)
    (matrix : S.R (r 15) = matrixWords A H G ++ tail) (modulus : S.R (r 2) = binSyms H (prime^(w+1)))
    (one : S.R (r 20) = binSyms H (1 : ZMod (prime^(w+1))).val) (ticks : (S.R (r 22)).length = w)
    (free : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (r i) = []) :
    let j := block*(prime^(w+1))^(m*m)+(LabelAddress.address g).val
    let code := fun t =>
      let pivots := classPivots (table (LabelStock.residue m (w+1) 1 t))
      scheduleCode (A := A) pivots ++ orderedScheduleCode (List.finRange (n+1)).reverse pivots
    let rows := classPivots (table (LabelStock.residue m (w+1) 1 j))
    let active := stageBank r (n+1) 15
    let undo := undoItinerary rows G (n+1)
    S.R src = ((List.range N).drop j).flatMap code ++ rest →
    ∃ z F l, ∃ weights : Fin n → (ZMod (prime^(w+1)))ˣ, ∃ negative,
      z.user = v.user ∧ l ≤ (n+1)*(2*(n+1)+(4*w+4+columnTime (n+1) prime w H))+1 +
        (n*(8*((n+1)*(n+1)*H)+14*H+22)+1) + (6*H+6) + (6*((n+1)*H)+6) + (6*(n*H)+6) ∧
      Exec body (.seq (.seq (.seq (recordWeights n r src) (Mult.PhaseCellToeplitz.copyWordHeader (r 20) (r 14) (r 3) (r 4)))
        (Mult.PhaseCellToeplitz.copyWordHeader (r 14) active (r 3) (r 4))) (Mult.PhaseCellToeplitz.copyWordHeader parentTape src (r 3) (r 4))) (mk v S) l (mk z F) ∧
      F.R src = S.R parentTape ++ (orderedScheduleCode (List.finRange (n+1)).reverse rows ++ (((List.range N).drop (j+1)).flatMap code ++ rest)) ∧
      F.R (r 14) = (List.ofFn fun i => binSyms H ((Fin.cons 1 (fun j => (weights j : ZMod (prime^(w+1)))) : Fin (n+1) → ZMod (prime^(w+1))) i).val).flatten ∧
      (∃ archive, F.R active = F.R (r 14) ++ archive ∧ (archive, F.R (stageBank r (n+1) 16)) =
        matrixArchive (fun k => matrixWords A H (Itinerary.run rows G k)) (S.R (r 15)) (S.R (r 16)) (n+1)) ∧
      (∀ i, i ≠ src → i ≠ r 14 → i ≠ stageBank r (n+1) 15 → i ≠ stageBank r (n+1) 16 → F.R i = S.R i) ∧
      (undo.map RowOp.children).sum ≤ (n+1)*(6*n+3) ∧
      (signStream (A := A) table (w+1) N)[j]? = some (bitSymbol negative) ∧
      (∃ a : Fin (n+1) → (ZMod (prime^(w+1)))ˣ, Itinerary.Valid rows G (n+1) ∧
        Itinerary.run rows G (n+1) = Matrix.diagonal (fun i => (a i : ZMod (prime^(w+1)))) ∧
        (∏ i, a i) = (if negative then -1 else 1) ∧ ∀ i, weights i = a i.succ) ∧
      ∀ b (x : Fin b → Fin (n+1) → ZMod (prime^(w+1))),
        fallbackBank b (if negative then -1 else 1) weights undo (bankFields (List.finRange (n+1)) x) =
          bankFields (List.finRange (n+1)) (fun k => G.mulVec (x k)) := by
  intro j code rows active undo source
  obtain ⟨u,D,l,weights,neg,hu,hl,run,schedule,packed,archive,frame,children,bit,units,effect⟩ :=
    recordWeights_exec body r src apart w H hm table g G sign lift block N index v S tail rest matrix modulus one ticks free source
  have off (i k : Fin 23) (hi : i ≠ 15) (hj : i ≠ 16) (ne : i ≠ k) : r i ≠ stageBank r (n+1) k := by
    rw [← stageBank_fixed r (n+1) i hi hj]
    exact (stageBank r (n+1)).injective.ne ne
  have keep (i : Fin 23) (hi : i ≠ 15) (hj : i ≠ 16) (hk : i ≠ 14) :=
    frame (r i) (apart i) (r.injective.ne hk) (off i 15 hi hj hi) (off i 16 hi hj hj)
  obtain ⟨z,hz,copy⟩ := prependPivotOne_exec body r w H weights [] u D
    ((keep 20 (by decide) (by decide) (by decide)).trans one) (by simpa using packed)
    ((keep 3 (by decide) (by decide) (by decide)).trans (free 3 (by decide)))
    ((keep 4 (by decide) (by decide) (by decide)).trans (free 4 (by decide)))
  simp only [List.append_nil] at copy
  let pivot : Fin (n+1) → ZMod (prime^(w+1)) := Fin.cons 1 (fun j => (weights j : ZMod (prime^(w+1))))
  let pivotWord := (List.ofFn fun i => binSyms (A := A) H (pivot i).val).flatten
  let E := {D with R := Function.update D.R (r 14) pivotWord}
  have distinct (i : Fin 23) (hi : i ≠ 15) (hj : i ≠ 16) : r i ≠ active := off i 15 hi hj hi
  have regs : [r 14,active,r 3,r 4].Nodup := by
    simp [r.injective.eq_iff,distinct 14 (by decide) (by decide),
      (distinct 3 (by decide) (by decide)).symm,(distinct 4 (by decide) (by decide)).symm]
  obtain ⟨y,hy,install⟩ := Mult.PhaseCellToeplitz.copyWordHeader_exec (body := body) _ _ _ _ regs z E
    (by simp [E,r.injective.eq_iff,keep 3 (by decide) (by decide) (by decide),free 3 (by decide)])
    (by simp [E,r.injective.eq_iff,keep 4 (by decide) (by decide) (by decide),free 4 (by decide)])
  have atSlot : E.R (r 14) = pivotWord := Function.update_self ..
  have len : pivotWord.length = (n+1)*H := by
    simp [pivotWord,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const,Nat.add_mul,Nat.add_comm]
  rw [atSlot,len] at install
  have srcOff (k : ℕ) (i : Fin 23) : stageBank r k i ≠ src := by
    induction k generalizing i with
    | zero => exact apart i
    | succ k ih => exact ih _
  have kept (i : Fin T) (hi : i ≠ active) (hj : i ≠ r 14) :
      Function.update E.R active (pivotWord ++ E.R active) i = D.R i :=
    (Function.update_of_ne hi _ _).trans (Function.update_of_ne hj _ _)
  let F := {E with R := Function.update E.R active (pivotWord ++ E.R active)}
  have parentOff (k : ℕ) (i : Fin 23) : stageBank r k i ≠ parentTape := by
    induction k generalizing i with
    | zero => exact outside i
    | succ k ih => exact ih _
  have parentEq : F.R parentTape = S.R parentTape :=
    (kept _ (parentOff _ _).symm (outside 14).symm).trans
      (frame _ separate (outside 14).symm (parentOff _ _).symm (parentOff _ _).symm)
  have clean (i : Fin 23) (hi : i < 14) (h2 : i ≠ 2) : F.R (r i) = [] := by
    rw [show F.R (r i) = D.R (r i) from kept _ (distinct i (by omega) (by omega)) (r.injective.ne (by omega)),
      keep i (by omega) (by omega) (by omega)]
    exact free i (.inl ⟨by omega,h2⟩)
  obtain ⟨x,hx,attach⟩ := Mult.PhaseCellToeplitz.copyWordHeader_exec (body := body) parentTape src (r 3) (r 4)
    (by simp [separate,(outside _).symm,(apart _).symm,r.injective.eq_iff]) y F
    (clean 3 (by decide) (by decide)) (clean 4 (by decide) (by decide))
  have plen : (F.R parentTape).length = n*H := by
    rw [parentEq,parents]
    simp [List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const]
  rw [plen,parentEq] at attach
  let result := Function.update F.R src (S.R parentTape ++ F.R src)
  have unaffected (i : Fin T) (ne : i ≠ src) : result i = F.R i := Function.update_of_ne ne _ _
  have slot : F.R (r 14) = pivotWord := (Function.update_of_ne (distinct 14 (by decide) (by decide)) _ _).trans atSlot
  refine ⟨x,_,_,weights,neg,hx.trans (hy.trans (hz.trans hu)),Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hl _) _) _,
    Exec.seq (Exec.seq (Exec.seq run copy) install) attach,?_,(unaffected _ (apart 14)).trans slot,?_,?_,children,bit,units,effect⟩
  · change result src = _
    simp only [result,Function.update_self]
    exact congrArg (S.R parentTape ++ ·) ((kept src (srcOff (n+1) 15).symm (apart 14).symm).trans schedule)
  · refine ⟨D.R active,?_,?_⟩
    · change result active = result (r 14) ++ _
      rw [unaffected _ (srcOff _ _),unaffected _ (apart 14),slot]
      change Function.update E.R active (pivotWord ++ E.R active) active = _
      rw [Function.update_self]
      exact congrArg (pivotWord ++ ·) (Function.update_of_ne (distinct 14 (by decide) (by decide)).symm _ _)
    · change (D.R active,result _) = _
      rw [unaffected _ (srcOff _ _),show F.R (stageBank r (n+1) 16) = D.R _ from
        kept _ ((stageBank r (n+1)).injective.ne (by decide : (16 : Fin 23) ≠ 15))
          (off 14 16 (by decide) (by decide) (by decide)).symm]
      exact archive
  · intro i hs hw ha hb
    exact (unaffected i hs).trans ((kept i ha hw).trans (frame i hs hw ha hb))

end IntegerMultBounds.MathlibTM2.Cover.Fallback
