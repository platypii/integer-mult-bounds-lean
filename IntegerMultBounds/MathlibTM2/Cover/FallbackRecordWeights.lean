module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackStreamedItinerary
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPayloadWeights

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
    (minor : ∀ k (hk : k < ranks), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk hr) m).det)
    :
    let stage := GoodForm.stageAt m ranks hr minor ranks le_rfl
    let weights := List.ofFn fun i : Fin ranks => binSyms (A := A) H
      (stage.M (i.castLE hr) (i.castLE hr)).val
    ∃ z F l, z.user = v.user ∧ l ≤ ranks*(4*w+4+columnTime d p w H)+1 +
      (ranks*(8*(d*d*H)+14*H+22)+1) ∧
      Exec body (goodWeights p ranks hr r) (mk v S) l (mk z F) ∧
      F.R (r 14) = weights.flatten ∧
      ∀ i : Fin ranks, IsUnit (stage.M (i.castLE hr) (i.castLE hr)) := by
  intro stage weights
  obtain ⟨u,D,l,suffix,hu,hl,run,packed,_,_,_,_,frame⟩ := goodProgram_exec body r p w H hp m hm v S tail
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
  exact ⟨z,_,l+t,hz.trans hu,Nat.add_le_add hl ht,Exec.seq run emit,Function.update_self ..,
    fun i => stage.unit _ i.isLt⟩

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
      ∀ b (x : Fin b → Fin (n+1) → ZMod (prime^(w+1))),
        fallbackBank b (if negative then -1 else 1) weights undo (bankFields (List.finRange (n+1)) x) =
          bankFields (List.finRange (n+1)) (fun k => G.mulVec (x k)) := by
  intro j code rows undo source
  obtain ⟨u,D,l,suffix,a,neg,hu,hl,run,remaining,packed,archive,frame,units,bit,prod,children,action⟩ :=
    recordDiagonalize_exec body r src apart w H hm table g G sign lift block N index v S tail rest matrix modulus one ticks free source
  let bank := stageBank r (n+1)
  have keep (i : Fin 23) (h : i ≠ 15) (h' : i ≠ 16) : D.R (bank i) = S.R (r i) := by
    have eq := stageBank_fixed r (n+1) i h h'
    exact (frame _ (eq ▸ apart i) (bank.injective.ne h) (bank.injective.ne h')).trans (congrArg S.R eq)
  have fresh : ∀ i : Fin 7, i = 0 ∨ 4 ≤ i → weightReadPorts i < 15 ∧ weightReadPorts i ≠ 2 := by decide
  obtain ⟨z,t,weights,hz,ht,emit,effect⟩ := payloadWeights_exec body (weightReadPorts.trans bank) H a units neg prod undo G action
    u D suffix packed (by change (D.R (bank 2)).length = H; simp [keep 2 (by decide) (by decide),modulus,length_binSyms])
    (by intro i h; obtain ⟨lo,h2⟩ := fresh i h
        exact (keep _ (by omega) (by omega)).trans (free _ (.inl ⟨lo,h2⟩)))
  have slot : (weightReadPorts.trans bank) 3 = r 14 := stageBank_fixed r (n+1) 14 (by decide) (by decide)
  have blank : D.R (r 14) = [] := by
    simpa [bank,stageBank_fixed r (n+1) 14 (by decide) (by decide)] using
      (keep 14 (by decide) (by decide)).trans (free 14 (by decide))
  rw [slot,blank,List.append_nil] at emit
  refine ⟨z,_,l+t,weights,neg,hz.trans hu,Nat.add_le_add hl ht,Exec.seq run emit,?_,?_,?_,?_,by simpa using children,bit,effect⟩
  · exact (Function.update_of_ne (apart 14).symm _ _).trans remaining
  · exact Function.update_self ..
  · have mid : bank 14 = r 14 := slot
    have h15 : bank 15 ≠ r 14 := mid ▸ bank.injective.ne (by decide)
    have h16 : bank 16 ≠ r 14 := mid ▸ bank.injective.ne (by decide)
    change (Function.update D.R (r 14) _ (bank 15), Function.update D.R (r 14) _ (bank 16)) = _
    rwa [Function.update_of_ne h15, Function.update_of_ne h16]
  · intro i hs hw ha hb
    exact (Function.update_of_ne hw _ _).trans (frame i hs ha hb)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
