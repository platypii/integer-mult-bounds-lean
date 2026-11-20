module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodAdapter
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalLabel
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairWeights
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordWeights

/-! The physical good branch uses the elimination pivots as child weights. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open Matrix Finset IntegerMultBounds.Swap.LowerTriangular IntegerMultBounds.Swap.Modular
  IntegerMultBounds.Swap.Shear M8.Exchange M8.ReversedExchange
variable {m T Q A w : ℕ} {P U : Type}
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

def goodChildPorts : Fin 20 ↪ Fin 24 :=
  ⟨![0,1,3,4,2,5,6,7,8,9,10,11,12,13,17,20,22,21,14,23],by decide⟩

/-- The stopped leaf extends the twenty coefficient tapes by the parent's
empty register 18. The two matrix archive tapes remain in place. -/
def goodLeafPorts : Fin 21 ↪ Fin 24 :=
  ⟨Fin.lastCases 18 goodChildPorts,by decide⟩

theorem goodLeafPorts_pair : (Fin.castAddEmb 1).trans goodLeafPorts = goodChildPorts := by
  apply Function.Embedding.ext
  intro j
  exact (by decide : ∀ j : Fin 20, goodLeafPorts (j.castAdd 1) = goodChildPorts j) j

/-- On a good record the words emitted by elimination are precisely the
diagonal corrections in the one-child move. Each active child coordinate can
then read its product weight and reciprocal from the parent and pivot tapes. Tapes outside the pivot
archive and weight output are preserved. -/
theorem goodRecordWeights_exec (body : P → Pr P T Q A U) (ports : Fin 24 ↪ Fin T)
    (proj : Matrix (Fin m) (Fin m) ℚ) (idem : proj*proj = proj)
    (f : Factorization univ univ proj) (hd : ∀ d ∈ factorizationDenominators f, d < prime)
    (fits : proj.rank ≤ m) (j H : ℕ) (hm : M < 2^H)
    (live : LabelStock.live m (w+1) 1 j = true)
    (α α' : Fin m → ZMod M) (inv : ∀ i, α i * α' i = 1)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4))) (negateForward : Bool := false) :
    let bank := (Fin.castLEEmb (by decide : 23 ≤ 24)).trans ports
    let child := goodChildPorts.trans ports
    let g := physicalLabel m (w+1) j
    let G := g*reduce M proj*g⁻¹
    fallbackBit fits (reduce M proj) g = false →
    S.R (bank 15) = matrixWords A H G ++ tail → S.R (bank 2) = binSyms H M →
    S.R (bank 20) = binSyms H (1 : ZMod M).val → (S.R (bank 22)).length = w →
    (∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (bank i) = []) →
    ∃ minor : ∀ k (hk : k < proj.rank), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk fits) G).det,
    let stage := GoodForm.stageAt G proj.rank fits minor proj.rank le_rfl
    let δ := fun i : Fin m => if i.val < proj.rank then stage.M i i else 1
    let δ' := fun i : Fin m => if i.val < proj.rank then Ring.inverse (stage.M i i) else 1
    let R := rev m * stage.U * rev m
    let R' := rev m * stage.U' * rev m
    let K := kMat (pivotMatrix (revPivots m proj.rank)) (R * rev m * (stage.L * diagonal δ)) *
      diagonal fun i => α' i * δ' i
    ∃ z F l,
      z.user = v.user ∧ l ≤ proj.rank*(4*w+4+columnTime m prime w H)+1 +
        (proj.rank*(8*(m*m*H)+14*H+22)+1) ∧
      Exec body (goodWeights prime proj.rank fits bank) (mk v S) l (mk z F) ∧
      F.R (bank 14) = (List.ofFn fun i : Fin proj.rank => binSyms H (δ (i.castLE fits)).val).flatten ∧
      (F.R (stageBank bank proj.rank 15), F.R (stageBank bank proj.rank 16)) =
        matrixArchive (fun k => if hk : k ≤ proj.rank then
          matrixWords A H (GoodForm.stageAt G proj.rank fits minor k hk).M else [])
          (S.R (bank 15)) (S.R (bank 16)) proj.rank ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ i, i ≠ bank 14 → i ≠ stageBank bank proj.rank 15 → i ≠ stageBank bank proj.rank 16 → F.R i = S.R i) ∧
      (∀ rest : List (Fin (A+4)),
        S.R (ports 23) = (List.ofFn fun k => binSyms H (α k).val).flatten ++ rest →
        F.R (ports (goodLeafPorts 20)) = [] ∧
        PackedLeafInputs child H α (fun k : Fin proj.rank => δ (k.castLE fits)) F [] rest ∧
        ∀ i : Fin proj.rank,
        let C := 48*H*H+152*H+66
        ∃ u D t, u.user = v.user ∧ t ≤ (8*(i.val*H)+14*H+22) +
          ((8*(i.val*H)+48*H*H+166*H+88)+(6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C)))) +
          (2*H+2)+(8*H+8) ∧ Exec body (signedChildPair prime i.val i.val child negateForward) (mk z F) t (mk u D) ∧
          D.R (child 14) = binSyms H (α (i.castLE fits) * δ (i.castLE fits)).val ∧
          D.R (child 0) = binSyms H (α' (i.castLE fits) * δ' (i.castLE fits)).val ∧
          D.R (child 12) = binSyms H (-(if negateForward then α (i.castLE fits) * δ (i.castLE fits) else α' (i.castLE fits) * δ' (i.castLE fits))).val ∧
          D.L = F.L ∧ D.inp = F.inp ∧ D.out = F.out ∧
          ∀ k, k ≠ child 0 → k ≠ child 14 → k ≠ child 12 → D.R k = F.R k) ∧
      (∀ i, δ i * δ' i = 1) ∧
      let head := goodHeadWord G proj.rank fits minor α α' proj.rank le_rfl
      head.length ≤ proj.rank*m ∧ (head.map RowOp.children).sum = 0 ∧ ((inverseWord head).map RowOp.children).sum = 0 ∧
      ∀ s : State (Fin m) (ZMod M),
        let before := (head.foldl (fun x op => op.apply x) s.1, R.mulVec s.2)
        let after := cross (-K) (Weighted.child proj.rank (fun i => α i * δ i) (fun i => α' i * δ' i)
          (cross K before))
        ((inverseWord head).foldl (fun x op => op.apply x) after.1, R'.mulVec after.2) =
          transform (diagonal α) 1 (revExchangeOf (rev m) G (transform (diagonal α') 1 s)) := by
  classical
  intro bank child g G clear matrix modulus one ticks free
  have unit : IsUnit g := (physicalLabel_live (by omega) j).mp live
  have minor (k) (hk : k < proj.rank) : IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk fits) G).det := by
    by_contra bad
    have selected : fallbackBit fits (reduce M proj) g = true :=
      decide_eq_true ⟨unit,k,hk,bad⟩
    simp [clear] at selected
  refine ⟨minor,?_⟩
  intro stage δ δ' R R' K
  obtain ⟨z,F,l,user,time,run,words,_,archive,left,inp,out,frame⟩ := goodWeights_exec body bank prime w H
    prime_prime G hm v S tail matrix modulus one ticks free proj.rank fits minor
  obtain ⟨a,b,factor⟩ := LabelProjector.rank_factors proj f prime_prime hd (w+1) g
  have adm : Admissible M proj := admissible_of_lt prime_prime
    (fun d h => hd d (by simp [factorizationDenominators,h])) _
  have square : reduce M proj * reduce M proj = reduce M proj := by rw [← reduce_mul _ adm adm,idem]
  have idempotent : G*G = G := by
    change (g*_ * g⁻¹)*(g*_ * g⁻¹) = _
    calc
      _ = g*(reduce M proj*(g⁻¹*g)*reduce M proj)*g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).mp unit),Matrix.mul_one,square]
  obtain ⟨_,_,_,_,units,_⟩ := stage.normalForm fits a b factor
  have zero := goodHeadWord_children G proj.rank fits minor α α' proj.rank le_rfl
  refine ⟨z,F,l,user,time,run,?_,archive,left,inp,out,frame,?_,units,goodHeadWord_length ..,zero,(inverseWord_children _).trans zero,?_⟩
  · simpa only [δ,Fin.val_castLE,Fin.isLt,ite_true] using words
  · intro rest parent
    have unchanged (k : Fin 23) (a : k ≠ 14) (b : k ≠ 15) (c : k ≠ 16) :
        F.R (bank k) = S.R (bank k) := by
      have stable := stageBank_fixed bank proj.rank k b c
      exact frame _ (bank.injective.ne a) (stable ▸ (stageBank bank proj.rank).injective.ne b)
        (stable ▸ (stageBank bank proj.rank).injective.ne c)
    have outside (k : Fin 23) : ports 23 ≠ bank k :=
      ports.injective.ne ((by decide : ∀ j : Fin 23, (23 : Fin 24) ≠ j.castLE (Nat.le_succ 23)) k)
    have apart (n : ℕ) (k : Fin 23) : ports 23 ≠ stageBank bank n k := by
      induction n generalizing k with
      | zero => exact outside k
      | succ n ih => exact ih ((Equiv.swap 15 16) k)
    have parentWord : F.R (child 19) = _ := (frame _ (outside 14) (apart _ 15) (apart _ 16)).trans parent
    let pivot := fun k : Fin proj.rank => stage.M (k.castLE fits) (k.castLE fits)
    have pivots : F.R (child 18) = (List.ofFn fun k => binSyms H (pivot k).val).flatten ++ [] := by
      rw [show child 18 = bank 14 from rfl,List.append_nil]
      exact words
    have scratch (k : Fin 20) (hk : (k ≤ 14 ∧ k ≠ 4) ∨ k = 17) :
        F.R (child k) = [] := by
      have slots : ∀ k : Fin 20, (k ≤ 14 ∧ k ≠ 4) ∨ k = 17 →
          ∃ j : Fin 23, goodChildPorts k = j.castLE (by decide) ∧ j ≠ 14 ∧ j ≠ 15 ∧ j ≠ 16 ∧
            ((j < 15 ∧ j ≠ 2) ∨ (17 ≤ j ∧ j ≤ 19) ∨ j = 21) := by decide
      obtain ⟨j,eq,h14,h15,h16,hfree⟩ := slots k hk
      exact (congrArg (fun x => F.R (ports x)) eq).trans ((unchanged j h14 h15 h16).trans (free j hfree))
    have ready : PackedLeafInputs child H α pivot F [] rest :=
      ⟨parentWord,pivots,(unchanged 2 (by decide) (by decide) (by decide)).trans modulus,
        (unchanged 20 (by decide) (by decide) (by decide)).trans one,
        (congrArg List.length (unchanged 22 (by decide) (by decide) (by decide))).trans ticks,scratch⟩
    refine ⟨(unchanged 18 (by decide) (by decide) (by decide)).trans (free 18 (by decide)),?_,?_⟩
    · simpa only [δ,Fin.val_castLE,Fin.isLt,ite_true,pivot] using ready
    intro i C
    obtain ⟨u,D,t,hu,ht,run,pair,inverse,negative,hL,hin,hout,kept⟩ := signedChildPair_exec body child α
      (i.castLE fits) _ (inv _) pivot i (stage.unit _ i.isLt) prime_prime H hm z F [] rest ready.weights ready.pivots ready.modulus ready.one ready.clock ready.scratch negateForward
    exact ⟨u,D,t,hu.trans user,ht,run,by simpa only [δ,Fin.val_castLE,Fin.isLt,ite_true] using pair,
      by simpa only [δ',Fin.val_castLE,Fin.isLt,ite_true] using inverse,
      by simpa only [δ,δ',Fin.val_castLE,Fin.isLt,ite_true] using negative,hL,hin,hout,kept⟩
  · intro s
    dsimp only
    rw [goodHeadWord_inverse_apply _ _ _ _ _ _ inv,goodHeadWord_apply _ _ _ _ _ _ inv]
    exact stage.goodMove fits a b factor idempotent α α' inv s

theorem stageBank_slot (bank : Fin 23 ↪ Fin T) (n : ℕ) (k : Fin 23) :
    ∃ j, stageBank bank n k = bank j := by
  induction n generalizing k with
  | zero => exact ⟨k,rfl⟩
  | succ n ih => exact ih ((Equiv.swap 15 16) k)

/-- Pass the elimination pivots and the original full-width parent archive to the next host call. -/
theorem withGoodRecordWeights_exec (body : P → Pr P T Q A U) (ports : Fin 24 ↪ Fin T)
    (proj : Matrix (Fin m) (Fin m) ℚ) (idem : proj*proj = proj)
    (f : Factorization univ univ proj) (hd : ∀ d ∈ factorizationDenominators f, d < prime)
    (fits : proj.rank ≤ m) (j H : ℕ) (hm : M < 2^H)
    (live : LabelStock.live m (w+1) 1 j = true)
    (α α' : Fin m → ZMod M) (inv : ∀ i, α i * α' i = 1)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4))) (parentTail : List (Fin (A+4)))
    (next : Pr P T Q A U) (budget : ℕ) (post : Stacks T A → Prop) :
    let bank := (Fin.castLEEmb (by decide : 23 ≤ 24)).trans ports
    let child := goodChildPorts.trans ports
    let g := physicalLabel m (w+1) j
    let G := g*reduce M proj*g⁻¹
    fallbackBit fits (reduce M proj) g = false →
    S.R (bank 15) = matrixWords A H G ++ tail → S.R (bank 2) = binSyms H M →
    S.R (bank 20) = binSyms H (1 : ZMod M).val → (S.R (bank 22)).length = w →
    (∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (bank i) = []) →
    S.R (ports 23) = (List.ofFn fun k => binSyms H (α k).val).flatten ++ parentTail →
    (∀ (minor : ∀ k (hk : k < proj.rank), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk fits) G).det)
        (y : HS T Q A U) (E : Stacks T A),
      let stage := GoodForm.stageAt G proj.rank fits minor proj.rank le_rfl
      let pivot := fun k : Fin proj.rank => stage.M (k.castLE fits) (k.castLE fits)
      (∀ k, IsUnit (pivot k)) →
      PackedLeafInputs child H α pivot E [] parentTail → E.R (ports 18) = [] →
      (E.R (stageBank bank proj.rank 15), E.R (stageBank bank proj.rank 16)) =
        matrixArchive (fun k => if hk : k ≤ proj.rank then
          matrixWords A H (GoodForm.stageAt G proj.rank fits minor k hk).M else [])
          (S.R (bank 15)) (S.R (bank 16)) proj.rank →
      E.L = S.L → (∀ j, (∀ k, ports k ≠ j) → E.R j = S.R j) →
      ∃ z D t, z.user = y.user ∧ t ≤ budget ∧ Exec body next (mk y E) t (mk z D) ∧ post D) →
    ∃ z D t, z.user = v.user ∧ t ≤ (proj.rank*(4*w+4+columnTime m prime w H)+1+
      (proj.rank*(8*(m*m*H)+14*H+22)+1))+budget ∧
      Exec body ((goodWeights prime proj.rank fits bank).seq next) (mk v S) t (mk z D) ∧ post D := by
  intro bank child g G good matrix modulus one ticks free weights consume
  obtain ⟨minor,y,E,l,user,cost,run,_,archive,left,_,_,frame,ready,units,_⟩ :=
    goodRecordWeights_exec body ports proj idem f hd fits j H hm live α α' inv v S tail
      (negateForward := false) good matrix modulus one ticks free
  obtain ⟨spare,packed,_⟩ := ready parentTail weights
  have outside (n) (k : Fin 23) (j : Fin T) (off : ∀ k, ports k ≠ j) : stageBank bank n k ≠ j := by
    obtain ⟨i,eq⟩ := stageBank_slot bank n k
    exact eq ▸ off _
  obtain ⟨z,D,t,hz,ht,step,done⟩ := consume minor y E (by
    intro k
    refine isUnit_iff_exists_inv.mpr ⟨Ring.inverse ((GoodForm.stageAt G proj.rank fits minor proj.rank le_rfl).M (k.castLE fits) (k.castLE fits)),?_⟩
    simpa only [Fin.val_castLE,k.isLt,ite_true] using units (k.castLE fits))
    (by simpa only [Fin.val_castLE,Fin.isLt,ite_true] using packed) spare archive left
    (fun j off => frame j (off _).symm (outside _ _ j off).symm (outside _ _ j off).symm)
  exact ⟨z,D,l+t,hz.trans user,Nat.add_le_add cost ht,Exec.seq run step,done⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
