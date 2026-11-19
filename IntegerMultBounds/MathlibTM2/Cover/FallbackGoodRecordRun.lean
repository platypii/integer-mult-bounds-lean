module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildPayload
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodOutgoing
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordEffect

/-! Execute one archived good record around the recursive rank child. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm FlatCoordinateLayout LabelTraversal
open CrossWeightLayout Matrix M8.Exchange IntegerMultBounds.Swap.Shear
open HeadPivotLayout HeadWidthLayout M8.ReversedExchange
open GoodChildLayout
variable {P U α : Type} {T A d W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def goodIncoming (b rank : ℕ) (hr : rank ≤ d) (machine : Fin 55 ↪ Fin T) : Pr P T 217 A U :=
    let bank := adapterBank.trans machine
    let cw := crossBank.trans machine
    let crossHost := CrossWeightLayout.inverse.trans cw
    let host := head.trans bank
    let as := List.finRange rank
    let ordinary := ordinaryHead.trans bank
    let tailOrder := List.finRange rank
    (.seq (.seq (.seq (.seq (dimensionPower (power.trans bank) d) (headStages b rank hr true host as)) (bclear (bank 27))) (tailStagesAt (Fin.natAdd d) b rank hr false ordinary tailOrder)) (crossStages b rank hr false crossHost as))

noncomputable def goodIncomingTime [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (b w W H J rank : ℕ) (hr : rank ≤ d) :=
    let bank := adapterBank.trans machine
    let cw := crossBank.trans machine
    let crossHost := CrossWeightLayout.inverse.trans cw
    let host := head.trans bank
    let h := (coeff true).trans host
    let s := shear.trans host
    let cost := fun a : Fin rank =>
      let k := a.castLE hr
      headPivotPrepareTime b d w H a.val (rank-a.val) +
        ((((List.finRange d).filter (k < ·)).map (headRowTime body h s k (b^(w+1)) ((b^(w+1))^d*W) H (d*H+J))).sum+1+(2*(d*d*H+3*H)+9))
    let as := List.finRange rank
    let ordinary := ordinaryHead.trans bank
    let th := (coeff false).trans ordinary
    let ts := shear.trans ordinary
    let tailOrder := List.finRange rank
    let tailCost := fun a : Fin rank =>
      let k := a.castLE hr
      (8*((rank-a.val)/2*(d*d*H))+14*(d*d*H)+22 + tailPivotTime b w H a.val) +
        ((((List.finRange d).filter (k < ·)).map (tailEntryTimeAt body th ts (Fin.natAdd d) k (b^(w+1)) W H J)).sum+1+(2*(d*d*H+3*H)+9))
    let crossCost := fun a : Fin rank =>
      let k := a.castLE hr
      let rows := (List.finRange d).filter (fun i => rank ≤ i.val)
      let group := fun src => (rows.map fun t => let e := crossPair src k t
                                                 crossShearTime body ((coeff (if src then false else true)).trans crossHost)
                                                   ts e.1 e.2 (b^(w+1)) W H J).sum+1
      (8*((rank-a.val)/2*(d*d*H))+14*(d*d*H)+22 + tailPivotTime b w H a.val) +
        (group true + group false + (2*(d*d*H+3*H)+9))
    dimensionTime H J d + ((as.map cost).sum+1) + (2*(d*H+J)+2) + ((tailOrder.map tailCost).sum+1) + ((as.map crossCost).sum+1)

def goodOutgoing (b rank : ℕ) (hr : rank ≤ d) (machine : Fin 55 ↪ Fin T) : Pr P T 217 A U :=
    let bank := adapterBank.trans machine
    let cw := crossBank.trans machine
    let crossHost := CrossWeightLayout.inverse.trans cw
    let host := head.trans bank
    let as := (List.finRange rank).reverse
    let ordinary := ordinaryHead.trans bank
    let tailOrder := (List.finRange rank).reverse
    (.seq (crossStages b rank hr true crossHost (List.finRange rank)) (.seq (.seq (.seq (dimensionPower (power.trans bank) d) (headStages b rank hr false host as)) (bclear (bank 27))) (tailStagesAt (Fin.natAdd d) b rank hr true ordinary tailOrder)))

noncomputable def goodOutgoingTime [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (b w W H J rank : ℕ) (hr : rank ≤ d) :=
    let bank := adapterBank.trans machine
    let cw := crossBank.trans machine
    let crossHost := CrossWeightLayout.inverse.trans cw
    let host := head.trans bank
    let h := (coeff false).trans host
    let s := shear.trans host
    let cost := fun a : Fin rank =>
      let k := a.castLE hr
      headPivotPrepareTime b d w H a.val (rank-a.val) +
        ((((List.finRange d).filter (k < ·)).map (headRowTime body h s k (b^(w+1)) ((b^(w+1))^d*W) H (d*H+J))).sum+1+(2*(d*d*H+3*H)+9))
    let as := (List.finRange rank).reverse
    let ordinary := ordinaryHead.trans bank
    let th := (coeff true).trans ordinary
    let ts := shear.trans ordinary
    let tailOrder := (List.finRange rank).reverse
    let tailCost := fun a : Fin rank =>
      let k := a.castLE hr
      (8*((rank-a.val)/2*(d*d*H))+14*(d*d*H)+22 + tailPivotTime b w H a.val) +
        ((((List.finRange d).filter (k < ·)).map (tailEntryTimeAt body th ts (Fin.natAdd d) k (b^(w+1)) W H J)).sum+1+(2*(d*d*H+3*H)+9))
    let crossCost := fun a : Fin rank =>
      let k := a.castLE hr
      let rows := (List.finRange d).filter (fun i => rank ≤ i.val)
      let group := fun src => (rows.map fun t => let e := crossPair src k t
                                                 crossShearTime body ((coeff (if src then true else false)).trans crossHost)
                                                   ts e.1 e.2 (b^(w+1)) W H J).sum+1
      (8*((rank-a.val)/2*(d*d*H))+14*(d*d*H)+22 + tailPivotTime b w H a.val) +
        (group true + group false + (2*(d*d*H+3*H)+9))
    (((List.finRange rank).map crossCost).sum+1) + (dimensionTime H J d + ((as.map cost).sum+1) + (2*(d*H+J)+2) + ((tailOrder.map tailCost).sum+1))

/-- Rank is fixed by the selected projector. A zero-rank record takes one
machine step and requires neither archive traversal nor a recursive call. -/
def goodRecord (full : Fin 58 ↪ Fin T) (f : P) (b rank g : ℕ) (hr : rank ≤ d) : Pr P T 217 A U :=
  let machine := parent.trans (parentWithWeights.trans full)
  if rank = 0 then .act .done else
    .seq (.seq (goodIncoming b rank hr machine) (goodChildCall f full b rank g))
      (goodOutgoing b rank hr machine)

private theorem zeroRank_exchange {N : ℕ} (G : Matrix (Fin d) (Fin d) (ZMod N))
    (L : Matrix (Fin d) (Fin 0) (ZMod N)) (R : Matrix (Fin 0) (Fin d) (ZMod N))
    (factor : G = L*R) (weights inv : Fin d → ZMod N) (inverse : ∀ i, weights i * inv i = 1)
    (x : State (Fin d) (ZMod N)) :
    transform (diagonal weights) 1 (revExchangeOf (rev d) G (transform (diagonal inv) 1 x)) = x := by
  have zero : G = 0 := by rw [factor]; ext i j; simp [Matrix.mul_apply]
  simp [zero,revExchangeOf,exchange,transform,mulVec_mulVec,rev_mul_rev,Weighted.diagonal_inv_mul weights inv inverse]

theorem goodRecord_exec [Fintype P] (body : P → Pr P T 217 A U) (full : Fin 58 ↪ Fin T) (f : P) (budget : ℕ)
    {rank : ℕ} (G : Matrix (Fin d) (Fin d) (ZMod M)) (g : ℕ) (dim : d = rank+g) (hr : rank ≤ d)
    (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (idem : G*G = G) (L : Matrix (Fin d) (Fin rank) (ZMod M)) (R : Matrix (Fin rank) (Fin d) (ZMod M))
    (factor : G = L*R) (weights inv : Fin d → ZMod M) (inverse : ∀ i, weights i * inv i = 1)
    (hb : b.Prime) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail dest rest invRest pivotTail : List (Fin (A+4))) (sym : α → Fin 4) (source target : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+d)*W : ℕ) → target z = blank) :
    let machine := parent.trans (parentWithWeights.trans full)
    let bank := adapterBank.trans machine
    let host := head.trans bank
    let c := child.trans host
    let h := (coeff true).trans host
    let s := shear.trans host
    let words := fun j => if hj : j ≤ rank then matrixWords A H (stageAt G rank hr minor j hj).M else []
    let pair := matrixArchive words (words 0 ++ tail) dest rank
    let stage := stageAt G rank hr minor rank le_rfl
    let piv := fun j : Fin rank => stage.M (j.castLE hr) (j.castLE hr)
    let parent := (List.ofFn fun i => binSyms H (weights i).val).flatten ++ rest
    let ready := HeadColumnReady (d := d+d) (W := W) h (entry.trans bank) H J [] parent [] sym source target p q
    let ordinary := ordinaryHead.trans bank
    let ts := shear.trans ordinary
    let childWeight := fun i : Fin rank => weights (i.castLE hr) * piv i
    let childInv := fun i : Fin rank => inv (i.castLE hr) * Ring.inverse (piv i)
    let prepared := fun S : Stacks T A => {S with R := Function.update (Function.update (Function.update S.R
      (full 55) (List.ofFn fun i => binSyms H (childWeight i).val).flatten) (full 56)
      (List.ofFn fun i => binSyms H (childInv i).val).flatten) (full 57) (binSyms ((g+g)*H+1) (M^(g+g)))}
    let middleCost := (((List.finRange rank).map fun i => childWeightTime b w H i.val).sum+1 + dimensionTime H 1 (g+g)) +
        (budget+2+(2*(rank*H+rank*H+((g+g)*H+1))+7))
    ∀ v S (word : Fin (M^(d+d)*W) → α),
      ready word S →
      S.R (bank 27) = [] → S.R (machine 54) = (List.ofFn fun j => binSyms H (inv j).val).flatten ++ invRest →
      (S.R (host 49),S.R (host 50)) = pair → (S.R (host 51)).length = d*d*H →
      S.R (c 18) = (List.ofFn fun j => binSyms H (piv j).val).flatten ++ pivotTail →
      S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
      (∀ k ∈ [full 55,full 56,full 57], S.R k = []) →
      (0 < rank → ∀ (u : HS T 217 A U) (D : Stacks T A) (before : Fin (M^(d+d)*W) → α),
        HeadColumnReady ((coeff false).trans ordinary) ts H J [] parent [] sym source target p q before D →
        ∃ z F n after, z.user = u.user ∧ n ≤ budget ∧ Exec body (body f) (mk u (prepared D)) n (mk z F) ∧
          (∀ (hg tg : Fin g → ZMod M) (x : State (Fin rank) (ZMod M)) j,
            let addr := fun y => let t := childFields hg tg y
                                 index (Fin.append (fun i : Fin d => t.1 (i.cast dim)) (fun i : Fin d => t.2 (i.cast dim))) j
            after (addr (Weighted.child rank childWeight childInv x)) = before (addr x)) ∧
          (∀ k, k ≠ ts 24 → F.L k = (prepared D).L k ∧ F.R k = (prepared D).R k) ∧
          ∀ k, RadixToBinary.binaryEncoding.encode (putWord source p (List.ofFn (sym ∘ after)) k) =
            readAt blank (F.L (ts 24)) (F.R (ts 24)) (k-p)) →
      ∃ z F n out, z.user = v.user ∧
        n ≤ goodIncomingTime body machine b w W H J rank hr + middleCost + goodOutgoingTime body machine b w W H J rank hr ∧
        Exec body (goodRecord full f b rank g hr) (mk v S) n (mk z F) ∧ ready out F ∧ F.R (bank 27) = [] ∧
        (∀ j, (∀ i, s i ≠ j) → (∀ i, ts i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ x j, let y := transform (diagonal weights) 1 (revExchangeOf (rev d) G (transform (diagonal inv) 1 x))
               out (index (Fin.append y.1 y.2) j) = word (index (Fin.append x.1 x.2) j) := by
  subst d
  intro machine bank host c h s words pair stage piv parent ready ordinary ts childWeight childInv prepared
    middleCost v S word initial free stored packed count pivots one clock scratch fresh recursive
  by_cases zero : rank = 0
  · subst rank
    refine ⟨v,S,1,word,rfl,?_,?_,initial,free,fun _ _ _ => ⟨rfl,rfl⟩,?_⟩
    · dsimp only [middleCost]
      omega
    · exact Exec.act _ _
    · intro x j
      rw [zeroRank_exchange G L R factor weights inv inverse x]
  have positive : 0 < rank := Nat.pos_of_ne_zero zero
  obtain ⟨u,D,l,before,hu,hl,first,mid,unused,frame,inc⟩ := goodIncoming_exec body machine G rank hr minor
    idem L R factor weights inv inverse hb H J hm hw hW tail dest rest invRest pivotTail sym source target p q empty
    v S word initial free stored packed count pivots one clock scratch
  have keep (j : Fin 58) (hj : 29 ≤ j ∧ j ≠ 53) : D.R (full j) = S.R (full j) :=
    (frame _ (fun i => full.injective.ne ((by decide : ∀ i (j : Fin 58), 29 ≤ j → j ≠ 53 →
      parentWithWeights (GoodChildLayout.parent (adapterBank (head (shear i)))) ≠ j) i j hj.1 hj.2))
      (fun i => full.injective.ne ((by decide : ∀ i (j : Fin 58), 29 ≤ j → j ≠ 53 →
      parentWithWeights (GoodChildLayout.parent (adapterBank (entry i))) ≠ j) i j hj.1 hj.2))).2
  have ck (j : Fin 20) : D.R (c j) = S.R (c j) :=
    keep _ ((by decide : ∀ i, let k := parentWithWeights (GoodChildLayout.parent (adapterBank (head (child i))))
                              29 ≤ k ∧ k ≠ 53) j)
  have coeq (sign : Bool) : (coeff sign).trans ordinary = (coeff sign).trans host :=
    congrArg (fun e => e.trans bank) (ordinary_coeff sign)
  let effect := fun after : Fin (M^((rank+g)+(rank+g))*W) → α =>
    ∀ (hg tg : Fin g → ZMod M) (x : State (Fin rank) (ZMod M)) (j : Fin W),
      let addr := fun y => let t := childFields hg tg y; index (Fin.append t.1 t.2) j
      after (addr (Weighted.child rank childWeight childInv x)) = before (addr x)
  have mid' := mid
  rw [coeq] at mid'
  obtain ⟨y,E,t,after,hy,act,next,saved,ht,call⟩ := goodChildPayload_exec body f full G hr g W minor
    weights inv inverse hb H hm u D pivotTail rest budget J sym source target p q before effect mid'
    ((ck 18).trans pivots) ((ck 15).trans one) ((congrArg List.length (ck 16)).trans clock)
    (fun j hj => (ck j).trans (scratch j hj)) (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl
      all_goals exact (keep _ (by decide)).trans (fresh _ (by simp)))
    (by
      intro v _
      obtain ⟨z,F,n,out,hz,hn,run,act,saved,src⟩ := recursive positive v D before mid
      refine ⟨z,F,n,out,hz,hn,?_,?_,?_,src⟩
      · simpa only [prepared,childWeight,childInv,piv,stage,goodChildDescriptor] using run
      · intro hg tg x j
        simpa only [Fin.cast_refl,id_eq] using act hg tg x j
      · intro k hk; exact saved k hk)
  have archive (j : Fin 58) (hj : 29 ≤ j ∧ j ≠ 53) : E.R (full j) = S.R (full j) :=
    (saved _ (full.injective.ne (by change j ≠ 24; omega))).2.trans (keep j hj)
  have childArchive (j : Fin 20) : E.R (c j) = S.R (c j) :=
    archive _ ((by decide : ∀ i, let k := parentWithWeights (GoodChildLayout.parent (adapterBank (head (child i))))
                                29 ≤ k ∧ k ≠ 53) j)
  obtain ⟨z,F,n,out,hz,hn,last,done,blank,outer,outgoing⟩ := goodOutgoing_exec body machine G rank hr minor idem L R factor
    weights inv inverse hb H J hm hw hW tail dest rest invRest pivotTail sym source target p q empty y E after next
    ((saved _ (full.injective.ne (by decide : (27 : Fin 58) ≠ 24))).2.trans unused)
    ((archive 54 (by decide)).trans stored)
    (by change (E.R (full 49),E.R (full 50)) = pair; rw [archive 49 (by decide),archive 50 (by decide)]; exact packed)
    ((congrArg List.length (archive 51 (by decide))).trans count) ((childArchive 18).trans pivots)
    ((childArchive 15).trans one) ((congrArg List.length (childArchive 16)).trans clock)
    (fun j hj => (childArchive j).trans (scratch j hj))
  rw [coeq] at done
  exact ⟨z,F,_,out,hz.trans (hy.trans hu),Nat.add_le_add (Nat.add_le_add hl ht) hn,
    by simpa only [goodRecord,ite_eq_right zero,goodIncoming,goodOutgoing,machine] using Exec.seq (Exec.seq first call) last,done,blank,
    fun j hs ht => ⟨(outer j hs ht).1.trans ((saved j (ht 24).symm).1.trans (frame j hs ht).1),
      (outer j hs ht).2.trans ((saved j (ht 24).symm).2.trans (frame j hs ht).2)⟩,
    goodRecord_effect stage L R factor idem weights inv inverse word before after out inc (fun hg tg x j => by
      simpa only [childWeight,childInv,piv,stage,Fin.castLE,Fin.castAdd] using act hg tg x j) outgoing⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
