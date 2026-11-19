module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodFullCross
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodPair

/-! Execute the outgoing cross correction and coordinate transform after the weighted child. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm FlatCoordinateLayout LabelTraversal
open CrossWeightLayout Matrix M8.Exchange IntegerMultBounds.Swap.Shear
open HeadPivotLayout HeadWidthLayout M8.ReversedExchange
variable {P U α : Type} {T A d W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

theorem goodOutgoing_exec [Fintype P] (body : P → Pr P T 217 A U) (machine : Fin 55 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (idem : G*G = G) (L : Matrix (Fin d) (Fin rank) (ZMod M)) (R : Matrix (Fin rank) (Fin d) (ZMod M))
    (factor : G = L*R) (weights inv : Fin d → ZMod M) (inverse : ∀ i, weights i * inv i = 1)
    (hb : b.Prime) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail dest rest invRest pivotTail : List (Fin (A+4))) (sym : α → Fin 4) (source target : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+d)*W : ℕ) → target z = blank) :
    let bank := adapterBank.trans machine
    let cw := crossBank.trans machine
    let crossHost := CrossWeightLayout.inverse.trans cw
    let host := head.trans bank
    let c := child.trans host
    let h := (coeff false).trans host
    let s := shear.trans host
    let words := fun j => if hj : j ≤ rank then matrixWords A H (stageAt G rank hr minor j hj).M else []
    let pair := matrixArchive words (words 0 ++ tail) dest rank
    let piv := fun j : Fin rank => (stageAt G rank hr minor rank le_rfl).M (j.castLE hr) (j.castLE hr)
    let parent := (List.ofFn fun i => binSyms H (weights i).val).flatten ++ rest
    let ready := HeadColumnReady (d := d+d) (W := W) h (entry.trans bank) H J [] parent [] sym source target p q
    let cost := fun a : Fin rank =>
      let k := a.castLE hr
      headPivotPrepareTime b d w H a.val (rank-a.val) +
        ((((List.finRange d).filter (k < ·)).map (headRowTime body h s k M (M^d*W) H (d*H+J))).sum+1+(2*(d*d*H+3*H)+9))
    let as := (List.finRange rank).reverse
    let ordinary := ordinaryHead.trans bank
    let th := (coeff true).trans ordinary
    let ts := shear.trans ordinary
    let tailOrder := (List.finRange rank).reverse
    let tailCost := fun a : Fin rank =>
      let k := a.castLE hr
      (8*((rank-a.val)/2*(d*d*H))+14*(d*d*H)+22 + tailPivotTime b w H a.val) +
        ((((List.finRange d).filter (k < ·)).map (tailEntryTimeAt body th ts (Fin.natAdd d) k M W H J)).sum+1+(2*(d*d*H+3*H)+9))
    let finalStage := stageAt G rank hr minor rank le_rfl
    let δ := fun t : Fin d => if t.val < rank then finalStage.M t t else 1
    let δ' := fun t : Fin d => if t.val < rank then Ring.inverse (finalStage.M t t) else 1
    let K := kMat (pivotMatrix (revPivots d rank))
      (rev d * finalStage.U * rev d * rev d * (finalStage.L * diagonal δ)) * diagonal (fun t => inv t * δ' t)
    let crossCost := fun a : Fin rank =>
      let k := a.castLE hr
      let rows := (List.finRange d).filter (fun i => rank ≤ i.val)
      let group := fun src => (rows.map fun t => let e := crossPair src k t
                                                 crossShearTime body ((coeff (if src then true else false)).trans crossHost)
                                                   ts e.1 e.2 M W H J).sum+1
      (8*((rank-a.val)/2*(d*d*H))+14*(d*d*H)+22 + tailPivotTime b w H a.val) +
        (group true + group false + (2*(d*d*H+3*H)+9))
    ∀ v S (word : Fin (M^(d+d)*W) → α),
      ready word S →
      S.R (bank 27) = [] → S.R (machine 54) = (List.ofFn fun j => binSyms H (inv j).val).flatten ++ invRest →
      (S.R (host 49),S.R (host 50)) = pair → (S.R (host 51)).length = d*d*H →
      S.R (c 18) = (List.ofFn fun j => binSyms H (piv j).val).flatten ++ pivotTail →
      S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
      ∃ z F n out, z.user = v.user ∧ n ≤ (((List.finRange rank).map crossCost).sum+1) + (dimensionTime H J d + ((as.map cost).sum+1) + (2*(d*H+J)+2) + ((tailOrder.map tailCost).sum+1)) ∧
        Exec body (.seq (crossStages b rank hr true crossHost (List.finRange rank)) (.seq (.seq (.seq (dimensionPower (power.trans bank) d) (headStages b rank hr false host as)) (bclear (bank 27))) (tailStagesAt (Fin.natAdd d) b rank hr true ordinary tailOrder))) (mk v S) n (mk z F) ∧ HeadColumnReady th ts H J [] parent [] sym source target p q out F ∧ F.R (bank 27) = [] ∧
        (∀ j, (∀ i, s i ≠ j) → (∀ i, ts i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        let stage := stageAt G rank hr minor rank le_rfl
        let action := Matrix.diagonal weights * stage.L * Matrix.diagonal inv
        let tailAction := rev d * stage.U' * rev d
        ∀ x y j, out (index (Fin.append (action.mulVec x) (tailAction.mulVec (y + (-K).mulVec x))) j) = word (index (Fin.append x y) j) := by
  intro bank cw crossHost host c h s words pair piv parent ready cost as ordinary th ts tailOrder tailCost
    stage δ δ' K crossCost v S word initial free stored packed count pivots one clock scratch
  have shared : CrossWeightLayout.base.trans cw = ordinary := congrArg (fun e => e.trans machine) sharedHost
  have childEq : child.trans ordinary = c := congrArg (fun e => e.trans bank) ordinary_child
  have same (j : Fin 53) (hj : 29 ≤ j) : ordinary j = host j := congrArg bank
    ((by decide : ∀ j : Fin 53, 29 ≤ j → ordinaryHead j = head j) j hj)
  have enter := tailReady bank false H J parent sym source target p q word S initial
    (scratch 0 (by decide)) (scratch 12 (by decide))
  have crossRun := fullCross_exec body cw G rank hr minor idem L R factor inv hb true H J hm hw hW
    parent tail dest invRest pivotTail sym source target p q empty
  dsimp only at crossRun
  rw [shared] at crossRun
  obtain ⟨u,D,l,mid,hu,hl,first,done,frame,effect⟩ := crossRun v S word enter
    (by rw [show cw 53 = machine 54 from congrArg machine inversePort]; exact stored)
    (by simpa only [same 49 (by decide),same 50 (by decide)] using packed)
    (by simpa only [same 51 (by decide)] using count)
    (by rwa [childEq]) (by rwa [childEq]) (by rwa [childEq]) (by rwa [childEq])
  have keep (j : Fin 53) (hj : 29 ≤ j) : D.R (host j) = S.R (host j) :=
    (frame _ (fun i => bank.injective.ne ((by decide : ∀ i (j : Fin 53), 29 ≤ j →
      entry i ≠ head j) i j hj))).2
  have childKeep (j : Fin 20) : D.R (c j) = S.R (c j) := keep _ ((by decide : ∀ i, 29 ≤ child i) j)
  have coeffEq : (coeff true).trans ordinary = (coeff true).trans host :=
    congrArg (fun e => e.trans bank) (ordinary_coeff true)
  rw [coeffEq] at done
  have next := tailReady bank true H J parent sym source target p q mid D done
    ((childKeep 0).trans (scratch 0 (by decide))) ((childKeep 12).trans (scratch 12 (by decide)))
  have ordinaryEq : (coeff false).trans ordinary = h := congrArg (fun e => e.trans bank) (ordinary_coeff false)
  change HeadColumnReady ((coeff false).trans ordinary) ts H J [] parent [] sym source target p q mid D at next
  rw [ordinaryEq] at next
  obtain ⟨z,F,n,out,hz,hn,run,post,unused,outer,act⟩ := goodAdapterPair_exec body bank G rank hr minor
    weights inv inverse hb false H J hm hw hW tail dest rest pivotTail sym source target p q empty u D mid next
    ((frame _ (fun i => bank.injective.ne ((by decide : ∀ i, entry i ≠ 27) i))).2.trans free)
    (by change (D.R (host 49),D.R (host 50)) = pair; simpa only [keep 49 (by decide),keep 50 (by decide)] using packed)
    (by change (D.R (host 51)).length = d*d*H; simpa only [keep 51 (by decide)] using count)
    ((childKeep 18).trans pivots) ((childKeep 15).trans one) ((congrArg List.length (childKeep 16)).trans clock)
    (fun j hj => (childKeep j).trans (scratch j hj))
  refine ⟨z,F,l+n,out,hz.trans hu,Nat.add_le_add hl hn,Exec.seq first run,post,unused,?_,?_⟩
  · intro j hs ht
    exact ⟨(outer j hs ht).1.trans (frame j ht).1,(outer j hs ht).2.trans (frame j ht).2⟩
  · intro finalStage action tailAction x y j
    exact (act x (y + (-K).mulVec x) j).trans (effect x y j)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
