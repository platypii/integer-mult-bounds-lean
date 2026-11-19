module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadWidth
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodTailRun

/-! The incoming and outgoing coordinate transforms of a good record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm FlatCoordinateLayout LabelTraversal
open HeadPivotLayout HeadWidthLayout M8.ReversedExchange
variable {P U α : Type} {T A d W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

private theorem tailReady {N : ℕ} (bank : Fin 54 ↪ Fin T) (negative : Bool) (H J : ℕ)
    (parent : List (Fin (A+4))) (sym : α → Fin 4) (source target : ℤ → Fin 4) (p q : ℤ)
    (out : Fin (N^(d+d)*W) → α) (D : Stacks T A) :
    let h := (coeff negative).trans (head.trans bank)
    let th := (coeff (!negative)).trans (ordinaryHead.trans bank)
    HeadColumnReady h (entry.trans bank) H J [] parent [] sym source target p q out D →
    D.R (bank (head (child 0))) = [] → D.R (bank (head (child 12))) = [] →
    HeadColumnReady th (entry.trans bank) H J [] parent [] sym source target p q out D := by
  intro h th done pos neg
  have same (j : Fin 17) (hj : j ≠ 14) : th j = h j :=
    congrArg bank ((by cases negative <;> decide : ∀ k : Fin 17, k ≠ 14 →
      ordinaryHead (coeff (!negative) k) = head (coeff negative k)) j hj)
  refine ⟨by rw [same 13 (by decide)]; exact done.stage,by rw [same 16 (by decide)]; exact done.weights,?_,
      by rw [same 2 (by decide)]; exact done.modulus,fun j hj => by rw [same j (by omega)]; exact done.coeffWork j hj,
      done.base,done.one,done.width,done.scratch,done.src,done.dst⟩
  cases negative
  · exact neg
  · exact pos

theorem goodAdapterPair_exec [Fintype P] (body : P → Pr P T 217 A U) (bank : Fin 54 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (weights inv : Fin d → ZMod M) (inverse : ∀ i, weights i * inv i = 1)
    (hb : b.Prime) (negative : Bool) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail dest rest pivotTail : List (Fin (A+4))) (sym : α → Fin 4) (source target : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+d)*W : ℕ) → target z = blank) :
    let host := head.trans bank
    let c := child.trans host
    let h := (coeff negative).trans host
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
    let as := if negative then List.finRange rank else (List.finRange rank).reverse
    let ordinary := ordinaryHead.trans bank
    let th := (coeff (!negative)).trans ordinary
    let ts := shear.trans ordinary
    let tailOrder := if !negative then (List.finRange rank).reverse else List.finRange rank
    let tailCost := fun a : Fin rank =>
      let k := a.castLE hr
      (8*((rank-a.val)/2*(d*d*H))+14*(d*d*H)+22 + tailPivotTime b w H a.val) +
        ((((List.finRange d).filter (k < ·)).map (tailEntryTimeAt body th ts (Fin.natAdd d) k M W H J)).sum+1+(2*(d*d*H+3*H)+9))
    ∀ v S (word : Fin (M^(d+d)*W) → α),
      ready word S →
      S.R (bank 27) = [] →
      (S.R (host 49),S.R (host 50)) = pair → (S.R (host 51)).length = d*d*H →
      S.R (c 18) = (List.ofFn fun j => binSyms H (piv j).val).flatten ++ pivotTail →
      S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
      ∃ z F n out, z.user = v.user ∧ n ≤ dimensionTime H J d + ((as.map cost).sum+1) + (2*(d*H+J)+2) + ((tailOrder.map tailCost).sum+1) ∧
        Exec body (.seq (.seq (.seq (dimensionPower (power.trans bank) d) (headStages b rank hr negative host as)) (bclear (bank 27))) (tailStagesAt (Fin.natAdd d) b rank hr (!negative) ordinary tailOrder)) (mk v S) n (mk z F) ∧ HeadColumnReady th ts H J [] parent [] sym source target p q out F ∧ F.R (bank 27) = [] ∧
        (∀ j, (∀ i, s i ≠ j) → (∀ i, ts i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        let stage := stageAt G rank hr minor rank le_rfl
        let action := Matrix.diagonal weights * (if negative then stage.L' else stage.L) * Matrix.diagonal inv
        let tailAction := rev d * (if !negative then stage.U' else stage.U) * rev d
        ∀ x y j, out (index (Fin.append (action.mulVec x) (tailAction.mulVec y)) j) = word (index (Fin.append x y) j) := by
  intro host c h s words pair piv parent ready cost as ordinary th ts tailOrder tailCost v S word initial free
    packed count pivots one clock scratch
  obtain ⟨u,D,l,out,hu,hl,headRun,done,unused,frame,headEffect⟩ := ordinaryFullHead_exec body bank G rank hr minor
    weights inv inverse hb negative H J hm hw hW tail dest rest pivotTail sym source target p q empty
    v S word initial free packed count pivots one clock scratch
  have childKeep (j : Fin 20) : D.R (c j) = S.R (c j) :=
    (frame _ (fun i => bank.injective.ne ((by decide : ∀ i j, head (shear i) ≠ head (child j)) i j))).2
  have clear (j : Fin 20) (hj : (j ≤ 14 ∧ j ≠ 4) ∨ j = 17) :=
    (childKeep j).trans (scratch j hj)
  have enter := tailReady bank negative H J parent sym source target p q out D done
    (clear 0 (by decide)) (clear 12 (by decide))
  have keep (j : Fin 53) (hj : 49 ≤ j) : D.R (ordinary j) = S.R (host j) := by
    rw [show ordinary j = host j from congrArg bank ((by decide : ∀ j : Fin 53, 49 ≤ j →
      ordinaryHead j = head j) j hj)]
    exact (frame _ (fun i => bank.injective.ne ((by decide : ∀ i (j : Fin 53), 49 ≤ j →
      head (shear i) ≠ head j) i j hj))).2
  have children : child.trans ordinary = c := congrArg (fun e => e.trans bank) ordinary_child
  obtain ⟨z,F,n,result,hz,hn,tailRun,post,outer,tailEffect⟩ := fullTail_exec body ordinary G rank hr minor
    hb (!negative) H J hm hw hW tail dest parent pivotTail sym source target p q empty u D out enter
    (by simpa only [keep 49 (by decide),keep 50 (by decide)] using packed)
    (by simpa only [keep 51 (by decide)] using count)
    (by rw [children]; exact (childKeep 18).trans pivots)
    (by rw [children]; exact (childKeep 15).trans one)
    (by rw [children,childKeep,clock]) (by rw [children]; exact clear)
  refine ⟨z,F,l+n,result,hz.trans hu,Nat.add_le_add hl hn,Exec.seq headRun tailRun,post,
    (outer _ (fun i => bank.injective.ne ((by decide : ∀ i, entry i ≠ 27) i))).2.trans unused,?_,?_⟩
  · intro j hs ht
    exact ⟨(outer j ht).1.trans (frame j hs).1,(outer j ht).2.trans (frame j hs).2⟩
  · intro stage action tailAction x y j
    exact (tailEffect (action.mulVec x) y j).trans (headEffect x y j)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
