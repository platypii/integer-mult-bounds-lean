module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadStage

/-! Execute successive good pivots from one fixed archive in either traversal order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm FlatCoordinateLayout LabelTraversal
open HeadPivotLayout
variable {P U α : Type} {T A d W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def headStages (b rank : ℕ) (hr : rank ≤ d) (negative : Bool) (host : Fin 53 ↪ Fin T) :
    List (Fin rank) → Pr P T 217 A U
  | [] => .act .done
  | a :: as =>
    let k := a.castLE hr
    .seq (headStage b rank k negative host ((List.finRange d).filter (k < ·)))
      (headStages b rank hr negative host as)

noncomputable def headStageWord {R : Type*} [CommRing R] (G : Matrix (Fin d) (Fin d) R)
    (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (weights inv : Fin d → R) (negative : Bool) (a : Fin rank) :=
  let k := a.castLE hr
  let stage := (stageAt G rank hr minor a.val a.isLt.le).M
  goodColumnWord k fun i => let x := weights i * (stage i k * Ring.inverse (stage k k)) * inv k
                            if negative then -x else x

theorem headStages_exec [Fintype P] (body : P → Pr P T 217 A U) (host : Fin 53 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (weights inv : Fin d → ZMod M) (inverse : ∀ i, weights i * inv i = 1)
    (hb : b.Prime) (negative : Bool) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail dest rest pivotTail : List (Fin (A+4))) (sym : α → Fin 4) (source target : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → target z = blank) :
    let c := child.trans host
    let h := (coeff negative).trans host
    let s := shear.trans host
    let words := fun j => if hj : j ≤ rank then matrixWords A H (stageAt G rank hr minor j hj).M else []
    let pair := matrixArchive words (words 0 ++ tail) dest rank
    let piv := fun j : Fin rank => (stageAt G rank hr minor rank le_rfl).M (j.castLE hr) (j.castLE hr)
    let parent := (List.ofFn fun i => binSyms H (weights i).val).flatten ++ rest
    let ready : (Fin (M^d*W) → α) → Stacks T A → Prop := HeadColumnReady (d := d) (W := W) h s H J [] parent [] sym source target p q
    let cost := fun a : Fin rank =>
      let k := a.castLE hr
      headPivotPrepareTime b d w H a.val (rank-a.val) +
        ((((List.finRange d).filter (k < ·)).map (headRowTime body h s k M W H J)).sum+1+(2*(d*d*H+3*H)+9))
    ∀ as : List (Fin rank), ∀ v S word, ready word S →
      (S.R (host 49),S.R (host 50)) = pair → (S.R (host 51)).length = d*d*H →
      S.R (c 18) = (List.ofFn fun j => binSyms H (piv j).val).flatten ++ pivotTail →
      S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
      ∃ z F n out, z.user = v.user ∧ n ≤ (as.map cost).sum+1 ∧
        Exec body (headStages b rank hr negative host as) (mk v S) n (mk z F) ∧ ready out F ∧
        (∀ j, (∀ i, s i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ x j, out (index ((as.flatMap (headStageWord G rank hr minor weights inv negative)).foldl
          (fun y op => op.apply y) x) j) = word (index x j) := by
  intro c h s words pair piv parent ready cost as
  induction as with
  | nil =>
    intro v S word initial _ _ _ _ _ _
    exact ⟨v,S,1,word,rfl,by simp,Exec.act _ _,initial,fun _ _ => ⟨rfl,rfl⟩,fun _ _ => rfl⟩
  | cons a as ih =>
    intro v S word initial packed count pivots one clock scratch
    let odd := decide ((rank-a.val)%2 ≠ 0)
    let r := (reader odd).trans host
    have select : S.R (r 2) = if (rank-a.val)%2 = 0 then pair.1 else pair.2 := by
      by_cases even : (rank-a.val)%2 = 0
      · simpa [r,odd,even,reader] using congrArg Prod.fst packed
      · simpa [r,odd,even,reader] using congrArg Prod.snd packed
    have width : (S.R (r 1)).length = d*d*H := by cases eq : odd <;> simpa [r,eq,reader] using count
    let k := a.castLE hr
    obtain ⟨u,D,t,out,hu,ht,step,next,frame,effect⟩ := headStage_exec body host G rank hr minor a weights inv
      inverse hb negative H J hm hw hW v S tail dest rest pivotTail sym source target p q word empty
      ((List.finRange d).filter (k < ·)) select width pivots one clock scratch initial
      (fun i hi => of_decide_eq_true (List.mem_filter.mp hi).2)
    have childKeep (j : Fin 20) : D.R (c j) = S.R (c j) :=
      (frame _ (fun i => host.injective.ne ((by decide : ∀ i j, shear i ≠ child j) i j))).2
    have keep (j : Fin 53) (hj : 49 ≤ j) := (frame (host j)
      (fun i => host.injective.ne ((by decide : ∀ i j, 49 ≤ j → shear i ≠ j) i j hj))).2
    obtain ⟨z,F,n,result,hz,hn,more,done,saved,act⟩ := ih u D out next
      (by rwa [keep 49 (by decide),keep 50 (by decide)]) (by rwa [keep 51 (by decide)])
      ((childKeep 18).trans pivots) ((childKeep 15).trans one) (by rwa [childKeep])
      (fun j hj => (childKeep j).trans (scratch j hj))
    refine ⟨z,F,t+n,result,hz.trans hu,?_,Exec.seq step more,done,?_,?_⟩
    · have bound : t ≤ cost a := ht
      simpa [Nat.add_assoc] using Nat.add_le_add bound hn
    · intro j outside
      exact ⟨(saved j outside).1.trans (frame j outside).1,(saved j outside).2.trans (frame j outside).2⟩
    · intro x j
      rw [List.flatMap_cons,List.foldl_append]
      exact (act _ j).trans (effect x j)

section
variable {R : Type*} [CommRing R] (G : Matrix (Fin d) (Fin d) R) (rank : ℕ) (hr : rank ≤ d)
  (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
  (weights inv : Fin d → R)

theorem ascendingHeadWord (n : ℕ) (hn : n ≤ rank) :
    ((List.finRange n).flatMap fun a => headStageWord G rank hr minor weights inv true (a.castLE hn)) =
      goodHeadWord G rank hr minor weights inv n hn := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ_last,List.flatMap_append,List.flatMap_map]
    change ((List.finRange n).flatMap fun a => headStageWord G rank hr minor weights inv true
      (a.castLE (by omega))) ++ _ = _
    rw [ih]
    simp [goodHeadWord,headStageWord]
    rfl

private theorem undoHeadColumn (a : Fin rank) (x : Fin d → R) :
    (headStageWord G rank hr minor weights inv false a).foldl (fun y op => op.apply y)
      ((headStageWord G rank hr minor weights inv true a).foldl (fun y op => op.apply y) x) = x := by
  funext i
  simp only [headStageWord,goodColumnWord_apply,Bool.false_eq_true,ite_false,ite_true,lt_irrefl]
  split <;> simp_all

theorem descendingHeadWord_cancel (as : List (Fin rank)) (x : Fin d → R) :
    (as.reverse.flatMap (headStageWord G rank hr minor weights inv false)).foldl (fun y op => op.apply y)
      ((as.flatMap (headStageWord G rank hr minor weights inv true)).foldl (fun y op => op.apply y) x) = x := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
    simp only [List.reverse_cons,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.foldl_append,ih,undoHeadColumn]

open Matrix in
theorem headStages_matrix (units : ∀ i, weights i * inv i = 1) (negative : Bool) (x : Fin d → R) :
    let as := List.finRange rank
    let stage := stageAt G rank hr minor rank le_rfl
    ((if negative then as else as.reverse).flatMap (headStageWord G rank hr minor weights inv negative)).foldl
      (fun y op => op.apply y) x =
      (diagonal weights * (if negative then stage.L' else stage.L) * diagonal inv).mulVec x := by
  intro as stage
  have forward (y : Fin d → R) : (as.flatMap (headStageWord G rank hr minor weights inv true)).foldl
      (fun z op => op.apply z) y = (diagonal weights * stage.L' * diagonal inv).mulVec y := by
    have word := ascendingHeadWord G rank hr minor weights inv rank le_rfl
    change as.flatMap (headStageWord G rank hr minor weights inv true) = _ at word
    rw [word]
    exact goodHeadWord_apply _ _ _ _ _ _ units _ _ _
  cases negative with
  | true => exact forward x
  | false =>
    let y := (diagonal weights * stage.L * diagonal inv).mulVec x
    have undo := descendingHeadWord_cancel G rank hr minor weights inv as y
    rw [forward] at undo
    have cancel : (diagonal weights * stage.L' * diagonal inv).mulVec y = x := by
      simp only [y,mulVec_mulVec]
      rw [show diagonal weights * stage.L' * diagonal inv * (diagonal weights * stage.L * diagonal inv) =
        diagonal weights * (stage.L' * (diagonal inv * diagonal weights) * stage.L) * diagonal inv by
          simp only [Matrix.mul_assoc],
        Weighted.diagonal_inv_mul inv weights (fun i => (mul_comm ..).trans (units i)),
        Matrix.mul_one,stage.left',Matrix.mul_one,Weighted.diagonal_inv_mul weights inv units,one_mulVec]
    rwa [cancel] at undo

end

end IntegerMultBounds.MathlibTM2.Cover.Fallback
