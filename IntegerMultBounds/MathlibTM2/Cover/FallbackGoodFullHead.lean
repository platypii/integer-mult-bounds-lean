module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadRun
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodPayload

/-! Apply the head adapter on the whole two-field word using the tail as part of its record width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm FlatCoordinateLayout LabelTraversal
open HeadPivotLayout
variable {P U α : Type} {T A d W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

theorem fullHead_exec [Fintype P] (body : P → Pr P T 217 A U) (host : Fin 53 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (weights inv : Fin d → ZMod M) (inverse : ∀ i, weights i * inv i = 1)
    (hb : b.Prime) (negative : Bool) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail dest rest pivotTail : List (Fin (A+4))) (sym : α → Fin 4) (source target : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+d)*W : ℕ) → target z = blank) :
    let c := child.trans host
    let h := (coeff negative).trans host
    let s := shear.trans host
    let words := fun j => if hj : j ≤ rank then matrixWords A H (stageAt G rank hr minor j hj).M else []
    let pair := matrixArchive words (words 0 ++ tail) dest rank
    let piv := fun j : Fin rank => (stageAt G rank hr minor rank le_rfl).M (j.castLE hr) (j.castLE hr)
    let parent := (List.ofFn fun i => binSyms H (weights i).val).flatten ++ rest
    let coeIndex := Fin.cast (payloadVolume M d d W)
    let ready := fun (word : Fin (M^(d+d)*W) → α) =>
      HeadColumnReady (d := d) (W := M^d*W) h s H (d*H+J) [] parent [] sym source target p q (word ∘ coeIndex)
    let cost := fun a : Fin rank =>
      let k := a.castLE hr
      headPivotPrepareTime b d w H a.val (rank-a.val) +
        ((((List.finRange d).filter (k < ·)).map (headRowTime body h s k M (M^d*W) H (d*H+J))).sum+1+(2*(d*d*H+3*H)+9))
    let as := if negative then List.finRange rank else (List.finRange rank).reverse
    ∀ v S word, ready word S →
      (S.R (host 49),S.R (host 50)) = pair → (S.R (host 51)).length = d*d*H →
      S.R (c 18) = (List.ofFn fun j => binSyms H (piv j).val).flatten ++ pivotTail →
      S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
      ∃ z F n out, z.user = v.user ∧ n ≤ (as.map cost).sum+1 ∧
        Exec body (headStages b rank hr negative host as) (mk v S) n (mk z F) ∧ ready out F ∧
        (∀ j, (∀ i, s i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        let stage := stageAt G rank hr minor rank le_rfl
        let action := Matrix.diagonal weights * (if negative then stage.L' else stage.L) * Matrix.diagonal inv
        ∀ x y j, out (index (Fin.append (action.mulVec x) y) j) = word (index (Fin.append x y) j) := by
  intro c h s words pair piv parent coeIndex ready cost as v S word initial packed count pivots one clock scratch
  have width : M^d*W < 2^(d*H+J) := by
    rw [show 2^(d*H+J) = (2^H)^d * 2^J by simp [pow_add, ← pow_mul, Nat.mul_comm H d]]
    exact (Nat.mul_le_mul_right W (Nat.pow_le_pow_left hm.le d)).trans_lt
      (Nat.mul_lt_mul_of_pos_left hw (by positivity))
  have vol := payloadVolume M d d W
  obtain ⟨z,F,n,result,hz,hn,run,done,frame,effect⟩ := headStages_exec body host G rank hr minor weights inv
    inverse hb negative H (d*H+J) hm width (Nat.mul_pos (pow_pos (NeZero.pos _) _) hW) tail dest rest pivotTail
    sym source target p q (by simpa only [vol] using empty) as v S (word ∘ coeIndex) initial
    packed count pivots one clock scratch
  let out := result ∘ Fin.cast vol.symm
  have restore : out ∘ coeIndex = result := by funext t; rfl
  refine ⟨z,F,n,out,hz,hn,run,?_,frame,?_⟩
  · unfold ready
    rw [restore]
    exact done
  · intro stage action x y j
    apply headPayload_effect action.mulVec word out _ x y j
    intro u t
    have act := effect u t
    rw [headStages_matrix G rank hr minor weights inv inverse negative u] at act
    exact act

end IntegerMultBounds.MathlibTM2.Cover.Fallback
