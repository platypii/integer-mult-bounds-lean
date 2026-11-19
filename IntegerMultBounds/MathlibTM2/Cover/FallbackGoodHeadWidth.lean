module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodFullHead

/-! Prepare the widened head-pass header from the ordinary two-field record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host HeadPivotLayout
variable {P U α : Type} {T A d M W : ℕ}

namespace HeadWidthLayout
def head : Fin 53 ↪ Fin 54 := Fin.castLEEmb (by decide)
def entry := (shear.trans head).trans (Equiv.swap 27 53).toEmbedding
def power : Fin 10 ↪ Fin 54 := ⟨![2,53,27,0,1,3,4,5,6,7],by decide⟩
end HeadWidthLayout
open HeadWidthLayout

theorem fullHeadWidth_exec (body : P → Pr P T 217 A U) (host : Fin 54 ↪ Fin T)
    (negative : Bool) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J)
    (matrix parent pivot : List (Fin (A+4))) (sym : α → Fin 4) (src dst : ℤ → Fin 4)
    (p q : ℤ) (word : Fin (M^(d+d)*W) → α) (v : HS T 217 A U) (S : Stacks T A) :
    let h := (coeff negative).trans (head.trans host)
    let s := shear.trans (head.trans host)
    HeadColumnReady h (entry.trans host) H J matrix parent pivot sym src dst p q word S →
    S.R (host 27) = [] →
    let F : Stacks T A := {S with R := Function.update S.R (host 27) (binSyms (d*H+J) (M^d*W))}
    ∃ z t, z.user = v.user ∧ t ≤ dimensionTime H J d ∧
      Exec body (dimensionPower (power.trans host) d) (mk v S) t (mk z F) ∧
      HeadColumnReady h s H (d*H+J) matrix parent pivot sym src dst p q
        (word ∘ Fin.cast (payloadVolume M d d W)) F := by
  intro h s initial empty F
  have free : ∀ i : Fin 10, 2 ≤ i → i < 9 → S.R (host (power i)) = [] := by
    intro i lo hi
    by_cases eq : i = 2
    · subst i; exact empty
    · obtain ⟨j,hj,hij⟩ := (by decide : ∀ i : Fin 10, 2 < i → i < 9 →
          ∃ j ∈ headShearWork, entry j = power i) i (by omega) hi
      rw [← hij]
      exact (initial.scratch j hj).2
  obtain ⟨z,t,hz,ht,run⟩ := dimensionPower_exec body d (power.trans host) H J M W hm hw v S
    initial.base initial.width free
  refine ⟨z,t,hz,ht,run,?_⟩
  have keep (j : Fin 54) (hj : j ≠ 27) : F.R (host j) = S.R (host j) :=
    Function.update_of_ne (host.injective.ne hj) _ _
  have coeffKeep (j : Fin 17) : F.R (h j) = S.R (h j) :=
    keep _ ((by cases negative <;> decide : ∀ k, head (coeff negative k) ≠ 27) j)
  have bankKeep (j : Fin 29) (hj : j ≠ 27) : F.R (s j) = S.R ((entry.trans host) j) := by
    change F.R (s j) = S.R (host (entry j))
    rw [show entry j = head (shear j) from (by decide : ∀ k : Fin 29, k ≠ 27 → entry k = head (shear k)) j hj]
    exact keep _ ((by decide : ∀ k : Fin 29, k ≠ 27 → head (shear k) ≠ 27) j hj)
  refine ⟨(coeffKeep _).trans initial.stage,(coeffKeep _).trans initial.weights,
    (coeffKeep _).trans initial.reciprocal,(coeffKeep _).trans initial.modulus,
    fun j hj => (coeffKeep j).trans (initial.coeffWork j hj),
    (bankKeep 2 (by decide)).trans initial.base,(bankKeep 28 (by decide)).trans initial.one,
    Function.update_self ..,?_,?_,?_⟩
  · intro j hj
    have ne := (by decide : ∀ j ∈ headShearWork, j ≠ 27) j hj
    have same := (by decide : ∀ k : Fin 29, k ≠ 27 → entry k = head (shear k)) j ne
    exact ⟨by simpa only [Function.Embedding.trans_apply,same,s,F] using (initial.scratch j hj).1,
      (bankKeep j ne).trans (initial.scratch j hj).2⟩
  · have castList {m n : ℕ} (eq : m = n) (f : Fin n → Fin 4) :
        List.ofFn (f ∘ Fin.cast eq) = List.ofFn f := by subst n; rfl
    simpa only [← Function.comp_assoc,castList,bankKeep 24 (by decide),show F.L (s 24) = S.L ((entry.trans host) 24) from congrArg (fun k => S.L (host k)) (by decide : head (shear 24) = entry 24)] using initial.src
  · simpa only [bankKeep 25 (by decide),show F.L (s 25) = S.L ((entry.trans host) 25) from congrArg (fun k => S.L (host k)) (by decide : head (shear 25) = entry 25)] using initial.dst

open GoodForm FlatCoordinateLayout LabelTraversal
variable {b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

theorem preparedFullHead_exec [Fintype P] (body : P → Pr P T 217 A U) (bank : Fin 54 ↪ Fin T)
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
    let coeIndex := Fin.cast (payloadVolume M d d W)
    let ready := fun (word : Fin (M^(d+d)*W) → α) =>
      HeadColumnReady (d := d) (W := M^d*W) h s H (d*H+J) [] parent [] sym source target p q (word ∘ coeIndex)
    let cost := fun a : Fin rank =>
      let k := a.castLE hr
      headPivotPrepareTime b d w H a.val (rank-a.val) +
        ((((List.finRange d).filter (k < ·)).map (headRowTime body h s k M (M^d*W) H (d*H+J))).sum+1+(2*(d*d*H+3*H)+9))
    let as := if negative then List.finRange rank else (List.finRange rank).reverse
    ∀ v S (word : Fin (M^(d+d)*W) → α),
      HeadColumnReady h (entry.trans bank) H J [] parent [] sym source target p q word S →
      S.R (bank 27) = [] →
      (S.R (host 49),S.R (host 50)) = pair → (S.R (host 51)).length = d*d*H →
      S.R (c 18) = (List.ofFn fun j => binSyms H (piv j).val).flatten ++ pivotTail →
      S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
      ∃ z F n out, z.user = v.user ∧ n ≤ dimensionTime H J d + ((as.map cost).sum+1) ∧
        Exec body (.seq (dimensionPower (power.trans bank) d) (headStages b rank hr negative host as)) (mk v S) n (mk z F) ∧ ready out F ∧
        (∀ j, (∀ i, s i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        let stage := stageAt G rank hr minor rank le_rfl
        let action := Matrix.diagonal weights * (if negative then stage.L' else stage.L) * Matrix.diagonal inv
        ∀ x y j, out (index (Fin.append (action.mulVec x) y) j) = word (index (Fin.append x y) j) := by
  intro host c h s words pair piv parent coeIndex ready cost as v S word initial free packed count pivots one clock scratch
  let D : Stacks T A := {S with R := Function.update S.R (bank 27) (binSyms (d*H+J) (M^d*W))}
  obtain ⟨u,t,hu,ht,prep,prepared⟩ := fullHeadWidth_exec body bank negative H J hm hw [] parent []
    sym source target p q word v S initial free
  have keep (j : Fin 53) (hj : head j ≠ 27) : D.R (host j) = S.R (host j) :=
    Function.update_of_ne (bank.injective.ne hj) _ _
  have childKeep (j : Fin 20) : D.R (c j) = S.R (c j) :=
    keep _ ((by decide : ∀ k, head (child k) ≠ 27) j)
  obtain ⟨z,F,n,out,hz,hn,run,done,frame,effect⟩ := fullHead_exec body host G rank hr minor weights inv
    inverse hb negative H J hm hw hW tail dest rest pivotTail sym source target p q empty u D word prepared
    (by simpa only [keep 49 (by decide),keep 50 (by decide)] using packed)
    (by simpa only [keep 51 (by decide)] using count)
    ((childKeep 18).trans pivots) ((childKeep 15).trans one) ((congrArg List.length (childKeep 16)).trans clock)
    (fun j hj => (childKeep j).trans (scratch j hj))
  refine ⟨z,F,t+n,out,hz.trans hu,Nat.add_le_add ht hn,Exec.seq prep run,done,?_,effect⟩
  intro j hj
  have outside : j ≠ bank 27 := (hj 27).symm
  exact ⟨(frame j hj).1,(frame j hj).2.trans (Function.update_of_ne outside _ _)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
