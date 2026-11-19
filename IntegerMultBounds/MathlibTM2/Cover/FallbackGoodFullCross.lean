module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodCrossRun
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadWidth

/-! Read inverse weights from a separate tape while preserving the ordinary adapter layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm FlatCoordinateLayout LabelTraversal
open HeadPivotLayout Matrix M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear
variable {P U α : Type} {T A d W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

namespace CrossWeightLayout
def base : Fin 53 ↪ Fin 54 := Fin.castLEEmb (by decide)
def inverse := base.trans (Equiv.swap 48 53).toEmbedding

private theorem changeWeights {N dim : ℕ} (bank : Fin 54 ↪ Fin T) (negative : Bool) (H J : ℕ)
    (fromHost toHost : Fin 53 ↪ Fin 54)
    (same : ∀ i, i ≠ 48 → fromHost i = toHost i)
    (parent weights : List (Fin (A+4))) (sym : α → Fin 4) (source target : ℤ → Fin 4)
    (p q : ℤ) (word : Fin (N^dim*W) → α) (S : Stacks T A) :
    let h := (coeff negative).trans (fromHost.trans bank)
    let h' := (coeff negative).trans (toHost.trans bank)
    let s := shear.trans (fromHost.trans bank)
    let s' := shear.trans (toHost.trans bank)
    HeadColumnReady h s H J [] parent [] sym source target p q word S →
    S.R (h' 16) = weights → HeadColumnReady h' s' H J [] weights [] sym source target p q word S := by
  intro h h' s s' initial stored
  have hs : s' = s := Function.Embedding.ext fun i => congrArg bank
    (same _ ((by decide : ∀ j, shear j ≠ 48) i)).symm
  have hc (j : Fin 17) (hj : j ≠ 16) : h' j = h j := congrArg bank
    (same _ ((by cases negative <;> decide : ∀ k : Fin 17, k ≠ 16 → coeff negative k ≠ 48) j hj)).symm
  rw [hs]
  exact ⟨by rw [hc 13 (by decide)]; exact initial.stage,stored,
    by rw [hc 14 (by decide)]; exact initial.reciprocal,
    by rw [hc 2 (by decide)]; exact initial.modulus,
    fun j hj => by rw [hc j (by omega)]; exact initial.coeffWork j hj,
    initial.base,initial.one,initial.width,initial.scratch,initial.src,initial.dst⟩
/-- The adapter reserves port 53 for the ordinary record width. Cross corrections
share that placement and take their inverse-weight vector from port 54. -/
def adapterBank : Fin 54 ↪ Fin 55 := Fin.castLEEmb (by decide)
def crossBank : Fin 54 ↪ Fin 55 :=
    (adapterBank.trans (Equiv.swap 53 54).toEmbedding).trans (Equiv.swap 27 53).toEmbedding

theorem sharedHost : base.trans crossBank = HeadWidthLayout.ordinaryHead.trans adapterBank := by
  apply Function.Embedding.ext
  decide

theorem inversePort : crossBank 53 = 54 := by decide
end CrossWeightLayout

theorem fullCross_exec [Fintype P] (body : P → Pr P T 217 A U) (bank : Fin 54 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (idem : G*G = G) (L : Matrix (Fin d) (Fin rank) (ZMod M)) (R : Matrix (Fin rank) (Fin d) (ZMod M))
    (factor : G = L*R) (inv : Fin d → ZMod M)
    (hb : b.Prime) (negative : Bool) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (parent tail dest rest pivotTail : List (Fin (A+4))) (sym : α → Fin 4) (source target : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+d)*W : ℕ) → target z = blank) :
    let host := CrossWeightLayout.base.trans bank
    let crossHost := CrossWeightLayout.inverse.trans bank
    let c := child.trans host
    let h := (coeff negative).trans host
    let s := shear.trans host
    let words := fun j => if hj : j ≤ rank then matrixWords A H (stageAt G rank hr minor j hj).M else []
    let pair := matrixArchive words (words 0 ++ tail) dest rank
    let piv := fun j : Fin rank => (stageAt G rank hr minor rank le_rfl).M (j.castLE hr) (j.castLE hr)
    let inverseWords := (List.ofFn fun j => binSyms H (inv j).val).flatten ++ rest
    let ready : (Fin (M^(d+d)*W) → α) → Stacks T A → Prop := HeadColumnReady (d := d+d) (W := W) h s H J [] parent [] sym source target p q
    let finalStage := stageAt G rank hr minor rank le_rfl
    let δ := fun t : Fin d => if t.val < rank then finalStage.M t t else 1
    let δ' := fun t : Fin d => if t.val < rank then Ring.inverse (finalStage.M t t) else 1
    let K := kMat (pivotMatrix (revPivots d rank))
      (rev d * finalStage.U * rev d * rev d * (finalStage.L * diagonal δ)) * diagonal (fun t => inv t * δ' t)
    let cost := fun a : Fin rank =>
      let k := a.castLE hr
      let rows := (List.finRange d).filter (fun i => rank ≤ i.val)
      let group := fun src => (rows.map fun t => let e := crossPair src k t
                                                 crossShearTime body ((coeff (if src then negative else !negative)).trans crossHost)
                                                   s e.1 e.2 M W H J).sum+1
      (8*((rank-a.val)/2*(d*d*H))+14*(d*d*H)+22 + tailPivotTime b w H a.val) +
        (group true + group false + (2*(d*d*H+3*H)+9))
    let as := List.finRange rank
    ∀ v S word, ready word S → S.R (bank 53) = inverseWords →
      (S.R (host 49),S.R (host 50)) = pair → (S.R (host 51)).length = d*d*H →
      S.R (c 18) = (List.ofFn fun j => binSyms H (piv j).val).flatten ++ pivotTail →
      S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
      ∃ z F n out, z.user = v.user ∧ n ≤ (as.map cost).sum+1 ∧
        Exec body (crossStages b rank hr negative crossHost as) (mk v S) n (mk z F) ∧ ready out F ∧
        (∀ j, (∀ i, s i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ x y j, out (index (Fin.append x (y + (if negative then -K else K).mulVec x)) j) =
          word (index (Fin.append x y) j) := by
  intro host crossHost c h s words pair piv inverseWords ready stage δ δ' K cost as v S word initial stored
    packed count pivots one clock scratch
  have same : ∀ i, i ≠ 48 → CrossWeightLayout.base i = CrossWeightLayout.inverse i := by decide
  have port (j : Fin 53) (hj : j ≠ 48) : crossHost j = host j := congrArg bank (same j hj).symm
  have bankEq : shear.trans crossHost = s := Function.Embedding.ext fun i =>
    port _ ((by decide : ∀ i, shear i ≠ 48) i)
  have coefPort : (coeff negative).trans crossHost 16 = bank 53 :=
    congrArg bank (by cases negative <;> decide)
  have enter := CrossWeightLayout.changeWeights bank negative H J _ _ same parent inverseWords sym
    source target p q word S initial (coefPort ▸ stored)
  have childPort (j : Fin 20) (hj : j ≠ 19) : (child.trans crossHost) j = c j :=
    port _ ((by decide : ∀ k : Fin 20, k ≠ 19 → child k ≠ 48) j hj)
  obtain ⟨z,F,n,out,hz,hn,run,post,frame,effect⟩ := crossStages_exec body crossHost G rank hr minor
    idem L R factor inv hb negative H J hm hw hW tail dest rest pivotTail sym source target p q empty as
    v S word enter (by simpa only [port 49 (by decide),port 50 (by decide)] using packed)
    (by simpa only [port 51 (by decide)] using count)
    (by rw [childPort 18 (by decide)]; exact pivots) (by rw [childPort 15 (by decide)]; exact one)
    (by rw [childPort 16 (by decide)]; exact clock)
    (fun j hj => by rw [childPort j (by omega)]; exact scratch j hj)
  rw [bankEq] at frame
  have keep := (frame (h 16) (fun i => host.injective.ne
    ((by cases negative <;> decide : ∀ j, shear j ≠ coeff negative 16) i))).2
  have restored := CrossWeightLayout.changeWeights bank negative H J _ _ (fun i hi => (same i hi).symm)
    inverseWords parent sym source target p q out F post (keep.trans initial.weights)
  rw [bankEq] at hn
  refine ⟨z,F,n,out,hz,hn,run,restored,frame,?_⟩
  intro x y j
  have act := effect (Fin.append x y) j
  rw [goodCrossStages_apply G rank hr minor idem L R factor inv negative x y] at act
  exact act

end IntegerMultBounds.MathlibTM2.Cover.Fallback
