module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodHeadLayout
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodTailRow
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodTailPivot

/-! One complete pivot of either unweighted tail adapter on a shared physical bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm FlatCoordinateLayout LabelTraversal
open HeadPivotLayout
variable {P U α : Type} {T A d W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def tailStage (b rank : ℕ) (k : Fin d) (negative : Bool) (host : Fin 53 ↪ Fin T)
    (rows : List (Fin d)) : Pr P T 217 A U :=
  let c := child.trans host
  let r := (reader (decide ((rank-k.val)%2 ≠ 0))).trans host
  .seq (.seq (readMatrixWord ((rank-k.val)/2) r) (signedTailPivot b k.val ((Fin.castLEEmb (by decide)).trans c))) (.seq (tailRowRun k ((coeff negative).trans host)
    (shear.trans host) rows) (Mult.ShortConv.clearWords [host 52,c 0,c 12,c 14]))

theorem tailStage_exec [Fintype P] (body : P → Pr P T 217 A U) (host : Fin 53 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (a : Fin rank)
    (hb : b.Prime) (negative : Bool) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (v : HS T 217 A U) (S : Stacks T A) (tail dest parent pivotTail : List (Fin (A+4)))
    (sym : α → Fin 4) (source target : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^d*W) → α)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → target z = blank) (rows : List (Fin d)) :
    let k := a.castLE hr
    let gap := rank-a.val
    let odd := decide (gap%2 ≠ 0)
    let r := (reader odd).trans host
    let c := child.trans host
    let h := (coeff negative).trans host
    let s := shear.trans host
    let words := fun j => if hj : j ≤ rank then matrixWords A H (stageAt G rank hr minor j hj).M else []
    let pair := matrixArchive words (words 0 ++ tail) dest rank
    let piv := fun j : Fin rank => (stageAt G rank hr minor rank le_rfl).M (j.castLE hr) (j.castLE hr)
    let ready : (Fin (M^d*W) → α) → Stacks T A → Prop := HeadColumnReady (d := d) (W := W) h s H J [] parent [] sym source target p q
    S.R (r 2) = (if gap%2 = 0 then pair.1 else pair.2) →
    (S.R (r 1)).length = d*d*H →
    S.R (c 18) = (List.ofFn fun j => binSyms H (piv j).val).flatten ++ pivotTail →
    S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
    (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
    ready word S → (∀ i ∈ rows, k < i) →
    let stage := (stageAt G rank hr minor a.val a.isLt.le).M
    let coef := fun i => let x := elimU k stage (Ring.inverse (stage k k)) i
                         if negative then -x else x
    ∃ z F n out, z.user = v.user ∧
      n ≤ ((8*(gap/2*(d*d*H))+14*(d*d*H)+22) + tailPivotTime b w H a.val) +
        ((rows.map (tailEntryTime body h s k M W H J)).sum+1+(2*(d*d*H+3*H)+9)) ∧
      Exec body (tailStage b rank k negative host rows) (mk v S) n (mk z F) ∧ ready out F ∧
      (∀ j, (∀ i, s i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
      ∀ x j, out (index ((goodTailRow k coef rows).foldl (fun y op => op.apply y) x) j) =
        word (index x j) := by
  intro k gap odd r c h s words pair piv ready packed count pivots one clock scratch initial above stage coef
  have childSep j : c j ≠ r 3 := host.injective.ne (child_apart odd j)
  have modPort : h 2 = c 4 := by cases negative <;> rfl
  have stagePort : h 13 = r 3 := by cases negative <;> cases odd <;> rfl
  have readFree (j : Fin 7) (hj : j = 0 ∨ 4 ≤ j) : S.R (r j) = [] := by
    obtain ⟨i,eq,free⟩ := (by cases odd <;> decide : ∀ j : Fin 7, j = 0 ∨ 4 ≤ j →
      ∃ i : Fin 20, reader odd j = child i ∧ ((i ≤ 14 ∧ i ≠ 4) ∨ i = 17)) j hj
    exact (congrArg (fun t => S.R (host t)) eq).trans (scratch i free)
  obtain ⟨v',hv,copy⟩ := copyGoodPivotStage_exec body r G rank hr minor a H tail dest v S packed count readFree
  let snap := matrixWords A H (stageAt G rank hr minor a.val a.isLt.le).M
  let B := {S with R := Function.update S.R (r 3) (snap ++ S.R (r 3))}
  have keep (j : Fin 20) : B.R (c j) = S.R (c j) := Function.update_of_ne (childSep j) _ _
  let ports := (Fin.castLEEmb (by decide : 19 ≤ 20)).trans c
  have small : ∀ j : Fin 19, (j < 13 ∧ j ≠ 4) ∨ j = 14 ∨ j = 17 →
      let t := (Fin.castLEEmb (by decide : 19 ≤ 20)) j
      (t ≤ 14 ∧ t ≠ 4) ∨ t = 17 := by decide
  obtain ⟨u,D,l,hu,hl,load,prod,pos,neg,left,_,_,stored⟩ := signedTailPivot_exec body ports piv a
    ((stageAt G rank hr minor rank le_rfl).unit _ a.isLt) hb H hm v' B pivotTail
    ((keep 18).trans pivots) ((keep 4).trans (modPort ▸ initial.modulus)) ((keep 15).trans one)
    (by change (B.R (c 16)).length = w; rw [keep,clock]) (fun j hj => (keep _).trans (scratch _ (small j hj)))
  have mat : D.R (r 3) = words a.val ++ S.R (r 3) := by
    rw [stored _ (childSep 0).symm (childSep 14).symm (childSep 12).symm]
    simp [B,words,snap,a.isLt.le]
  have frame (j) (hs : j ≠ r 3) (h0 : j ≠ c 0) (h14 : j ≠ c 14) (h12 : j ≠ c 12) :
      D.R j = S.R j := (stored j h0 h14 h12).trans (Function.update_of_ne hs _ _)
  have prepared := ready_after_prepare host odd negative H J S D (words a.val) parent
    (Ring.inverse (piv a)) sym source target p q word initial mat pos neg left frame
  have matrixEq : words a.val = matrixWords A H stage := dite_eq_left a.isLt.le
  rw [matrixEq] at prepared
  obtain ⟨y,E,t,out,hy,ht,run,post,saved,effect⟩ := tailRowRun_exec body G rank hr minor a negative h s
    (congrArg host (shared negative)) (fun j ne i => host.injective.ne (apart negative j ne i))
    H J hm hw hW [] parent sym source target p q empty rows above u D word (by simpa only [List.append_nil] using prepared)
  have outside (j : Fin 53) (hj : ∀ i, shear i ≠ j) := saved (host j) (fun i => host.injective.ne (hj i))
  have childKeep (j : Fin 20) : E.R (c j) = D.R (c j) := (outside (child j) ((by decide : ∀ j i, shear i ≠ child j) j)).2
  have len : (E.R (host 52)).length = d*d*H := by
    have eq : h 13 = host 52 := by cases negative <;> rfl
    rw [← eq,post.stage]
    simp [matrixWords,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const,Nat.mul_assoc]
  have lengths (j : Fin 20) (hj : j = 0 ∨ j = 12 ∨ j = 14) : (E.R (c j)).length = H := by
    rw [childKeep]
    rcases hj with rfl | rfl | rfl
    · exact (congrArg List.length pos).trans (length_binSyms ..)
    · exact (congrArg List.length neg).trans (length_binSyms ..)
    · exact (congrArg List.length prod).trans (length_binSyms ..)
  have stageEq : r 3 = host 52 := by cases odd <;> rfl
  obtain ⟨z,hz,clear⟩ := clearHeadPivot_exec body (host 52) c (stageEq ▸ childSep) H (d*d*H) y E len lengths
  refine ⟨z,_,_,out,hz.trans (hy.trans (hu.trans hv)),Nat.add_le_add (Nat.add_le_add_left hl _) (Nat.add_le_add_right ht _),
    Exec.seq (Exec.seq copy load) (Exec.seq run clear),ready_after_clear host negative H J E _ parent _ sym source target p q out post,?_,effect⟩
  intro j hj
  refine ⟨(saved j hj).1.trans (congrFun left j),?_⟩
  have stageEmpty : S.R (host 52) = [] := stageEq ▸ stagePort ▸ initial.stage
  change (if j ∈ [host 52,c 0,c 12,c 14] then [] else E.R j) = S.R j
  split
  · rename_i mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl
    · exact stageEmpty.symm
    all_goals exact (scratch _ (by decide)).symm
  · rename_i miss
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at miss
    exact (saved j hj).2.trans (frame _ (stageEq ▸ miss.1) miss.2.1 miss.2.2.2 miss.2.2.1)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
