module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodCrossStage

/-! Execute successive cross corrections from one fixed archive in either traversal order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host GoodForm FlatCoordinateLayout LabelTraversal
open HeadPivotLayout Matrix M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear
variable {P U α : Type} {T A d W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def crossStages (b rank : ℕ) (hr : rank ≤ d) (negative : Bool) (host : Fin 53 ↪ Fin T) :
    List (Fin rank) → Pr P T 217 A U
  | [] => .act .done
  | a :: as =>
    let k := a.castLE hr
    .seq (crossStage b rank k negative host ((List.finRange d).filter (fun i => rank ≤ i.val)))
      (crossStages b rank hr negative host as)

def crossStagePairs (rank : ℕ) (k : Fin d) :=
  let ts := (List.finRange d).filter (fun i => rank ≤ i.val)
  ts.map (crossPair true k) ++ ts.map (crossPair false k)

private theorem crossStagePairs_mem (rank : ℕ) (k i j : Fin d) :
    (i,j) ∈ crossStagePairs rank k ↔
      (j = k ∧ rank ≤ i.rev.val) ∨ (i.rev = k ∧ rank ≤ j.val) := by
  simp only [crossStagePairs,List.mem_append,List.mem_map,List.mem_filter,List.mem_finRange,
    true_and,decide_eq_true_eq,crossPair,ite_true,Bool.false_eq_true,ite_false,Prod.mk.injEq]
  constructor
  · rintro (⟨t,ht,eq,rfl⟩ | ⟨t,ht,eq,rfl⟩)
    · exact Or.inl ⟨rfl,by simpa [← eq] using ht⟩
    · exact Or.inr ⟨by simp [← eq],ht⟩
  · rintro (⟨rfl,h⟩ | ⟨eq,h⟩)
    · exact Or.inl ⟨i.rev,h,by simp,rfl⟩
    · exact Or.inr ⟨j,h,by simp [← eq],rfl⟩

theorem crossPairs_mem (rank : ℕ) (hr : rank ≤ d) (i j : Fin d) :
    (i,j) ∈ (List.finRange rank).flatMap (fun a => crossStagePairs rank (a.castLE hr)) ↔
      (i.rev.val < rank ↔ ¬ j.val < rank) := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨a,_,ha⟩
    rcases (crossStagePairs_mem ..).mp ha with ⟨eq,hi⟩ | ⟨eq,hj⟩
    · have : j.val < rank := eq ▸ a.isLt
      omega
    · have : i.rev.val < rank := eq ▸ a.isLt
      omega
  · intro mixed
    by_cases h : j.val < rank
    · exact ⟨⟨j.val,h⟩,List.mem_finRange _,(crossStagePairs_mem ..).mpr (.inl ⟨rfl,by omega⟩)⟩
    · exact ⟨⟨i.rev.val,mixed.mpr h⟩,List.mem_finRange _,(crossStagePairs_mem ..).mpr (.inr ⟨rfl,by omega⟩)⟩

theorem crossPairs_nodup (rank : ℕ) (hr : rank ≤ d) :
    ((List.finRange rank).flatMap (fun a => crossStagePairs rank (a.castLE hr))).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro a _
    let ts := (List.finRange d).filter (fun i => rank ≤ i.val)
    have nd : ts.Nodup := (List.nodup_finRange d).filter _
    apply List.nodup_append'.mpr
    refine ⟨nd.map (fun x y eq => ?_),nd.map (fun x y eq => ?_),?_⟩
    · simpa [crossPair] using congrArg (fun e : Fin d × Fin d => e.1.rev) eq
    · exact congrArg Prod.snd eq
    · intro e he he'
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
      obtain ⟨y,hy,eq⟩ := List.mem_map.mp he'
      have val := congrArg (fun e : Fin d × Fin d => e.2.val) eq
      change y.val = a.val at val
      have lo := of_decide_eq_true (List.mem_filter.mp hy).2
      omega
  · apply (List.nodup_finRange rank).imp
    intro a b ne e ha hb
    obtain ⟨i,j⟩ := e
    rcases (crossStagePairs_mem ..).mp ha with ⟨ha,hi⟩ | ⟨ha,hj⟩ <;>
      rcases (crossStagePairs_mem ..).mp hb with ⟨hb,hi'⟩ | ⟨hb,hj'⟩
    all_goals have va := congrArg Fin.val ha; have vb := congrArg Fin.val hb
    all_goals apply ne; apply Fin.ext; simp only [Fin.val_castLE] at va vb; omega

def crossStageWord {R : Type*} (K : Matrix (Fin d) (Fin d) R) (rank : ℕ) (k : Fin d) :=
  let ts := (List.finRange d).filter (fun i => rank ≤ i.val)
  let ops := fun src => ts.map fun t => let e := crossPair src k t
                                        crossEntryShear K e.1 e.2
  ops true ++ ops false

section
variable {R : Type*} [CommRing R]

private theorem crossPairs_apply (K : Matrix (Fin d) (Fin d) R) (es : List (Fin d × Fin d))
    (x y : Fin d → R) :
    (es.map (fun e => crossEntryShear K e.1 e.2)).foldl (fun z op => op.apply z) (Fin.append x y) =
      Fin.append x fun i => y i + (es.map fun e => if e.1 = i then K i e.2*x e.2 else 0).sum := by
  induction es generalizing y with
  | nil => simp
  | cons e es ih =>
    obtain ⟨i,j⟩ := e
    have step := crossRow_apply K i [j] x y
    simp only [List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,List.sum_cons,List.sum_nil,add_zero] at step
    simp only [List.map_cons,List.foldl_cons,step,ih,List.sum_cons]
    congr 1
    funext t
    by_cases eq : i = t
    · simp [eq,add_assoc]
    · simp [eq,Ne.symm eq]

theorem crossStages_apply (K : Matrix (Fin d) (Fin d) R) (rank : ℕ) (hr : rank ≤ d)
    (zero : ∀ i j : Fin d, (i.rev.val < rank ↔ j.val < rank) → K i j = 0)
    (x y : Fin d → R) :
    ((List.finRange rank).flatMap fun a => crossStageWord K rank (a.castLE hr)).foldl
      (fun z op => op.apply z) (Fin.append x y) = Fin.append x (y + K.mulVec x) := by
  let es := (List.finRange rank).flatMap fun a => crossStagePairs rank (a.castLE hr)
  let op := fun e : Fin d × Fin d => crossEntryShear K e.1 e.2
  have schedule : (List.finRange rank).flatMap (fun a => crossStageWord K rank (a.castLE hr)) = es.map op := by
    simp [es,op,crossStageWord,crossStagePairs,List.map_flatMap,List.map_append,List.map_map,Function.comp_def]
  rw [schedule,crossPairs_apply]
  congr 1
  funext i
  apply congrArg (y i + ·)
  let f := fun e : Fin d × Fin d => if e.1 = i then K i e.2*x e.2 else 0
  change (es.map f).sum = _
  rw [← List.sum_toFinset f (crossPairs_nodup rank hr)]
  calc
    _ = ∑ e, f e := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro e _ absent
      have miss : e ∉ es := fun he => absent (List.mem_toFinset.mpr he)
      obtain ⟨t,j⟩ := e
      have h := mt (crossPairs_mem rank hr t j).mpr miss
      by_cases eq : t = i
      · subst t
        simp [zero i j (by omega)]
      · simp [eq]
    _ = _ := by simp [Fintype.sum_prod_type,f,mulVec,dotProduct]

end

theorem goodCrossStages_apply {R : Type*} [CommRing R] (G : Matrix (Fin d) (Fin d) R)
    (rank : ℕ) (hr : rank ≤ d) (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (idem : G*G = G) (L : Matrix (Fin d) (Fin rank) R) (B : Matrix (Fin rank) (Fin d) R)
    (factor : G = L*B) (inv : Fin d → R) (negative : Bool) (x y : Fin d → R) :
    let finalStage := stageAt G rank hr minor rank le_rfl
    let δ := fun t : Fin d => if t.val < rank then finalStage.M t t else 1
    let δ' := fun t : Fin d => if t.val < rank then Ring.inverse (finalStage.M t t) else 1
    let K := kMat (pivotMatrix (revPivots d rank))
      (rev d * finalStage.U * rev d * rev d * (finalStage.L * diagonal δ)) * diagonal (fun t => inv t * δ' t)
    let correction := if negative then -K else K
    ((List.finRange rank).flatMap fun a => crossStageWord correction rank (a.castLE hr)).foldl
      (fun z op => op.apply z) (Fin.append x y) = Fin.append x (y + correction.mulVec x) := by
  intro stage δ δ' K correction
  apply crossStages_apply
  intro i j same
  have entry := archivedCross_entry G rank hr minor idem L B factor inv i j
  have zero : K i j = 0 := by
    change K i j = _ at entry
    by_cases hj : j.val < rank
    · simpa only [hj,same.mpr hj,dite_true,ite_true] using entry
    · simpa only [hj,mt same.mp hj,dite_false,ite_false] using entry
  cases negative <;> simp [correction,zero]

theorem crossStages_exec [Fintype P] (body : P → Pr P T 217 A U) (host : Fin 53 ↪ Fin T)
    (G : Matrix (Fin d) (Fin d) (ZMod M)) (rank : ℕ) (hr : rank ≤ d)
    (minor : ∀ j (hj : j < rank), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
    (idem : G*G = G) (L : Matrix (Fin d) (Fin rank) (ZMod M)) (R : Matrix (Fin rank) (Fin d) (ZMod M))
    (factor : G = L*R) (inv : Fin d → ZMod M)
    (hb : b.Prime) (negative : Bool) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail dest rest pivotTail : List (Fin (A+4))) (sym : α → Fin 4) (source target : ℤ → Fin 4) (p q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+d)*W : ℕ) → target z = blank) :
    let c := child.trans host
    let h := (coeff negative).trans host
    let s := shear.trans host
    let words := fun j => if hj : j ≤ rank then matrixWords A H (stageAt G rank hr minor j hj).M else []
    let pair := matrixArchive words (words 0 ++ tail) dest rank
    let piv := fun j : Fin rank => (stageAt G rank hr minor rank le_rfl).M (j.castLE hr) (j.castLE hr)
    let parent := (List.ofFn fun j => binSyms H (inv j).val).flatten ++ rest
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
                                                 crossShearTime body ((coeff (if src then negative else !negative)).trans host)
                                                   s e.1 e.2 M W H J).sum+1
      (8*((rank-a.val)/2*(d*d*H))+14*(d*d*H)+22 + tailPivotTime b w H a.val) +
        (group true + group false + (2*(d*d*H+3*H)+9))
    ∀ as : List (Fin rank), ∀ v S word, ready word S →
      (S.R (host 49),S.R (host 50)) = pair → (S.R (host 51)).length = d*d*H →
      S.R (c 18) = (List.ofFn fun j => binSyms H (piv j).val).flatten ++ pivotTail →
      S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
      (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
      ∃ z F n out, z.user = v.user ∧ n ≤ (as.map cost).sum+1 ∧
        Exec body (crossStages b rank hr negative host as) (mk v S) n (mk z F) ∧ ready out F ∧
        (∀ j, (∀ i, s i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ x j, out (index ((as.flatMap (fun a => crossStageWord (if negative then -K else K) rank (a.castLE hr))).foldl
          (fun y op => op.apply y) x) j) = word (index x j) := by
  intro c h s words pair piv parent ready finalStage δ δ' K cost as
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
    obtain ⟨u,D,t,out,hu,ht,step,next,frame,effect⟩ := crossStage_exec body host G rank hr minor idem L R factor inv a
      hb negative H J hm hw hW v S tail dest rest pivotTail sym source target p q word empty
      ((List.finRange d).filter (fun i => rank ≤ i.val)) select width pivots one clock scratch initial
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

end IntegerMultBounds.MathlibTM2.Cover.Fallback
