module

public import IntegerMultBounds.MathlibTM2.M6.BitChildDirectoryBill
public import IntegerMultBounds.MathlibTM2.M6.BitStoppedRoleHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitPackedFlatStage

/-! Present a packed stage in the flat node's word length and address order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host M8.RevMachine Certificates.PR589
open Shared50ModularControl (prime)

private theorem pack {P U : Type} {T Q V price : ℕ} {effect}
    {body : P → Pr P T Q prime U} {code src dst seed}
    (run : PackedPieceHandoff V effect body code src dst seed price) :
    PackedWindowHandoff U Q V effect price := ⟨P,T,body,code,src,dst,seed,run⟩

private theorem sweepCast {U : Type} {Q w W V price : ℕ} (n : Fin 9)
    (size : (prime^w)^128*W = V) :
    PackedWindowHandoff U Q V (fun x y => ∀ j : Fin W,
      let addr := fun z => (flatWindowEquiv w W (windowState w z,j)).cast size
      readRoles addr y = (Piece.stage n).run (readRoles addr x)) price →
    PackedWindowHandoff U Q ((prime^w)^128*W) (fun x y => ∀ j : Fin W,
      let addr := fun z => flatWindowEquiv w W (windowState w z,j)
      readRoles addr y = (Piece.stage n).run (readRoles addr x)) price := by
  subst V
  exact id

theorem flatSweepFromPacked [M8.Machine.Net] :
    ∃ (C : ℝ) (base nt states : ℕ), ∀ {Q h B rows : ℕ} {P U : Type}
    (node : RecursiveInterchangeLayout.Descriptor) (n : Fin 9)
    (tapes : StageRun → ℕ) (body : ∀ p, P → Pr P (tapes p) Q prime U)
    (coeff : StageRun → ℝ) (required : (ℕ → ℕ) → Prop),
    (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080) ≤ Q →
    node.width = 64*(h+1) → node.rows = 142080*rows → node.beforeH = B*prime^(64*((h+1)*64)) →
    let w := h+1
    let K := node.beforeRows*rows*node.between*node.afterD
    let W := B*prime^(64*(w*64))*K
    let V := (prime^w)^128*W
    states ≤ Q → 0 < B → 0 < K → ({node with rows := rows} : RecursiveInterchangeLayout.Descriptor).Positive →
    PackedStageExecution (w := w) (B := B) (K := K) n tapes body coeff required →
    ∀ childTime, required childTime →
    let children := ((List.range' (stageChildStart n)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map childTime).sum
    PackedWindowHandoff U Q V (fun x y => ∀ j : Fin W,
      let addr := fun z => flatWindowEquiv w W (windowState w z,j)
      readRoles addr y = (Piece.stage n).run (readRoles addr x))
      (⌊(stageSetupCost base nt V w : ℝ)+(C+|stagePackingRate n+(stageRuns.map coeff).sum|)*V*(w : ℝ)^M8.Machine.BudgetBound.tau+children⌋₊+
        142081*(8*V+10)+1) := by
  obtain ⟨C,base,nt,states,execute⟩ := packedFlatStage_cost
  refine ⟨C,base,nt,states,?_⟩
  intro Q h B rows P U node n tapes body coeff required cap width split label w K W V fits hB hK positive packed time ready children
  obtain ⟨T,fan,bank,run⟩ := execute node n tapes body coeff required cap width split label fits hB hK positive packed
  obtain ⟨t₁,t₂,mid,outer,code,seed,work⟩ := run time ready
  let packedV := (prime^w)^16*((prime^w)^112*B*prime^(64*(w*64))*K)
  have size : V = packedV := (ordinaryCompact_width (prime^w) W).symm.trans (by simp [packedV,W,Nat.mul_assoc])
  apply sweepCast n size
  obtain ⟨program,initial,handoff⟩ := flatStageHandoff _ _ code seed _ _ work
  let bill (v : ℕ) := ⌊(stageSetupCost base nt v w : ℝ)+(C+|stagePackingRate n+(stageRuns.map coeff).sum|)*v*(w : ℝ)^M8.Machine.BudgetBound.tau+children⌋₊+142081*(8*v+10)+1
  change PackedWindowHandoff U Q packedV _ (bill V)
  rw [congrArg bill size]
  exact pack handoff

open RecursiveInterchangeLayout

theorem handoff_le {U : Type} {Q V p q : ℕ} {effect}
    (run : PackedWindowHandoff U Q V effect p) (paid : p ≤ q) : PackedWindowHandoff U Q V effect q := by
  obtain ⟨P,T,body,code,src,dst,seed,exec⟩ := run
  refine ⟨P,T,body,code,src,dst,seed,?_⟩
  intro x u S words fresh
  obtain ⟨z,F,n,y,ran,cost,rest⟩ := exec x u S words fresh
  exact ⟨z,F,n,y,ran,cost.trans paid,rest⟩

private theorem sumNodeCosts (s i a b : Fin 9 → ℕ) (total : ℕ)
    (partition : (∑ j, a j) + (∑ j, b j) = total) :
    (∑ j, (s j + a j)) + (∑ j, (b j + i j)) = (∑ j, s j) + (∑ j, i j) + total := by
  simp only [Finset.sum_add_distrib]
  omega

private theorem collectIdle (r a b : ℕ) :
    r+a+1+b+1 ≤ r+(a+1+b+1) := by omega

theorem collectSweep (C rate power : ℝ) (setup v child copy : ℕ) (positive : 0 ≤ power) :
    ⌊(setup : ℝ)+(C+|rate|)*v*power+child⌋₊+copy+1 ≤ ⌊(setup : ℝ)+(|C|+|rate|)*v*power⌋₊+copy+1+child := by
  have scaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (add_le_add (le_abs_self C) (le_refl |rate|)) (Nat.cast_nonneg v)) positive
  have paid := Nat.floor_mono (add_le_add (add_le_add (le_refl (setup : ℝ)) scaled) (le_refl (child : ℝ)))
  rw [Nat.floor_add_natCast (by positivity : 0 ≤ (setup : ℝ)+(|C|+|rate|)*(v : ℝ)*power)] at paid
  omega

/-- The recursive interval has the directory width and occupies one of
the 142080 owner words of that directory child. -/
theorem alignedIntervalMeasures (node : Descriptor) (w groups W : ℕ) (hw : 0 < w)
    (width : node.width = 64*w) (split : node.rows = 142080*(142080*groups))
    (spectator : W = node.beforeRows*groups*node.beforeH*node.between*node.afterD)
    (i : Fin 9) (j : (Fin 32 × Fin 5) × Fin 222) :
    let e := idleInterval i j.2
    let lane := phaseIntervalChild (e.1+1) (e.2+1) w W 64
    let child := scheduledChild prime node (idleDirectoryIndex (i,idleCopyIndex j))
    lane.width = child.width ∧ lane.width < node.width ∧ volume prime lane*142080 = volume prime child := by
  intro e lane child
  have rank := idleDirectoryIndex_rank i (idleCopyIndex j)
  rw [idleCopyIndex_get] at rank
  have bounds := idleBounds i j.2
  refine ⟨?_,?_,?_⟩
  · change ((e.2+1)-(e.1+1))*w = nodeChildren5.get _*(node.width/64)
    rw [Nat.add_sub_add_right,width,Nat.mul_div_cancel_left _ (by decide : 0 < 64),rank]
  · rw [width]
    exact Nat.mul_lt_mul_of_pos_right (by dsimp [lane,e,phaseIntervalChild]; omega) hw
  · apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080)
    rw [(scheduledChild_measures prime node ⟨w,width⟩ ⟨142080*groups,split⟩ _).2]
    rw [show volume prime lane = (prime^w)^128*W from
      intervalChild_volume (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2) w W]
    rw [spectator,volume,width,split,Nat.mul_comm 64 w,pow_mul,show 128 = 64+64 by decide,pow_add]
    ring

/-- The scheduled child's role stream and the physical interval use the
same packed active coordinates after splitting off the child rows. -/
theorem intervalRolePositions (node : Descriptor) (groups : ℕ)
    (split : node.rows = 142080*(142080*groups)) (i : Fin nodeChildren5.length)
    (lane : Descriptor) (size : volume prime lane*142080 = volume prime (scheduledChild prime node i)) :
    let child := role (scheduledChild prime node i) 142080
    ∃ position : Fin (volume prime child) ≃ Fin (volume prime lane),
      InheritedIntervalPositions child lane rfl position := by
  intro child
  have rows : (scheduledChild prime node i).rows = 142080*groups := by
    change node.rows/142080 = _
    rw [split,Nat.mul_div_cancel_left _ (by decide)]
  have equal : volume prime child = volume prime lane := by
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 142080)
    rw [size]
    simp only [child,role,volume,rows,Nat.mul_div_cancel_left _ (by decide : 0 < 142080)]
    ring
  have card := Fintype.card_congr ((CopyChildLayout.packActive child).symm.trans
    ((finCongr equal).trans (CopyChildLayout.packActive lane)))
  simp only [Fintype.card_fin] at card
  let position := (CopyChildLayout.packActive child).trans
    ((finCongr card).trans (CopyChildLayout.packActive lane).symm)
  exact ⟨position,fun j => by simp [position]⟩

/-- Root alignment supplies the sweep dimensions at every active path.
The extra row factor reserves the recursive interval's role stream. -/
theorem scheduledFlatDimensions (root : Descriptor) (path : List (Fin nodeChildren5.length))
    (rootPos : root.Positive) (rootWidth : 0 < root.width)
    (widthStock : 64^(1+path.length) ∣ root.width)
    (rowStock : 142080^(2+path.length) ∣ root.rows)
    (blocks : ℕ) (labels : root.beforeH = blocks*prime^(64*root.width)) :
    let node := path.foldl (scheduledChild prime) root
    ∃ h groups B : ℕ, node.width = 64*(h+1) ∧ node.rows = 142080*(142080*groups) ∧
      node.beforeH = B*prime^(64*((h+1)*64)) ∧ 0 < B ∧
      0 < node.beforeRows*(142080*groups)*node.between*node.afterD ∧
      ({node with rows := 142080*groups} : Descriptor).Positive := by
  induction path generalizing root blocks with
  | nil =>
    simp only [List.length_nil,Nat.add_zero,pow_one] at widthStock rowStock
    obtain ⟨w,width⟩ := widthStock
    obtain ⟨groups,rows⟩ := rowStock
    cases w with
    | zero => omega
    | succ h =>
      have split : root.rows = 142080*(142080*groups) := by simpa only [pow_two,Nat.mul_assoc] using rows
      obtain ⟨pr,rr,ph,pb,pd⟩ := rootPos
      have rg : 0 < 142080*groups := Nat.pos_of_mul_pos_left (split ▸ rr)
      refine ⟨h,groups,blocks,width,split,?_,?_,?_,pr,rg,ph,pb,pd⟩
      · change root.beforeH = blocks*prime^(64*((h+1)*64))
        rw [labels,width,Nat.mul_comm (h+1) 64]
      · exact Nat.pos_of_mul_pos_right (labels ▸ ph)
      · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos pr rg) pb) pd
  | cons i path ih =>
    let child := scheduledChild prime root i
    have nextW := (scheduledChild_alignment prime root (1+path.length)
      (by simpa [Nat.add_assoc] using widthStock)
      (by apply dvd_trans (pow_dvd_pow 142080 (by simp only [List.length_cons]; omega : 1+path.length+1 ≤ 2+(i::path).length)) rowStock) i).1
    have rowPower : 142080^((2+path.length)+1) ∣ root.rows := by simpa [Nat.add_assoc] using rowStock
    obtain ⟨count,hcount⟩ := rowPower
    have nextR : 142080^(2+path.length) ∣ child.rows := by
      change _ ∣ root.rows/142080
      rw [hcount,pow_succ',Nat.mul_assoc,Nat.mul_div_cancel_left _ (by decide : 0 < 142080)]
      exact dvd_mul_right _ _
    have widthD : 64 ∣ root.width := dvd_trans (dvd_pow_self _ (by simp)) widthStock
    have rowsD : 142080 ∣ root.rows := dvd_trans (dvd_pow_self _ (by simp)) rowStock
    obtain ⟨measure,vol⟩ := scheduledChild_measures prime root widthD rowsD i
    have positive : child.Positive := LeafCore.positive_of_volume (Nat.pos_of_mul_pos_right
      (vol.symm ▸ (show 0 < volume prime root by
        obtain ⟨pr,rr,ph,pb,pd⟩ := rootPos
        dsimp [volume]; have := Shared50ModularControl.prime_prime.pos; positivity)))
    have cw : 0 < child.width := Nat.pos_of_mul_pos_right
      (measure.symm ▸ Nat.mul_pos (nodeChildren5_bounds i).1 rootWidth)
    have le : child.width ≤ root.width := by
      have bound := Nat.mul_le_mul_right root.width (nodeChildren5_le i)
      change child.width*64 = _ at measure
      omega
    apply ih child positive cw nextW nextR (blocks*prime^(64*(root.width-child.width)))
    change root.beforeH = _
    rw [labels,Nat.mul_assoc,← pow_add,← Nat.mul_add,Nat.sub_add_cancel le]

/-- A root with one spare row-splitting level supplies both row splits at
every node that actually recurses above the cutoff. -/
theorem activeFlatDimensions (root : Descriptor) (depth cutoff blocks : ℕ)
    (positive : root.Positive) (width : 0 < root.width)
    (widthStock : 64^depth ∣ root.width) (rowStock : 142080^(depth+1) ∣ root.rows)
    (labels : root.beforeH = blocks*prime^(64*root.width))
    (stop : root.width*42^depth ≤ cutoff*64^depth) (path : List (Fin nodeChildren5.length))
    (active : cutoff < (path.foldl (scheduledChild prime) root).width) :
    let node := path.foldl (scheduledChild prime) root
    ∃ h groups B : ℕ, node.width = 64*(h+1) ∧ node.rows = 142080*(142080*groups) ∧
      node.beforeH = B*prime^(64*((h+1)*64)) ∧ 0 < B ∧
      0 < node.beforeRows*(142080*groups)*node.between*node.afterD ∧
      ({node with rows := 142080*groups} : Descriptor).Positive := by
  have short := scheduledPath_length_lt prime root depth cutoff stop path active
  exact scheduledFlatDimensions root path positive width
    ((pow_dvd_pow 64 (by omega)).trans widthStock)
    ((pow_dvd_pow 142080 (by omega)).trans rowStock) blocks labels

/-- At two aligned row levels the packed stage and the recursive interval
window see the same spectator cells. Their bills use one child directory. -/
theorem alignedFlatNode [M8.Machine.Net] {U : Type} :
    ∃ (C leafRate : ℝ) (base nt states : ℕ), 0 ≤ leafRate ∧ ∀ {Q h B groups cutoff : ℕ}, states ≤ Q →
    ∀ (node : Descriptor), node.width = 64*(h+1) → node.rows = 142080*(142080*groups) →
    node.beforeH = B*prime^(64*((h+1)*64)) →
    let w := h+1
    let rows := 142080*groups
    let K := node.beforeRows*rows*node.between*node.afterD
    let W := B*prime^(64*(w*64))*(node.beforeRows*groups*node.between*node.afterD)
    let V := (prime^w)^128*W
    let m : ℕ := (prime^w)^128*(W*142080)
    let lane := fun i j => let e := idleInterval i j; phaseIntervalChild (e.1+1) (e.2+1) w W 64
    0 < B → 0 < K → ({node with rows := rows} : Descriptor).Positive →
    ∀ (P : Fin 9 → Type) (t : Fin 9 → StageRun → ℕ)
      (body : ∀ i j, P i → Pr (P i) (t i j) Q prime U) (coeff : Fin 9 → StageRun → ℝ)
      (required : Fin 9 → (ℕ → ℕ) → Prop) (recursiveBudget : Fin nodeChildren5.length → ℕ)
      (rate : ℝ), leafRate ≤ rate →
    let budget := fun k => let child := scheduledChild prime node k
      if child.width ≤ cutoff then ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
      else recursiveBudget k
    let time := fun n => if h : n < nodeChildren5.length then budget ⟨n,h⟩ else 0
    (∀ i, PackedStageExecution (w := w) (B := B) (K := K) i (t i) (body i) (coeff i) (required i)) →
    (∀ i, required i time) →
    let sweep : Fin 9 → ℕ := fun i =>
      ⌊(stageSetupCost base nt m w : ℝ)+(C+|stagePackingRate i+(stageRuns.map (coeff i)).sum|)*m*(w : ℝ)^M8.Machine.BudgetBound.tau⌋₊+
        142081*(8*m+10)+1
    (∀ i (j : (Fin 32 × Fin 5) × Fin 222),
      let child := scheduledChild prime node (idleDirectoryIndex (i,idleCopyIndex j))
      cutoff < child.width → (lane i j.2).width = child.width → (lane i j.2).width < node.width →
      volume prime (lane i j.2)*142080 = volume prime child →
      let stream := role child 142080
      ∀ position : Fin (volume prime stream) ≃ Fin (volume prime (lane i j.2)),
      InheritedIntervalPositions stream (lane i j.2) rfl position →
      PackedWindowHandoff U Q (volume prime (lane i j.2)) (fun x y =>
        ∀ (r : Fin 142080) j, y r.castSucc (position j) =
          Shared50RecursiveNodeRows.transpose (one_dvd stream.rows) (x r.castSucc ∘ position) j)
      (recursiveBudget (idleDirectoryIndex (i,idleCopyIndex j)))) →
    let idle := fun _ : Fin 9 =>
      35520 * (((298*(intervalSplitTapes+5)+5)*142080+142081*8)*V + (142081*10+31)) +
      1 + 142081*(8*m+10)+1
    PackedWindowHandoff U Q m (packedChildOutput w m)
      ((∑ i, sweep i)+(∑ i, idle i)+(∑ j, budget j)+9*(2*(76*17760*m*(142081+7)+6)+1+(142081*(8*m+10)+1))+2) := by
  obtain ⟨C,base,nt,stageStates,stage⟩ := flatSweepFromPacked
  obtain ⟨nodeStates,assemble⟩ := flatNodeFromIntervals (U := U)
  let divStates := (fun {q : ℕ} (_ : Program 38 q prime) => q) (RecursiveRowsNodeHeaders.program 142080)
  obtain ⟨leafRate,nonneg,atCutoff⟩ := roleHandoffAtCutoff (U := U)
  refine ⟨|C|,leafRate,base,nt,max Cover.Fallback.columnCapacity (max nodeStates (max divStates stageStates)),nonneg,?_⟩
  intro Q h B groups cutoff fits node width split label w rows K W V m lane hB hK pos P t body coeff required recursiveBudget rate rateBound budget time runs ready sweep children idle
  have shape : B*prime^(64*(w*64))*K = W*142080 := by dsimp only [K,W,rows]; ac_rfl
  have positive : 0 < W*142080 := shape ▸ Nat.mul_pos (Nat.mul_pos hB (pow_pos Shared50ModularControl.prime_prime.pos _)) hK
  have capacity := (le_max_left _ _).trans fits
  have fits := (le_max_right _ _).trans fits
  have caps := (le_max_right _ _).trans fits
  let charged (i : Fin 9) := ((List.range' (stageChildStart i)
    (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum
  let rest (i : Fin 9) := ∑ j : Fin idleCopies.length, budget (idleDirectoryIndex (i,j))
  have partition := nodeChildDirectoryBill time
  simp only [time,Fin.isLt,dite_eq_left,Fin.eta] at partition
  have total := sumNodeCosts sweep idle charged rest _ partition
  rw [← total]
  have nodeRun := assemble (w := w) ((le_max_left _ _).trans fits)
    (Nat.pos_of_mul_pos_right positive) budget (fun i => sweep i + charged i)
  have spectator : W = node.beforeRows*groups*node.beforeH*node.between*node.afterD := by
    rw [label]
    dsimp only [W,w]
    ac_rfl
  apply handoff_le (nodeRun ?_ (fun i j => by
    obtain ⟨same,smaller,size⟩ := alignedIntervalMeasures node w groups W (Nat.succ_pos h) width split spectator i j
    obtain ⟨position,coords⟩ := intervalRolePositions node groups split _ _ size
    let child := scheduledChild prime node (idleDirectoryIndex (i,idleCopyIndex j))
    have childWidth : 0 < child.width := by
      have rank := (nodeChildren5_bounds (idleDirectoryIndex (i,idleCopyIndex j))).1
      change 0 < nodeChildren5.get _ * (node.width/64)
      rw [width,Nat.mul_div_cancel_left _ (by decide)]
      exact Nat.mul_pos rank (Nat.succ_pos h)
    have laneVolume : 0 < volume prime (lane i j.2) := by
      have bounds := idleBounds i j.2
      rw [show volume prime (lane i j.2) = (prime^w)^128*W from
        intervalChild_volume (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2) w W]
      exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.pos_of_mul_pos_right positive)
    obtain ⟨L,T,b,c,src,dst,seed,exec⟩ := atCutoff capacity child (lane i j.2) cutoff (budget (idleDirectoryIndex (i,idleCopyIndex j)))
      position laneVolume childWidth same size coords (by
        intro stopped
        change _ ≤ (if child.width ≤ cutoff then _ else _)
        rw [if_pos stopped]
        exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right rateBound (by positivity)) (Nat.cast_nonneg _))) (by
        intro active
        simpa only [budget,child,if_neg (Nat.not_le_of_lt active)] using
          children i j active same smaller size position coords)
    refine ⟨L,T,b,c,src,dst,seed,?_⟩
    intro x u S words fresh
    obtain ⟨z,F,n,y,ran,paid,user,out,reads⟩ := exec x u S words fresh
    exact ⟨z,F,n,y,ran,paid,user,out,fun r => (coords.transpose_iff same _ _).1 (reads r)⟩))
  · apply Nat.add_le_add_right
    apply Nat.add_le_add_right
    apply Nat.add_le_add_left
    apply Finset.sum_le_sum
    intro i _
    exact collectIdle (rest i) _ _
  · intro i
    have call := stage node i (t i) (body i) (coeff i) (required i) ((le_max_left _ _).trans caps)
      width split label ((le_max_right _ _).trans caps) hB hK pos (runs i) time (ready i)
    let result (suffix : ℕ) := let v := (prime^w)^128*suffix
      PackedWindowHandoff U Q v (fun x y => ∀ j : Fin suffix,
        let addr := fun z => flatWindowEquiv w suffix (windowState w z,j)
        readRoles addr y = (Piece.stage i).run (readRoles addr x))
        (⌊(stageSetupCost base nt v w : ℝ)+(C+|stagePackingRate i+(stageRuns.map (coeff i)).sum|)*v*(w : ℝ)^M8.Machine.BudgetBound.tau+charged i⌋₊+
          142081*(8*v+10)+1)
    apply handoff_le ((congrArg result shape).mp call)
    exact collectSweep C _ _ _ m (charged i) _ (Real.rpow_nonneg (Nat.cast_nonneg w) _)


end IntegerMultBounds.MathlibTM2.M6.BitNode
