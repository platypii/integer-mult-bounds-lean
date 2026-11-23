module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalChildMerge
public import IntegerMultBounds.MathlibTM2.M6.BitStoppedRoleHandoff

/-! Execute packed recursive children on the scheduled idle owners. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks RecursiveInterchangeLayout
open Stack Host Cover.Fallback
open Shared50ModularControl (prime)

theorem packedIdleWorker {P U : Type} {B Q atom price : ℕ} (i : Fin 9) (j : Fin 222) (w W : ℕ)
    (positive : 0 < W) (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P B Q prime U} {code src dst seed} :
    let e := idleInterval i j
    let lane := phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64
    let V := (prime^(w+1))^128*W
    let m := (prime^(w+1))^128*(W*142080)
    lane.width = 64*atom →
    PackedPieceHandoff V (packedChildOutput atom _) body code src dst seed price →
    ∃ (H : ℕ) (slot : Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
      (program : Pr (Empty ⊕ P) H Q prime U) (stock : Stacks H prime),
    ∀ (x : Fin m → ZMod 2) u (S : Stacks H prime), S.L slot = [] →
      S.R slot = List.ofFn (fun k => SparseRoleCircuit.encode (x k)) →
      (∀ k, k ≠ slot → S.L k = stock.L k ∧ S.R k = stock.R k) →
      ∃ z F n y, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (149*(intervalSplitTapes+5)+5)*(V*142080)+24 + ((21*(w+1)+13) +
          (intervalChildToll U (e.1+1) (e.2+1) w W + price + (149*(V*142080)*(intervalSplitTapes+5)+6))) ∧
        z.user = u.user ∧ RecordPayload slot (fun _ => blank) 0 y F ∧ parentIntervalRead i j (w+1) (W*142080) x y := by
  intro e lane V m width child
  have ordered := Nat.succ_le_succ (idleBounds i j).1
  have fits := Nat.succ_le_succ (idleBounds i j).2
  obtain ⟨H,host,program,bank,stock,run⟩ := packedInterval_exec capacity mergeCap ordered fits positive width child
  refine ⟨H,bank 0,host,program,stock,?_⟩
  let wide := {lane with afterD := lane.afterD*142080}
  have size : volume prime lane = V := intervalChild_volume ordered fits (w+1) W
  have interleave : volume prime lane*142080 = volume prime wide := by simp [wide,volume,Nat.mul_assoc]
  have physical : volume prime wide = m := by rw [← interleave,size]; exact Nat.mul_assoc _ _ _
  apply transportWorker physical _ host program stock (parentIntervalRead i j (w+1) (W*142080))
  intro x u S left right ready
  obtain ⟨z,F,n,exec,paid,user,result⟩ := run x u S left
    (right.trans (castWord interleave (fun k => SparseRoleCircuit.encode (x k))).symm) ready
  refine ⟨z,F,n,Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x,exec,?_,user,?_,?_⟩
  · rw [← size]
    exact paid
  · exact castPayload interleave _ _ _ (mergedPayload bank F _ _ result)
  · exact idleInterleaved_read i j (w+1) W x

/-- The ordinary leaf supplies the same scheduled owner read at a stopped
width, including widths that do not split into another 64-axis node. -/
theorem stoppedIdleWorker [M8.Machine.Net] {U : Type} (minimum : ℝ := 0) :
    ∃ rate : ℝ, 0 ≤ rate ∧ minimum ≤ rate ∧ ∀ {Q : ℕ} (i : Fin 9) (j : Fin 222) (w W : ℕ),
    0 < W → columnCapacity ≤ Q →
    (let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) →
    let e := idleInterval i j
    let lane := phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64
    let V := (prime^(w+1))^128*W
    let m := (prime^(w+1))^128*(W*142080)
    0 < lane.width →
    let leaf := ⌊(rate*(lane.width : ℝ)^M8.Machine.BudgetBound.tau)*(V*142080 : ℕ)⌋₊
    ∃ (P : Type) (H : ℕ) (slot : Fin H) (host : P → Pr P H Q prime U)
      (program : Pr P H Q prime U) (stock : Stacks H prime),
    ∀ (x : Fin m → ZMod 2) u (S : Stacks H prime), S.L slot = [] →
      S.R slot = List.ofFn (fun k => SparseRoleCircuit.encode (x k)) →
      (∀ k, k ≠ slot → S.L k = stock.L k ∧ S.R k = stock.R k) →
      ∃ z F n y, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (149*(intervalSplitTapes+5)+5)*(V*142080)+24+
          ((142081*(8*V+10)+1+leaf)+(149*(V*142080)*(intervalSplitTapes+5)+6)) ∧
        z.user = u.user ∧ RecordPayload slot (fun _ => blank) 0 y F ∧ parentIntervalRead i j (w+1) (W*142080) x y := by
  obtain ⟨rate,nonneg,build⟩ := stoppedRoleCost (U := U)
  refine ⟨max rate minimum,nonneg.trans (le_max_left _ _),le_max_right _ _,?_⟩
  intro Q i j w W positive capacity mergeCap e lane V m width leaf
  have size : volume prime lane = V := intervalChild_volume
    (Nat.succ_le_succ (idleBounds i j).1) (Nat.succ_le_succ (idleBounds i j).2) (w+1) W
  have vol : 0 < volume prime lane := size ▸ Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive
  obtain ⟨price,paid,P,B,body,code,src,dst,seed,run⟩ :=
    build capacity lane lane vol width (Equiv.refl _) rfl (fun _ => rfl)
  have child : PackedPieceHandoff (volume prime lane) (fun x y => ∀ r : Fin 142080, y r.castSucc =
      Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc)) body code src dst seed leaf := by
    intro x u S words fresh
    obtain ⟨z,F,n,y,ran,bill,user,out,reads⟩ := run x u S words fresh
    refine ⟨z,F,n,y,ran,bill.trans (Nat.le_floor ?_),user,out,fun r => funext (reads r)⟩
    rw [← size]
    exact paid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Nat.cast_nonneg _))
  obtain ⟨host,program,stock,execute⟩ := inheritedSeededWorker_exec lane
    (inheritedIdleCopy_exec i j (w+1) W positive mergeCap child)
  let wide := {lane with afterD := lane.afterD*142080}
  have physical : volume prime wide = m := by
    change _ = (prime^(w+1))^128*(W*142080)
    rw [← Nat.mul_assoc]
    change _ = V*142080
    rw [← size]
    simp [wide,volume,Nat.mul_assoc]
  refine ⟨_,_,((0 : Fin intervalSplitTapes).natAdd 142082).castAdd B,host,program,stock,?_⟩
  apply transportWorker physical _ host program stock (parentIntervalRead i j (w+1) (W*142080))
  rw [← size]
  exact execute

noncomputable def idleCutoffCharge (U : Type) (i : Fin 9) (w W cutoff : ℕ) (rate : ℝ)
    (k : (Fin 32 × Fin 5) × Fin 222) (price : ℕ) : ℕ :=
  let e := idleInterval i k.2
  let lane := phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64
  let V := (prime^(w+1))^128*W
  (149*(intervalSplitTapes+5)+5)*(V*142080)+24 + (if cutoff < lane.width then (21*(w+1)+13) +
    (intervalChildToll U (e.1+1) (e.2+1) w W + price + (149*(V*142080)*(intervalSplitTapes+5)+6))
    else (142081*(8*V+10)+1+⌊(rate*(lane.width : ℝ)^M8.Machine.BudgetBound.tau)*(V*142080 : ℕ)⌋₊)+
      (149*(V*142080)*(intervalSplitTapes+5)+6))

/-- The physical idle lane has the directory rank times the atom width.
Its rank is positive and at most 42, so recursive calls strictly decrease. -/
theorem idleLaneWidth (i : Fin 9) (k : (Fin 32 × Fin 5) × Fin 222) (w W : ℕ) :
    let e := idleInterval i k.2
    let lane := phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64
    let index := idleDirectoryIndex (i,idleCopyIndex k)
    lane.width = nodeChildren5[index.val]*(w+1) ∧
      0 < lane.width ∧ lane.width < 64*(w+1) := by
  intro e lane index
  have rank := idleDirectoryIndex_rank i (idleCopyIndex k)
  rw [idleCopyIndex_get] at rank
  have width : lane.width = nodeChildren5[index.val]*(w+1) := by
    change ((e.2+1)-(e.1+1))*(w+1) = _
    rw [Nat.add_sub_add_right]
    exact congrArg (·*(w+1)) rank.symm
  obtain ⟨pos,cap⟩ := nodeChildren5_bounds index
  exact ⟨width,width ▸ Nat.mul_pos pos (Nat.succ_pos w),
    width ▸ Nat.mul_lt_mul_of_pos_right (cap.trans_lt (by decide : 42 < 64)) (Nat.succ_pos w)⟩

/-- Install stopped or packed children at the cutoff and return the exact words
needed by the following node stage. -/
theorem mixedIdleWindow {U : Type} (minimum : ℝ := 0) :
    ∃ rate : ℝ, 0 ≤ rate ∧ minimum ≤ rate ∧ ∀ {Q : ℕ} (i : Fin 9) (w W : ℕ), 0 < W → columnCapacity ≤ Q →
    rowSwapBlock.states ≤ Q → (let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) →
    let Job := (Fin 32 × Fin 5) × Fin 222
    let V := (prime^(w+1))^128*W
    let m := (prime^(w+1))^128*(W*142080)
    let lane := fun k : Job => let e := idleInterval i k.2; phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64
    ∀ (cutoff : ℕ) (atom price : Job → ℕ),
      (∀ k, cutoff < (lane k).width → (lane k).width = 64*atom k) →
      (∀ k, cutoff < (lane k).width → ∃ (P : Type) (B : ℕ) (body : P → Pr P B Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (packedChildOutput (atom k) _) body code src dst seed (price k)) →
      let charge := fun k => idleCutoffCharge U i w W cutoff rate k (price k)
      PackedWindowHandoff U Q m (fun x y => ∀ j : Fin (W*142080),
        let addr := fun z => flatWindowEquiv (w+1) (W*142080) (windowState (w+1) z,j)
        readRoles addr y = (Piece.remainder i.val).run (readRoles addr x))
        ((idleCopies.map charge).sum+1+142081*(8*m+10)+1) := by
  obtain ⟨rate,nonneg,enough,leaf⟩ := stoppedIdleWorker (U := U) minimum
  refine ⟨rate,nonneg,enough,?_⟩
  intro Q i w W positive leafCap capacity mergeCap Job V m lane cutoff atom price widths children charge
  have worker (k : Job) : ∃ (P : Type) (H : ℕ) (slot : Fin H) (host : P → Pr P H Q prime U)
      (program : Pr P H Q prime U) (stock : Stacks H prime),
      ∀ (x : Fin m → ZMod 2) u (S : Stacks H prime), S.L slot = [] →
      S.R slot = List.ofFn (fun j => SparseRoleCircuit.encode (x j)) →
      (∀ j, j ≠ slot → S.L j = stock.L j ∧ S.R j = stock.R j) →
      ∃ z F n y, Exec host program (mk u S) n (mk z F) ∧ n ≤ charge k ∧ z.user = u.user ∧
        RecordPayload slot (fun _ => blank) 0 y F ∧ parentIntervalRead i k.2 (w+1) (W*142080) x y := by
    by_cases active : cutoff < (lane k).width
    · obtain ⟨P,B,body,code,src,dst,seed,child⟩ := children k active
      refine ⟨Empty ⊕ P,?_⟩
      simpa only [charge,idleCutoffCharge,lane,ite_eq_left active] using
        packedIdleWorker i k.2 w W positive capacity mergeCap (widths k active) child
    · simpa only [charge,idleCutoffCharge,lane,ite_eq_right active] using leaf i k.2 w W positive leafCap mergeCap (idleLaneWidth i k w W).2.1
  choose P H slot host program stock run using worker
  obtain ⟨T,fan,table,window,prepared,exec⟩ := allocatedIdleWindow_exec (V := m) i H P slot host program stock
    charge (fun k => parentIntervalRead i k.2 (w+1) (W*142080)) run
  obtain ⟨out,initial,handoff⟩ := flatWordStageHandoff fan table window prepared
    (fun x y => (∀ k, parentIntervalRead i k.2 (w+1) (W*142080) (x (idleTape i k)) (y (idleTape i k))) ∧
      ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j) (((idleCopies.map charge).sum+1 : ℕ) : ℝ) (by
    intro x u D words fresh
    obtain ⟨F,z,n,y,ran,paid,result⟩ := exec x D u words.helperFan
      (fun k => ⟨words.left (idleTape i k),words.right (idleTape i k)⟩) fresh
    exact ⟨z,F,n,y,ran,by exact_mod_cast paid,result⟩)
  refine ⟨_,_,fun f => embProg (SweepFile.Exit.chart 0 T) id (table f),out,fan.trans (SweepFile.Exit.chart 0 T),returnedFan fan,initial,?_⟩
  intro x u S words fresh
  obtain ⟨z,F,n,y,ran,paid,user,returned,acts,off⟩ := handoff x u S words fresh
  exact ⟨z,F,n,y,ran,by simpa only [Nat.floor_natCast] using paid,user,returned,
    parentIdleWindow_read i (w+1) (W*142080) x y acts off⟩

/-- Assemble the nine sweeps with their cutoff-selected idle remainders.
The leaf coefficient and state capacity apply at every aligned width. -/
theorem mixedFlatNode {U : Type} (minimum : ℝ := 0) :
    ∃ (states : ℕ) (rate : ℝ), 0 ≤ rate ∧ minimum ≤ rate ∧ ∀ {Q w W : ℕ}, states ≤ Q → 0 < W →
    let Job := (Fin 32 × Fin 5) × Fin 222
    let V := (prime^(w+1))^128*W
    let m := (prime^(w+1))^128*(W*142080)
    let lane := fun i (k : Job) => let e := idleInterval i k.2; phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64
    ∀ (cutoff : ℕ) (atom price : Fin 9 → Job → ℕ) (sweep : Fin 9 → ℕ),
      (∀ i k, cutoff < (lane i k).width → (lane i k).width = 64*atom i k) →
      (∀ i k, cutoff < (lane i k).width → (lane i k).width < 64*(w+1) → PackedWindowHandoff U Q V (packedChildOutput (atom i k) V) (price i k)) →
      (∀ i, PackedWindowHandoff U Q m (fun x y => ∀ j : Fin (W*142080),
        let addr := fun z => flatWindowEquiv (w+1) (W*142080) (windowState (w+1) z,j)
        readRoles addr y = (Piece.stage i).run (readRoles addr x)) (sweep i)) →
      let idle := fun i => (idleCopies.map (fun k => idleCutoffCharge U i w W cutoff rate k (price i k))).sum+
        1+142081*(8*m+10)+1
      PackedWindowHandoff U Q m (packedChildOutput (w+1) m)
        ((∑ i, sweep i)+(∑ i, idle i)+9*(2*(76*17760*m*(142081+7)+6)+1+(142081*(8*m+10)+1))+2) := by
  obtain ⟨bridge,assemble⟩ := assembledFlatNode (U := U)
  obtain ⟨rate,nonneg,enough,window⟩ := mixedIdleWindow (U := U) minimum
  let q := 7+(CyclicRowCycle.states 142080+5)+4
  refine ⟨max (max bridge columnCapacity) (max rowSwapBlock.states (q+q)),rate,nonneg,enough,?_⟩
  intro Q w W fits pos Job V m lane cutoff atom price sweep aligned children sweeps idle
  have left := (le_max_left _ _).trans fits
  have right := (le_max_right _ _).trans fits
  have hm : 0 < m := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos pos (by decide))
  apply assemble (W := W*142080) ((le_max_left _ _).trans left) rfl hm (Equiv.refl _) sweep idle sweeps
  intro i
  exact window i w W pos ((le_max_right _ _).trans left) ((le_max_left _ _).trans right)
    ((le_max_right _ _).trans right) cutoff (atom i) (price i) (aligned i) (fun k above => children i k above (idleLaneWidth i k w W).2.2)

end IntegerMultBounds.MathlibTM2.M6.BitNode
