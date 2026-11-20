module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGeneratedSignedPass

/-! Build the PR589 remainder directory from the inherited parent entries. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.MathlibTM2.Cover Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout Node

private theorem buildCost_le (a w parents box records : ℕ) (count : records = parents*box)
    (fixed : 22*box+8*a+32 ≤ 151*box) :
    8*a+8+22*box + (parents*(6*box+10)+6 + (parents*box*(9*(a*(64*64))+15)+6 +
      (parents*(box*(8*w+11)+6*w+15)+6+parents*box*(6*(w+a*(64*64))+13)+6))) ≤
      directorySetupCost 64 a w parents records 0 box := by
  unfold directorySetupCost inheritedLabelCost
  subst records
  calc
    _ = parents*box*(15*(a*(64*64))+14*w+45) + parents*(6*w+25) + (22*box+8*a+32) := by ring
    _ ≤ _ := by grw [fixed]; ring_nf; omega

private theorem buildCounted {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 15 ↪ Fin T) (atom one : Fin T) (atomOff : ∀ i, atom ≠ r i) (oneOff : ∀ i, one ≠ r i)
    (v : Descriptor) (w rows B : ℕ) (positive : v.Positive) (width : v.width = 64*(w+1))
    (split : v.rows = 142080*rows) (shape : v.beforeH = B*prime^(64*((w+1)*64)))
    (word : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    (u : HS T Q prime U) (S : Stacks T prime) :
    let directory := role v 142080
    let parents := v.beforeRows*rows*B
    let box := (prime^(w+1))^(64*64)
    let L := (w+1)*(64*64)
    let W := (S.R (r 1)).length
    (S.R (r 9)).length = parents →
    (S.R atom).length = w+1 → (S.R one).length = 1 →
    (∀ i ∈ ([2,3,4,5,6,7,10,11,12,13] : List (Fin 15)), S.R (r i) = []) →
    S.R (r 0) = (List.range parents).flatMap word ++ tail → (∀ i < parents, (word i).length = W) →
    W ≤ prime^v.width →
    let entries := (List.range (LabelMask.records directory)).flatMap (LabelDirectory.entry (fun j => word (j/box)) 64 (w+1))
    let R := Function.update (LabelDirectorySetup.prepared S.R r L) (r 12) (expandedMask box (fun _ => false) (S.R (r 9)))
    ∃ z n, z.user = u.user ∧ prime^v.width*n*142080 ≤ (16*64*64+19*64+344)*volume prime v ∧
      Exec body ((LabelDirectorySetup.setup 64 r atom one).seq
        ((expandMask (r 9) (r 4) (r 2) (r 3) (r 5) (r 12) (fun _ => false)).seq (LabelDirectoryBuild.program r)))
        (mk u S) n (mk z {S with R := Function.update (Function.update R (r 0) tail) (r 14) (entries ++ S.R (r 14))}) := by
  intro directory parents box L W parentCount atomWidth unit fresh source widths prefixFits entries R
  have roleRows : directory.rows = rows := by simp [directory,role,split]
  have count : LabelMask.records directory = parents*box := by
    rw [LabelMask.records,roleRows]
    change v.beforeRows*rows*v.beforeH = _
    rw [shape]; dsimp only [parents,box]; rw [← pow_mul]; ring_nf
  have dp := RecursiveRowsNodeLayout.role_positive 142080 v (by decide) positive ⟨rows,split⟩
  have run := LabelDirectorySetup.build_from_parents (body := body) 64 r atom one atomOff oneOff u S word tail unit fresh
  simp only [atomWidth,parentCount,pow_mul prime (w+1) (64*64)] at run
  obtain ⟨z,n,user,time,exec⟩ := run (Nat.mul_pos (Nat.succ_pos _) (by decide)) source widths
  have pos : 0 < parents := by
    have h := positive.2.2.1
    rw [shape] at h
    exact Nat.mul_pos (Nat.mul_pos positive.1 (roleRows ▸ dp.2.1)) (Nat.pos_of_mul_pos_right h)
  have recordsPos : 0 < LabelMask.records directory := Nat.mul_pos (Nat.mul_pos dp.1 dp.2.1) dp.2.2.1
  have boxPos := Nat.pos_of_mul_pos_left (count ▸ recordsPos)
  have fixed := fixedBoxCost_le 64 w (by decide)
  have paid := time.trans (buildCost_le (w+1) W parents box _ count (by change 22*box+21*(w+1)+26*prime^w+82 ≤ 151*box at fixed; omega))
  have bound := directorySetupCost_le_volume directory dp 64 (w+1) W parents 0 box
    (show 64*(w+1) ≤ v.width by omega) (count ▸ Nat.le_mul_of_pos_right _ boxPos) (Nat.zero_le _)
    (count ▸ Nat.le_mul_of_pos_left _ pos) prefixFits
  have size : volume prime directory * 142080 = volume prime v := by
    unfold volume; rw [roleRows]
    rw [split]; dsimp only [directory,role]; ring
  refine ⟨z,n,user,?_,?_⟩
  · rw [← size,← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left _ paid).trans bound)
  · simpa only [entries,R,count,box,L] using exec

private theorem parentCountCharge (v : Descriptor) (positive : v.Positive) (w t : ℕ)
    (width : v.width = 64*(w+1)) (time : t ≤ 44*LabelMask.records v+13*(w+1)+14) :
    prime^v.width*t ≤ 71*volume prime v := by
  let records := LabelMask.records v
  let scale := prime^v.width
  have hr : 0 < records := Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) positive.2.2.1
  have hs : 0 < scale := Nat.pow_pos Networks.Shared50ModularControl.prime_prime.pos
  have hw : w+1 ≤ scale := (show w+1 ≤ v.width by omega).trans
    (Nat.lt_pow_self (n := v.width) Networks.Shared50ModularControl.prime_prime.one_lt).le
  have budget : t ≤ 71*(records*scale) := by
    have a := Nat.le_mul_of_pos_right records hs
    have b := Nat.le_mul_of_pos_left scale hr
    change t ≤ 44*records+13*(w+1)+14 at time
    omega
  have occupied : records*scale*scale ≤ volume prime v := by
    change records*scale*scale ≤ records*scale*v.between*scale*v.afterD
    calc
      _ = records*scale*1*scale*1 := by ring
      _ ≤ _ := by gcongr <;> first | exact positive.2.2.2.1 | exact positive.2.2.2.2
  calc
    _ ≤ scale*(71*(records*scale)) := Nat.mul_le_mul_left _ budget
    _ = 71*(records*scale*scale) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ occupied

/-- Register 46 receives the archive and register 47 retains its prefix width.
The other builder registers use the directory's private bank. -/
def remainderDirectoryPorts : Fin 15 ↪ Fin 72 :=
  ⟨![58,47,59,60,61,62,63,64,65,66,67,68,69,70,46], by decide⟩

/-- The builder writes the entries in scan order. Its tape time is charged to the
parent volume using the actual role split and inherited prefix width. -/
theorem remainderDirectory_build {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 72 ↪ Fin T)
    (v : Descriptor) (w rows B : ℕ) (positive : v.Positive) (width : v.width = 64*(w+1))
    (split : v.rows = 142080*rows) (shape : v.beforeH = B*prime^(64*((w+1)*64)))
    (word : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    (u : HS T Q prime U) (raw : Stacks T prime) :
    let r := remainderDirectoryPorts.trans bank
    let atom := bank 71
    let one := bank 28
    let br := bank 29
    let nr := bank 30
    let bh := bank 31
    let directory := role v 142080
    let parents := v.beforeRows*rows*B
    let box := (prime^(w+1))^(64*64)
    let L := (w+1)*(64*64)
    let W := (raw.R (r 1)).length
    let S := {raw with R := Function.update raw.R (r 9) (List.replicate parents tick)}
    (raw.R br).length = v.beforeRows → (raw.R nr).length = rows → (raw.R bh).length = v.beforeH →
    (raw.R atom).length = w+1 → (raw.R one).length = 1 →
    (∀ i ∈ ([2,3,4,5,6,7,9,10,11,12,13] : List (Fin 15)), raw.R (r i) = []) →
    raw.R (r 0) = (List.range parents).flatMap word ++ tail → (∀ i < parents, (word i).length = W) →
    W ≤ prime^v.width →
    let entries := (List.range (LabelMask.records directory)).flatMap (LabelDirectory.entry (fun j => word (j/box)) 64 (w+1))
    let R := Function.update (LabelDirectorySetup.prepared S.R r L) (r 12) (expandedMask box (fun _ => false) (S.R (r 9)))
    ∃ z elapsed, z.user = u.user ∧ prime^v.width*elapsed*142080 ≤ (71+16*64*64+19*64+344)*volume prime v ∧
      Exec body ((LabelSpectators.program 64 br nr bh atom (r 2) (r 9) (r 3) (r 5)).seq ((LabelDirectorySetup.setup 64 r atom one).seq
        ((expandMask (r 9) (r 4) (r 2) (r 3) (r 5) (r 12) (fun _ => false)).seq (LabelDirectoryBuild.program r))))
        (mk u raw) elapsed (mk z {S with R := Function.update (Function.update R (r 0) tail) (r 14) (entries ++ S.R (r 14))}) := by
  intro r atom one br nr bh directory parents box L W S beforeRows rowCount beforeH atomWidth unit fresh source widths prefixFits entries R
  have atomOff (i : Fin 15) : atom ≠ r i :=
    bank.injective.ne ((by decide : ∀ i, (71 : Fin 72) ≠ remainderDirectoryPorts i) i)
  have oneOff (i : Fin 15) : one ≠ r i :=
    bank.injective.ne ((by decide : ∀ i, (28 : Fin 72) ≠ remainderDirectoryPorts i) i)
  have ports : [br,nr,bh,atom,r 2,r 9,r 3,r 5].Nodup :=
    List.Nodup.map bank.injective (by decide : ([29,30,31,71,59,66,60,62] : List (Fin 72)).Nodup)
  have roleRows : directory.rows = rows := by simp [directory,role,split]
  have dp := RecursiveRowsNodeLayout.role_positive 142080 v (by decide) positive ⟨rows,split⟩
  obtain ⟨y,t,yu,account,countRun⟩ := LabelSpectators.runs body 64 (by decide) br nr bh atom (r 2) (r 9) (r 3) (r 5)
    ports directory dp (w+1) B shape u raw beforeRows (roleRows ▸ rowCount) beforeH atomWidth (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> apply fresh <;> decide)
  have init : Exec body (LabelSpectators.program 64 br nr bh atom (r 2) (r 9) (r 3) (r 5)) (mk u raw) t (mk y S) := by
    rw [roleRows] at countRun
    exact countRun
  have keep (i : Fin 15) (hi : i ≠ 9) : S.R (r i) = raw.R (r i) :=
    Function.update_of_ne (r.injective.ne hi) _ _
  have build := buildCounted body r atom one atomOff oneOff v w rows B positive width split shape word tail y S
    (by simp [S,parents]) (by simpa [S,atomOff] using atomWidth) (by simpa [S,oneOff] using unit) (by
      intro i hi
      have ne : i ≠ 9 := by rintro rfl; exact (by decide : (9 : Fin 15) ∉ [2,3,4,5,6,7,10,11,12,13]) hi
      rw [keep i ne]
      exact fresh i ((by decide : ([2,3,4,5,6,7,10,11,12,13] : List (Fin 15)) ⊆ [2,3,4,5,6,7,9,10,11,12,13]) hi))
  obtain ⟨z,n,user,paid,exec⟩ := build ((keep 0 (by decide)).trans source)
    (fun i hi => (widths i hi).trans (congrArg List.length (keep 1 (by decide))).symm)
    ((congrArg List.length (keep 1 (by decide))).le.trans prefixFits)
  have size : volume prime directory * 142080 = volume prime v := by
    unfold volume; rw [roleRows,split]; dsimp only [directory,role]; ring
  have countPaid := Nat.mul_le_mul_right 142080 (parentCountCharge directory dp w t width account)
  change prime^v.width*t*142080 ≤ 71*volume prime directory*142080 at countPaid
  rw [Nat.mul_assoc 71,size] at countPaid
  refine ⟨z,t+n,user.trans yu,?_,Exec.seq init exec⟩
  calc
    _ = prime^v.width*t*142080 + prime^v.width*n*142080 := by ring
    _ ≤ _ := (Nat.add_le_add countPaid paid).trans_eq (by ring)

end IntegerMultBounds.MathlibTM2.M6.BitNode
