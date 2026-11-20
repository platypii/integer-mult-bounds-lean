module

public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate
public import IntegerMultBounds.MathlibTM2.Cover.FallbackIdentitySeed
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGeneratedSignedPass

/-! Build the PR589 remainder directory from the inherited parent entries. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.MathlibTM2.Cover Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout Node

/-- Reuse the seven internal counting tapes and place the unary result in owner register two. -/
def ownerCountPorts (K : ℕ) : Fin 10 ↪ Fin ((66+K)+5) :=
  let slots : Fin 10 ↪ Fin (66+5) := ⟨![2,53,59,60,61,62,63,64,65,68],by decide⟩
  slots.trans (appendPrivate (Fin.castAddEmb K) 5)

theorem ownerCount_exec {K Q : ℕ} {P U : Type} (body : P → Pr P ((66+K)+5) Q prime U)
    (fields H J M W : ℕ) (hm : M < 2^H) (hw : W < 2^J) (u : HS ((66+K)+5) Q prime U)
    (S : Stacks ((66+K)+5) prime) {N : ℕ} (volumeEq : M^fields*W = N) :
    let caller := fun i : Fin 66 => (i.castAdd K).castAdd 5
    let dst := (2 : Fin 5).natAdd (66+K)
    S.R (caller 2) = binSyms H M → S.R (caller 53) = binSyms J W →
    (∀ i : Fin 66, 59 ≤ i.val → S.R (caller i) = []) → S.R dst = [] →
    ∃ z D n, z.user = u.user ∧ n ≤ dimensionTime H J fields+6*N+13*(fields*H+J)+8 ∧
      Exec body (payloadCountProgram (ownerCountPorts K) fields) (mk u S) n (mk z D) ∧
      embStk (fun i : Fin (66+K) => i.castAdd 5) D = embStk (fun i : Fin (66+K) => i.castAdd 5) S ∧
      (D.R dst).length = N ∧ ∀ i : Fin 5, i ≠ 2 → D.R (i.natAdd (66+K)) = S.R (i.natAdd (66+K)) := by
  intro caller dst base width scratch empty
  let slots : Fin 9 → Fin 66 := ![2,53,59,60,61,62,63,64,65]
  have shared (i : Fin 9) : ownerCountPorts K i.castSucc = caller (slots i) := by
    refine Eq.trans ?_ (appendPrivate_shared (Fin.castAddEmb K) (slots i))
    apply congrArg (appendPrivate (Fin.castAddEmb K) 5)
    exact (by decide : ∀ j : Fin 9, (![2,53,59,60,61,62,63,64,65,68] : Fin 10 → Fin 71) j.castSucc =
      (slots j).castAdd 5) i
  have last : ownerCountPorts K 9 = dst := appendPrivate_work (Fin.castAddEmb K) 2
  have run := payloadCount_exec body (ownerCountPorts K) fields H J M W hm hw u S
    ((congrArg S.R (shared 0)).trans base) ((congrArg S.R (shared 1)).trans width) (by
      intro i hi
      by_cases stop : i = 9
      · simpa only [stop,last] using empty
      · have lt : i.val < 9 := by have := i.isLt; have ne : i.val ≠ 9 := fun eq => stop (Fin.ext eq); omega
        let j : Fin 9 := ⟨i.val,lt⟩
        change S.R (ownerCountPorts K j.castSucc) = []
        rw [shared]
        exact scratch _ ((by decide : ∀ k : Fin 9, 2 ≤ k.val → 59 ≤ (slots k).val) j hi))
  rw [last,volumeEq] at run
  obtain ⟨z,n,user,time,exec⟩ := run
  refine ⟨z,_,n,user,time,exec,embStk_updateR_off S _ _ ?_,?_,?_⟩
  · intro i eq
    have bad := congrArg Fin.val eq
    change i.val = (66+K)+2 at bad
    have := i.isLt
    omega
  · simp
  · intro i hi
    exact Function.update_of_ne ((Fin.natAdd_injective ..).ne hi) ..

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

private theorem remainderDirectoryCount (v : Descriptor) (w rows B : ℕ)
    (split : v.rows = 142080*rows) (shape : v.beforeH = B*prime^(64*((w+1)*64))) :
    LabelMask.records (role v 142080) = (v.beforeRows*rows*B)*(prime^(w+1))^(64*64) := by
  simp only [LabelMask.records,role,split,Nat.mul_div_cancel_left _ (by decide : 0 < 142080),shape,← pow_mul]
  ring

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
  have count : LabelMask.records directory = parents*box := remainderDirectoryCount v w rows B split shape
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

private theorem countAndCleanupCharge (v : Descriptor) (positive : v.Positive) (w t parents box : ℕ) (count : LabelMask.records v = parents*box)
    (width : v.width = 64*(w+1)) (time : t ≤ 44*LabelMask.records v+13*(w+1)+14) :
    prime^v.width*(t+2*(box+parents+2*((w+1)*(64*64))+parents*box+(w+1))+29) ≤ 364*volume prime v := by
  let records := LabelMask.records v
  let scale := prime^v.width
  have hr : 0 < records := Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) positive.2.2.1
  have hs : 0 < scale := Nat.pow_pos Networks.Shared50ModularControl.prime_prime.pos
  have hw : w+1 ≤ scale := (show w+1 ≤ v.width by omega).trans
    (Nat.lt_pow_self (n := v.width) Networks.Shared50ModularControl.prime_prime.one_lt).le
  have budget : t+2*(box+parents+2*((w+1)*(64*64))+parents*box+(w+1))+29 ≤ 364*(records*scale) := by
    have a := Nat.le_mul_of_pos_right records hs
    have b := Nat.le_mul_of_pos_left scale hr
    have both : 0 < parents*box := count ▸ hr
    have p := Nat.le_mul_of_pos_right parents (Nat.pos_of_mul_pos_left both)
    have q := Nat.le_mul_of_pos_left box (Nat.pos_of_mul_pos_right both)
    have radix := (Nat.lt_pow_self (n := v.width) Networks.Shared50ModularControl.prime_prime.one_lt).le
    change records = parents*box at count
    change v.width ≤ scale at radix
    change t ≤ 44*records+13*(w+1)+14 at time
    omega
  have occupied : records*scale*scale ≤ volume prime v := by
    change records*scale*scale ≤ records*scale*v.between*scale*v.afterD
    calc
      _ = records*scale*1*scale*1 := by ring
      _ ≤ _ := by gcongr <;> first | exact positive.2.2.2.1 | exact positive.2.2.2.2
  calc
    _ ≤ scale*(364*(records*scale)) := Nat.mul_le_mul_left _ budget
    _ = 364*(records*scale*scale) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ occupied

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

/-- Dimension words, descriptor headers and inherited weights consumed by the row programs. -/
def DirectoryDimensions {m : ℕ} (v : Descriptor) (w W H J : ℕ)
    (parent : Fin m → ZMod (prime^(w+1))) (R : Fin 58 → List (Fin (prime+4))) : Prop :=
  let M := prime^(w+1)
  R 2 = binSyms H M ∧ R 28 = binSyms 1 1 ∧ R 53 = binSyms J W ∧
    (∀ i : Fin 6, R ((i.natAdd 33).castLE (by decide : 39 ≤ 58)) = (M8.RevMachine.Routines.hdr v i).map bitSymbol) ∧
    R 44 = binSyms H (1 : ZMod M).val ∧ (R 45).length = w ∧ R 55 = (List.ofFn fun i => binSyms H (parent i).val).flatten

open IntegerMultBounds.Swap.Modular in
/-- Shared inputs read by the row scan, all on registers preserved by the directory builder. -/
def DirectoryHeaders {m : ℕ} (v : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ) (w W H J : ℕ)
    (parent : Fin m → ZMod (prime^(w+1))) (R : Fin 58 → List (Fin (prime+4))) : Prop :=
  let M := prime^(w+1)
  R 49 = [] ∧ (∃ suffix, R 48 = matrixWords prime H (reduce M proj) ++ suffix) ∧
    DirectoryDimensions v w W H J parent R

structure DirectoryScanInput {m : ℕ} (v : Descriptor) (proj : Matrix (Fin m) (Fin m) ℚ) (w W H J : ℕ)
    (parent : Fin m → ZMod (prime^(w+1))) (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    (labels : List ℕ) (R : Fin 58 → List (Fin (prime+4))) : Prop where
  archive : R 46 = labels.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ tail
  widths : ∀ j ∈ labels, (R 47).length = (prefixes j).length
  headers : DirectoryHeaders v proj w W H J parent R

theorem DirectoryHeaders.of_frame {m w W H J : ℕ} {v : Descriptor} {proj : Matrix (Fin m) (Fin m) ℚ}
    {parent : Fin m → ZMod (prime^(w+1))} {R S : Fin 58 → List (Fin (prime+4))}
    (headers : DirectoryHeaders v proj w W H J parent R) (frame : ∀ i, i.val ≠ 46 → S i = R i) :
    DirectoryHeaders v proj w W H J parent S := by
  unfold DirectoryHeaders DirectoryDimensions at headers ⊢
  have hdr (i : Fin 6) : S ((i.natAdd 33).castLE (by decide)) = R ((i.natAdd 33).castLE (by decide)) :=
    frame _ (by change 33+i.val ≠ 46; omega)
  simpa only [hdr,frame 49 (by decide),frame 48 (by decide),frame 2 (by decide),frame 28 (by decide),
    frame 53 (by decide),frame 44 (by decide),frame 45 (by decide),frame 55 (by decide)] using headers

/-- Register 46 receives the archive and register 47 retains its prefix width.
The other builder registers use the directory's private bank. -/
def remainderDirectoryPorts : Fin 15 ↪ Fin 72 :=
  ⟨![58,47,59,60,61,62,63,64,65,66,67,68,69,70,46], by decide⟩

/-- Clear the inherited source and the six transient counters, preserving the archive. -/
private theorem finishDirectory {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 15 ↪ Fin T) (atom : Fin T) (apart : ∀ i, atom ≠ r i)
    (parents L box : ℕ) (tail entries : List (Fin (prime+4))) (u : HS T Q prime U) (raw : Stacks T prime) :
    let scratch := ([0,4,9,10,11,12] : List (Fin 15)).map r ++ [atom]
    let S := {raw with R := Function.update raw.R (r 9) (List.replicate parents tick)}
    let R := Function.update (LabelDirectorySetup.prepared S.R r L) (r 12) (expandedMask box (fun _ => false) (S.R (r 9)))
    let D := {S with R := Function.update (Function.update R (r 0) tail) (r 14) (entries ++ S.R (r 14))}
    ∃ z, z.user = u.user ∧ Exec body (clearWorkTapes scratch) (mk u D)
      ((scratch.map (fun i => 4*(raw.L i).length)).sum +
        2*(tail.length+prime^L+parents+2*L+parents*box+(raw.R atom).length)+29)
      (mk z {raw with L := fun i => if i ∈ scratch then [] else raw.L i,
                      R := fun i => if i ∈ scratch then [] else Function.update raw.R (r 14) (entries ++ raw.R (r 14)) i}) := by
  intro scratch S R D
  have nodup : scratch.Nodup := by
    simp only [scratch,List.nodup_append,List.nodup_cons,List.nodup_nil,List.not_mem_nil,not_false_eq_true,and_true]
    exact ⟨List.Nodup.map r.injective (by decide),by simp [ne_comm,apart]⟩
  obtain ⟨z,user,run⟩ := clearWorkTapes_exec body scratch nodup u D
  refine ⟨z,user,run.cast ?_ ?_⟩
  · simp [scratch,D,R,S,LabelDirectorySetup.prepared,RadixCounterData.zeros,expandedMask_length,apart]
    ring
  · congr 2
    funext i
    by_cases h : i ∈ scratch
    · simp [h]
    · have ne (j : Fin 15) (hj : j ∈ ([0,4,9,10,11,12] : List (Fin 15))) : i ≠ r j :=
        fun eq => h (eq ▸ List.mem_append_left _ (List.mem_map_of_mem hj))
      simp only [h,ite_false,D,R,S,LabelDirectorySetup.prepared]
      by_cases out : i = r 14
      · subst i; simp
      · simp [Function.update_of_ne out,Function.update_of_ne (ne 0 (by decide)),
          Function.update_of_ne (ne 4 (by decide)),Function.update_of_ne (ne 9 (by decide)),
          Function.update_of_ne (ne 10 (by decide)),Function.update_of_ne (ne 11 (by decide)),
          Function.update_of_ne (ne 12 (by decide))]

/-- Count the spectator labels, generate their directory and reclaim the construction tapes. -/
noncomputable def remainderDirectoryProgram {T Q : ℕ} {P U : Type} (bank : Fin 72 ↪ Fin T) : Pr P T Q prime U :=
  let r := remainderDirectoryPorts.trans bank
  let scratch := ([0,4,9,10,11,12] : List (Fin 15)).map r ++ [bank 71]
  ((LabelSpectators.program 64 (bank 29) (bank 30) (bank 31) (bank 71) (r 2) (r 9) (r 3) (r 5)).seq
    ((LabelDirectorySetup.setup 64 r (bank 71) (bank 28)).seq
      ((expandMask (r 9) (r 4) (r 2) (r 3) (r 5) (r 12) (fun _ => false)).seq
        (LabelDirectoryBuild.program r)))).seq (clearWorkTapes scratch)

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
    let W := (raw.R (r 1)).length
    (raw.R br).length = v.beforeRows → (raw.R nr).length = rows → (raw.R bh).length = v.beforeH →
    (raw.R atom).length = w+1 → (raw.R one).length = 1 →
    (∀ i ∈ ([2,3,4,5,6,7,9,10,11,12,13] : List (Fin 15)), raw.R (r i) = []) →
    raw.R (r 0) = (List.range parents).flatMap word ++ tail → (∀ i < parents, (word i).length = W) →
    W ≤ prime^v.width →
    let entries := (List.range (LabelMask.records directory)).flatMap (LabelDirectory.entry (fun j => word (j/box)) 64 (w+1))
    let scratch := ([0,4,9,10,11,12] : List (Fin 15)).map r ++ [atom]
    let inherited := (scratch.map (fun i => 4*(raw.L i).length)).sum + 2*tail.length
    let final := {raw with
          L := fun i => if i ∈ scratch then [] else raw.L i
          R := fun i => if i ∈ scratch then [] else Function.update raw.R (r 14) (entries ++ raw.R (r 14)) i}
    ∃ z elapsed, z.user = u.user ∧ prime^v.width*elapsed*142080 ≤ (364+16*64*64+19*64+344)*volume prime v + prime^v.width*inherited*142080 ∧
      Exec body (remainderDirectoryProgram bank) (mk u raw) elapsed (mk z final) ∧
      (∀ (child : Descriptor) (proj : Matrix (Fin 64) (Fin 64) ℚ) (rowVolume H J : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))),
        DirectoryHeaders child proj w rowVolume H J parent (fun i => raw.R (bank (i.castLE (by decide)))) →
        DirectoryScanInput child proj w rowVolume H J parent (fun j => word (j/box)) (raw.R (bank 46))
          (List.range (LabelMask.records directory)) (fun i => final.R (bank (i.castLE (by decide))))) ∧
      (∀ i : Fin 58, i.val ≠ 46 → final.R (bank (i.castLE (by decide))) = raw.R (bank (i.castLE (by decide)))) ∧
      (∀ i : Fin 58, final.L (bank (i.castLE (by decide))) = raw.L (bank (i.castLE (by decide)))) ∧
      (∀ k, (final.L k).length ≤ (raw.L k).length) ∧
      (raw.R (bank 65) = [] → ∀ i : Fin 72, 58 ≤ i.val → final.R (bank i) = []) ∧
      (∀ k, (∀ i, bank i ≠ k) → final.R k = raw.R k ∧ final.L k = raw.L k) := by
  intro r atom one br nr bh directory parents box W beforeRows rowCount beforeH atomWidth unit fresh source widths prefixFits entries scratch inherited final
  let L := (w+1)*(64*64)
  let S := {raw with R := Function.update raw.R (r 9) (List.replicate parents tick)}
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
  have count := remainderDirectoryCount v w rows B split shape
  let spent := t+2*(box+parents+2*L+parents*box+(w+1))+29
  have small := countAndCleanupCharge directory dp w t parents box count width account
  have countPaid : prime^v.width*spent*142080 ≤ 364*volume prime v := by
    rw [← size,← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ small
  obtain ⟨out,same,clean⟩ := finishDirectory body r atom atomOff parents L box tail entries z raw
  have outside (i : Fin 72) (small : i.val < 58) : bank i ∉ scratch := by
    have low : ∀ j ∈ ([0,4,9,10,11,12] : List (Fin 15)), 58 ≤ (remainderDirectoryPorts j).val := by decide
    intro h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨j,hj,eq⟩ := List.mem_map.mp h
      have same := bank.injective (show bank (remainderDirectoryPorts j) = bank i from eq)
      exact (Nat.not_le_of_gt small) (same ▸ low j hj)
    · have eq := bank.injective (List.mem_singleton.mp h)
      have := congrArg Fin.val eq
      change i.val = 71 at this
      omega
  have frame (i : Fin 72) (small : i.val < 58) (ne : i.val ≠ 46) : final.R (bank i) = raw.R (bank i) := by
    have off : bank i ≠ r 14 := bank.injective.ne (fun h => ne (congrArg Fin.val h))
    simp only [final,ite_eq_right (outside i small),Function.update_of_ne off]
  have cleared (unused : raw.R (bank 65) = []) (i : Fin 72) (hi : 58 ≤ i.val) :
      final.R (bank i) = [] := by
    by_cases cleared : bank i ∈ scratch
    · simp [final,cleared]
    have ne : bank i ≠ r 14 := bank.injective.ne (fun eq => by
      have h := congrArg Fin.val eq
      change i.val = 46 at h
      omega)
    simp only [final,ite_eq_right cleared,Function.update_of_ne ne]
    have ports : ∀ i : Fin 72, 58 ≤ i.val → i = 58 ∨ i = 71 ∨ i = 65 ∨
        ∃ j ∈ ([2,3,4,5,6,7,9,10,11,12,13] : List (Fin 15)), remainderDirectoryPorts j = i := by decide
    rcases ports i hi with rfl | rfl | rfl | ⟨j,hj,rfl⟩
    · exact False.elim (cleared (List.mem_append_left _ (List.mem_map_of_mem (f := r) (by decide : (0 : Fin 15) ∈ [0,4,9,10,11,12]))))
    · exact False.elim (cleared (List.mem_append_right _ (List.mem_singleton_self atom)))
    · exact unused
    · exact fresh j hj
  have lowLeft (i : Fin 58) : final.L (bank (i.castLE (by decide))) = raw.L (bank (i.castLE (by decide))) := by
    exact ite_eq_right (outside _ i.isLt)
  have leftSize (k : Fin T) : (final.L k).length ≤ (raw.L k).length := by
    change (if k ∈ scratch then [] else raw.L k).length ≤ _
    split <;> simp
  have external (k : Fin T) (off : ∀ i, bank i ≠ k) : final.R k = raw.R k ∧ final.L k = raw.L k := by
    have fresh : k ∉ scratch := by
      intro h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨j,_,eq⟩ := List.mem_map.mp h
        exact off _ eq
      · exact off 71 (List.mem_singleton.mp h).symm
    have ne : k ≠ r 14 := (off _).symm
    simp [final,fresh,ne]
  have archive : final.R (bank 46) = entries ++ raw.R (bank 46) := by
    change (if bank 46 ∈ scratch then [] else Function.update raw.R (bank 46) (entries ++ raw.R (bank 46)) (bank 46)) = _
    rw [ite_eq_right (outside 46 (by decide)),Function.update_self]
  have prefixWidth (j : ℕ) (hj : j ∈ List.range (LabelMask.records directory)) :
      (final.R (bank 47)).length = (word (j/box)).length := by
    have inside := List.mem_range.mp hj
    rw [count] at inside
    have positiveBox := Nat.pos_of_mul_pos_left (Nat.zero_lt_of_lt inside)
    rw [frame 47 (by decide) (by decide)]
    exact (widths _ ((Nat.div_lt_iff_lt_mul positiveBox).mpr inside)).symm
  refine ⟨out,_,same.trans (user.trans yu),?_,Exec.seq (Exec.seq init exec) clean,fun _ _ _ _ _ _ headers => ⟨archive,prefixWidth,headers.of_frame (fun i ne => frame _ i.isLt ne)⟩,fun i ne => frame _ (show i.val < 58 from i.isLt) ne,lowLeft,leftSize,cleared,external⟩
  have power : prime^L = box := pow_mul _ _ _
  rw [power,atomWidth]
  change prime^v.width*(t+n+(_+2*(tail.length+box+parents+2*L+parents*box+(w+1))+29))*142080 ≤ _
  calc
    _ = prime^v.width*spent*142080 + prime^v.width*n*142080 + prime^v.width*inherited*142080 := by
      dsimp only [spent,inherited]; ring
    _ ≤ _ := (Nat.add_le_add_right (Nat.add_le_add countPaid paid) _).trans_eq (by ring)

def intervalSeed (lo hi : ℕ) (i j : Fin 64) : Bool :=
  decide (i = j ∧ lo ≤ i.val ∧ i.val < hi)

open IntegerMultBounds.Swap.Modular in
theorem reduce_intervalSeed (M lo hi : ℕ) :
    reduce M (Matrix.diagonal fun i : Fin 64 => if lo ≤ i.val ∧ i.val < hi then 1 else 0) =
      fun i j => if intervalSeed lo hi i j then (1 : ZMod M) else 0 := by
  ext i j
  by_cases eq : i = j
  · subst j
    by_cases active : lo ≤ i.val ∧ i.val < hi <;> simp [reduce,intervalSeed,active,ratMod_one,ratMod_zero]
  · simp [reduce,intervalSeed,eq,ratMod_zero]

def projectorSeedPorts : Fin 5 ↪ Fin 72 := ⟨![49,44,48,59,60],by decide⟩

def projectorSeedTime (H : ℕ) := 4*H+4 + (64*(64*(6*H+6)+1)+1 + (2*H+2))

private theorem projectorSeed_charge (v : Descriptor) (positive : v.Positive) (w rows : ℕ)
    (width : v.width = 64*(w+1)) (split : v.rows = 142080*rows) :
    prime^v.width*projectorSeedTime (prime^(w+1)).size*142080 ≤ volume prime v := by
  let M := prime^(w+1)
  have two : 2 ≤ M := by
    change 2 ≤ prime^(w+1)
    rw [pow_succ]
    exact (show 2 ≤ prime from Networks.Shared50ModularControl.prime_prime.one_lt).trans
      (Nat.le_mul_of_pos_left _ (pow_pos Networks.Shared50ModularControl.prime_prime.pos _))
  have digits : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have time : projectorSeedTime M.size ≤ prime^v.width := by
    rw [width,Nat.mul_comm 64,pow_mul]
    change _ ≤ M^64
    calc
      _ ≤ 65536*M := by unfold projectorSeedTime; omega
      _ ≤ M^16*M := Nat.mul_le_mul_right _ (show 2^16 ≤ M^16 from Nat.pow_le_pow_left two _)
      _ = M^17 := (pow_succ M 16).symm
      _ ≤ M^64 := Nat.pow_le_pow_right (by omega) (by decide)
  have rowsFit : 142080 ≤ v.rows := by
    have pos := positive.2.1
    rw [split] at pos ⊢
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left pos)
  calc
    _ = 1*142080*1*prime^v.width*1*projectorSeedTime M.size*1 := by ring
    _ ≤ volume prime v := by
      unfold volume
      gcongr <;> first | exact positive.1 | exact rowsFit | exact positive.2.2.1 | exact positive.2.2.2.1 | exact time | exact positive.2.2.2.2

private theorem prependTime_le (scale copies n t volume rate inherited : ℕ)
    (setup : scale*n*copies ≤ volume) (run : scale*t*copies ≤ rate*volume+scale*inherited*copies) :
    scale*(n+t)*copies ≤ (1+rate)*volume+scale*inherited*copies := by
  rw [Nat.mul_add,Nat.add_mul,Nat.add_mul,one_mul]
  omega

open IntegerMultBounds.Swap.Modular in
/-- Prepare the scanner's shared bank from inherited labels while keeping all five
owner registers available for the packed role and the subsequent row counter. -/
theorem remainderDirectory_prepareOwner {K Q : ℕ} {P U : Type} (room : 72 ≤ K)
    (body : P → Pr P (K+5) Q prime U) (layout child : Descriptor) (w rows B W H J : ℕ)
    (positive : layout.Positive) (width : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
    (shape : layout.beforeH = B*prime^(64*((w+1)*64))) (lo hi : ℕ) (precision : H = (prime^(w+1)).size)
    (parent : Fin 64 → ZMod (prime^(w+1))) (word : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    (u : HS (K+5) Q prime U) (raw : Stacks (K+5) prime) :
    let proj := Matrix.diagonal fun i : Fin 64 => if lo ≤ i.val ∧ i.val < hi then (1 : ℚ) else 0
    let matrix := matrixWords prime H (reduce (prime^(w+1)) proj)
    let bank := (Fin.castLEEmb room).trans (Fin.castAddEmb 5)
    let r := remainderDirectoryPorts.trans bank
    let parents := layout.beforeRows*rows*B
    let box := (prime^(w+1))^(64*64)
    let directory := role layout 142080
    let scratch := ([0,4,9,10,11,12] : List (Fin 15)).map r ++ [bank 71]
    let inherited := (scratch.map (fun i => 4*(raw.L i).length)).sum + 2*tail.length
    (raw.R (bank 29)).length = layout.beforeRows → (raw.R (bank 30)).length = rows →
    (raw.R (bank 31)).length = layout.beforeH → (raw.R (bank 71)).length = w+1 →
    (∀ i : Fin K, 59 ≤ i.val → i.val ≠ 71 → raw.R (i.castAdd 5) = []) →
    raw.R (bank 58) = (List.range parents).flatMap word ++ tail →
    (∀ i < parents, (word i).length = (raw.R (bank 47)).length) →
    (raw.R (bank 47)).length ≤ prime^layout.width →
    raw.R (bank 49) = [] → DirectoryDimensions child w W H J parent (fun i => raw.R (bank (i.castLE (by decide)))) →
    ∃ z D elapsed, z.user = u.user ∧
      prime^layout.width*elapsed*142080 ≤ (365+16*64*64+19*64+344)*volume prime layout + prime^layout.width*inherited*142080 ∧
      Exec body ((writeBinaryMatrix (intervalSeed lo hi) (projectorSeedPorts.trans bank)).seq (remainderDirectoryProgram bank)) (mk u raw) elapsed (mk z D) ∧
      DirectoryScanInput child proj w W H J parent (fun j => word (j/box)) (raw.R (bank 46))
        (List.range (LabelMask.records directory)) (fun i => D.R (bank (i.castLE (by decide)))) ∧
      (∀ i : Fin K, 58 ≤ i.val → D.R (i.castAdd 5) = []) ∧
      D.R (bank 48) = matrix ++ raw.R (bank 48) ∧
      (∀ i : Fin 58, i.val ≠ 46 → i.val ≠ 48 → D.R (bank (i.castLE (by decide))) = raw.R (bank (i.castLE (by decide)))) ∧
      (∀ i : Fin 58, D.L (bank (i.castLE (by decide))) = raw.L (bank (i.castLE (by decide)))) ∧
      (∀ k, (D.L k).length ≤ (raw.L k).length) ∧
      (∀ i : Fin 5, D.R (i.natAdd K) = raw.R (i.natAdd K) ∧ D.L (i.natAdd K) = raw.L (i.natAdd K)) := by
  intro proj matrix bank r parents box directory scratch inherited br nr bh atom clean source widths fits spare dims
  have unit : (raw.R (bank 28)).length = 1 := by
    have one : raw.R (bank 28) = binSyms 1 1 := dims.2.1
    rw [one,length_binSyms]
  let ports := projectorSeedPorts.trans bank
  have one : raw.R (bank 44) = binSyms H (1 : ZMod (prime^(w+1))).val := dims.2.2.2.2.1
  obtain ⟨y,n,yu,time,seed⟩ := writeBinaryMatrix_writes (M := prime^(w+1)) body (intervalSeed lo hi) H ports u raw
    ⟨one,spare,clean ((59 : Fin 72).castLE room) (by decide : 59 ≤ 59) (by decide : (59 : ℕ) ≠ 71),
      clean ((60 : Fin 72).castLE room) (by decide : 59 ≤ 60) (by decide : (60 : ℕ) ≠ 71)⟩
  let S := {raw with R := Function.update raw.R (bank 48) (matrix ++ raw.R (bank 48))}
  have seedRun : Exec body (writeBinaryMatrix (intervalSeed lo hi) ports) (mk u raw) n (mk y S) := by
    simpa only [show ports 2 = bank 48 from rfl,S,matrix,proj,reduce_intervalSeed] using seed
  have stay (i : Fin 72) (hi : i.val ≠ 48) : S.R (bank i) = raw.R (bank i) :=
    Function.update_of_ne (bank.injective.ne (fun h => hi (congrArg Fin.val h))) ..
  have written : S.R (bank 48) = matrix ++ raw.R (bank 48) := Function.update_self (bank 48) _ raw.R
  have headers : DirectoryHeaders child proj w W H J parent (fun i => S.R (bank (i.castLE (by decide)))) := by
    refine ⟨(stay 49 (by decide)).trans spare,⟨raw.R (bank 48),written⟩,?_⟩
    obtain ⟨base,unit,trailing,desc,one,clock,weights⟩ := dims
    refine ⟨(stay 2 (by decide)).trans base,(stay 28 (by decide)).trans unit,(stay 53 (by decide)).trans trailing,?_,
      (stay 44 (by decide)).trans one,(congrArg List.length (stay 45 (by decide))).trans clock,(stay 55 (by decide)).trans weights⟩
    intro i
    exact (stay _ (by change 33+i.val ≠ 48; omega)).trans (desc i)
  have fresh (i : Fin 15) (hi : i ∈ ([2,3,4,5,6,7,9,10,11,12,13] : List (Fin 15))) : S.R (r i) = [] := by
    have bounds := (by decide : ∀ j ∈ ([2,3,4,5,6,7,9,10,11,12,13] : List (Fin 15)),
      59 ≤ (remainderDirectoryPorts j).val ∧ (remainderDirectoryPorts j).val ≠ 71) i hi
    exact (stay _ (by omega)).trans (clean ((remainderDirectoryPorts i).castLE room) bounds.1 bounds.2)
  obtain ⟨z,t,user,paid,run,input,right,left,size,cleared,off⟩ :=
    remainderDirectory_build body bank layout w rows B positive width split shape word tail y S
      ((congrArg List.length (stay 29 (by decide))).trans br) ((congrArg List.length (stay 30 (by decide))).trans nr)
      ((congrArg List.length (stay 31 (by decide))).trans bh) ((congrArg List.length (stay 71 (by decide))).trans atom)
      ((congrArg List.length (stay 28 (by decide))).trans unit) fresh ((stay 58 (by decide)).trans source)
      (fun i hi => (widths i hi).trans (congrArg List.length (stay 47 (by decide))).symm)
      ((congrArg List.length (stay 47 (by decide))).le.trans fits)
  have ready := input _ _ _ _ _ _ headers
  rw [stay 46 (by decide)] at ready
  refine ⟨z,_,n+t,user.trans yu,?_,Exec.seq seedRun run,ready,?_,(right 48 (by decide)).trans written,
    fun i ne off => (right i ne).trans (stay _ off),left,size,?_⟩
  · have bound : n ≤ projectorSeedTime (prime^(w+1)).size := precision ▸ time
    have charged := (Nat.mul_le_mul_right 142080 (Nat.mul_le_mul_left (prime^layout.width) bound)).trans
      (projectorSeed_charge layout positive w rows width split)
    exact prependTime_le _ _ _ _ _ _ _ charged paid
  · intro i high
    by_cases low : i.val < 72
    · exact cleared ((stay 65 (by decide)).trans (clean ((65 : Fin 72).castLE room) (by decide : 59 ≤ 65) (by decide : (65 : ℕ) ≠ 71))) ⟨i.val,low⟩ high
    · have outside (j : Fin 72) : bank j ≠ i.castAdd 5 := by
        intro eq
        have h := congrArg Fin.val eq
        change j.val = i.val at h
        omega
      exact (off _ outside).1.trans ((Function.update_of_ne (outside 48).symm ..).trans (clean i (by omega) (by omega)))
  · intro i
    have outside (j : Fin 72) : bank j ≠ i.natAdd K := by
      intro eq
      have h := congrArg Fin.val eq
      change j.val = K+i.val at h
      omega
    exact ⟨(off _ outside).1.trans (Function.update_of_ne (outside 48).symm ..),(off _ outside).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
