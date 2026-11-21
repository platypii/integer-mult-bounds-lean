module

public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate
public import IntegerMultBounds.MathlibTM2.M6.BitDirectoryRoleSplit
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderHeaders
public import IntegerMultBounds.MathlibTM2.Cover.FallbackIdentitySeed
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGeneratedSignedPass

/-! Build the PR589 remainder directory from the inherited parent entries. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.MathlibTM2.Cover Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout Node
open IntervalDescriptor

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
      (D.R dst).length = N ∧ D.L = S.L ∧ ∀ i : Fin 5, i ≠ 2 → D.R (i.natAdd (66+K)) = S.R (i.natAdd (66+K)) := by
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
  refine ⟨z,_,n,user,time,exec,embStk_updateR_off S _ _ ?_,?_,rfl,?_⟩
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

theorem remainderDirectoryCount (v : Descriptor) (w rows B : ℕ)
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
def DirectoryWords {m : ℕ} (fields : Fin 6 → List (Fin (prime+4))) (w W H J : ℕ)
    (parent : Fin m → ZMod (prime^(w+1))) (R : Fin 58 → List (Fin (prime+4))) : Prop :=
  let M := prime^(w+1)
  R 2 = binSyms H M ∧ R 28 = binSyms 1 1 ∧ R 53 = binSyms J W ∧
    (∀ i : Fin 6, R ((i.natAdd 33).castLE (by decide : 39 ≤ 58)) = fields i) ∧
    R 44 = binSyms H (1 : ZMod M).val ∧ (R 45).length = w ∧ R 55 = (List.ofFn fun i => binSyms H (parent i).val).flatten

abbrev DirectoryDimensions {m : ℕ} (v : Descriptor) (w W H J : ℕ) (parent : Fin m → ZMod (prime^(w+1))) :=
  DirectoryWords (fun i => (M8.RevMachine.Routines.hdr v i).map bitSymbol) w W H J parent

/-- The short and padded forms of one can both be generated from the modulus width. -/
noncomputable def directoryUnits {T Q : ℕ} {P U : Type} (bank : Fin 72 ↪ Fin T) : Pr P T Q prime U :=
  ((bzero (bank 2) (bank 44) (bank 59)).seq (countIter (bank 44) (bank 59) (bank 60))).seq
    (.act (pushBit (bank 28) true))

def DirectorySeed (w W H J : ℕ) (weightWords : List (Fin (prime+4))) (R : Fin 58 → List (Fin (prime+4))) : Prop :=
  R 2 = binSyms H (prime^(w+1)) ∧ R 53 = binSyms J W ∧
    (∀ i : Fin 6, R ((i.natAdd 33).castLE (by decide : 39 ≤ 58)) = []) ∧
    (R 45).length = w ∧ R 55 = weightWords

abbrev DirectoryParameters {m : ℕ} (w W H J : ℕ)
    (parent : Fin m → ZMod (prime^(w+1))) :=
  DirectorySeed w W H J (List.ofFn fun i => binSyms H (parent i).val).flatten

theorem directoryUnits_exec {m T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 72 ↪ Fin T) (w W H J : ℕ) (parent : Fin m → ZMod (prime^(w+1)))
    (u : HS T Q prime U) (S : Stacks T prime)
    (params : DirectoryParameters w W H J parent (fun i => S.R (bank (i.castLE (by decide)))))
    (short : S.R (bank 28) = []) (padded : S.R (bank 44) = []) (tmp : S.R (bank 59) = []) :
    ∃ z D, z.user = u.user ∧ Exec body (directoryUnits bank) (mk u S) (8*H+10) (mk z D) ∧
      DirectoryWords (fun _ => []) w W H J parent (fun i => D.R (bank (i.castLE (by decide)))) ∧
      D.L = S.L ∧ ∀ k, k ≠ bank 28 → k ≠ bank 44 → D.R k = S.R k := by
  obtain ⟨base,trailing,desc,clock,weights⟩ := params
  obtain ⟨y,yu,zero⟩ := bzero_exec body ((by decide : ([2,44,59] : List (Fin 72)).Nodup).map bank.injective) u S tmp
  have modulus : S.R (bank 2) = binSyms H (prime^(w+1)) := base
  rw [modulus,length_binSyms,padded,List.append_nil] at zero
  let B := {S with R := Function.update S.R (bank 44) (binSyms H 0)}
  obtain ⟨z,zy,inc⟩ := countIter_exec body (bank.injective.ne (by decide : (44 : Fin 72) ≠ 59)) (bank 60) y B
    (Function.update_self (bank 44) (binSyms H 0) S.R) ((Function.update_of_ne (bank.injective.ne (by decide : (59 : Fin 72) ≠ 44)) ..).trans tmp)
  let C := {S with R := Function.update S.R (bank 44) (binSyms H 1)}
  have first : Exec body ((bzero (bank 2) (bank 44) (bank 59)).seq (countIter (bank 44) (bank 59) (bank 60)))
      (mk u S) ((4*H+4)+(4*H+5)) (mk z C) := by simpa only [B,C,Function.update_idem] using Exec.seq zero inc
  have push := Exec.act (body := body) (pushBit (bank 28) true) (mk z C)
  rw [pushBit_run] at push
  have empty : C.R (bank 28) = [] := (Function.update_of_ne (bank.injective.ne (by decide : (28 : Fin 72) ≠ 44)) ..).trans short
  rw [empty] at push
  let D := {C with R := Function.update C.R (bank 28) [bitSymbol true]}
  have off (k : Fin T) (a : k ≠ bank 28) (b : k ≠ bank 44) : D.R k = S.R k :=
    (Function.update_of_ne a ..).trans (Function.update_of_ne b ..)
  have keep (i : Fin 72) (a : i.val ≠ 28) (b : i.val ≠ 44) :=
    off (bank i) (bank.injective.ne (fun e => a (congrArg Fin.val e))) (bank.injective.ne (fun e => b (congrArg Fin.val e)))
  refine ⟨z,D,zy.trans yu,(Exec.seq first push).cast (by omega) rfl,?_,rfl,off⟩
  have unit : D.R (bank 28) = [bitSymbol true] := Function.update_self ..
  have pad : D.R (bank 44) = binSyms H 1 :=
    (Function.update_of_ne (bank.injective.ne (by decide : (44 : Fin 72) ≠ 28)) ..).trans (Function.update_self ..)
  have val : (1 : ZMod (prime^(w+1))).val = 1 := ZMod.val_one'' (Nat.ne_of_gt (Nat.one_lt_pow (by omega : w+1 ≠ 0) Networks.Shared50ModularControl.prime_prime.one_lt))
  refine ⟨(keep 2 (by decide) (by decide)).trans modulus,unit,(keep 53 (by decide) (by decide)).trans trailing,?_,
    pad.trans (congrArg (binSyms H) val.symm),(congrArg List.length (keep 45 (by decide) (by decide))).trans clock,(keep 55 (by decide) (by decide)).trans weights⟩
  intro i
  exact (keep _ (by change 33+i.val ≠ 28; omega) (by change 33+i.val ≠ 44; omega)).trans (desc i)

noncomputable def directoryControls {T Q : ℕ} {P U : Type} (bank : Fin 72 ↪ Fin T) : Pr P T Q prime U :=
  (directoryUnits bank).seq ((bcopy (bank 45) (bank 71) (bank 59) (bank 60)).seq (.act (pushBit (bank 71) true)))

/-- The directory builder consumes an atom-width tally; the row scanner retains
the predecessor clock. A copy and one push supply both from the same input. -/
theorem directoryControls_exec {m T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 72 ↪ Fin T) (w W H J : ℕ) (parent : Fin m → ZMod (prime^(w+1)))
    (u : HS T Q prime U) (S : Stacks T prime)
    (params : DirectoryParameters w W H J parent (fun i => S.R (bank (i.castLE (by decide)))))
    (short : S.R (bank 28) = []) (padded : S.R (bank 44) = [])
    (clean : ∀ i : Fin 72, 59 ≤ i.val → S.R (bank i) = []) :
    ∃ z D, z.user = u.user ∧ Exec body (directoryControls bank) (mk u S) ((8*H+10)+(6*w+7)) (mk z D) ∧
      DirectoryWords (fun _ => []) w W H J parent (fun i => D.R (bank (i.castLE (by decide)))) ∧
      (D.R (bank 71)).length = w+1 ∧ D.L = S.L ∧
      ∀ k, k ≠ bank 28 → k ≠ bank 44 → k ≠ bank 71 → D.R k = S.R k := by
  obtain ⟨y,B,yu,init,dims,left,frame⟩ := directoryUnits_exec body bank w W H J parent u S params short padded (clean 59 (by decide))
  have empty (i : Fin 72) (h : 59 ≤ i.val) : B.R (bank i) = [] :=
    (frame _ (bank.injective.ne (fun e => by have := congrArg Fin.val e; change i.val = 28 at this; omega))
      (bank.injective.ne (fun e => by have := congrArg Fin.val e; change i.val = 44 at this; omega))).trans (clean i h)
  have clock : (B.R (bank 45)).length = w := dims.2.2.2.2.2.1
  obtain ⟨z,zy,copy⟩ := bcopy_exec body ((by decide : ([45,71,59,60] : List (Fin 72)).Nodup).map bank.injective)
    y B (empty 59 (by decide)) (empty 60 (by decide))
  rw [empty 71 (by decide),List.append_nil,clock] at copy
  let C := {B with R := Function.update B.R (bank 71) (B.R (bank 45))}
  have push := Exec.act (body := body) (pushBit (bank 71) true) (mk z C)
  rw [pushBit_run] at push
  let D := {B with R := Function.update B.R (bank 71) (bitSymbol true :: B.R (bank 45))}
  have pushed : Exec body (.act (pushBit (bank 71) true)) (mk z C) 1 (mk z D) := by
    simpa only [C,D,Function.update_self,Function.update_idem] using push
  have shared : (fun i : Fin 58 => D.R (bank (i.castLE (by decide)))) =
      fun i => B.R (bank (i.castLE (by decide))) := by
    funext i
    exact Function.update_of_ne (bank.injective.ne (fun eq => by
      have h := congrArg Fin.val eq; change i.val = 71 at h; omega)) ..
  refine ⟨z,D,zy.trans yu,(Exec.seq init (Exec.seq copy pushed)).cast (by omega) rfl,shared ▸ dims,?_,left,?_⟩
  · simp only [D,Function.update_self,List.length_cons,clock]
  · intro k a b c
    exact (Function.update_of_ne c ..).trans (frame k a b)

private theorem generatedDimensions_exec {m T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 72 ↪ Fin T) (v : Descriptor) (lo hi w W H J : ℕ) (parent : Fin m → ZMod (prime^(w+1)))
    (shape : ∀ i, M8.RevMachine.Routines.hdr v i = FlatCoordinateSchedule.bits (intervalValues lo hi (w+1) (prime^(w+1)) W i))
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J)
    (u : HS T Q prime U) (S : Stacks T prime)
    (params : DirectoryParameters w W H J parent (fun i => S.R (bank (i.castLE (by decide)))))
    (short : S.R (bank 28) = []) (padded : S.R (bank 44) = [])
    (clean : ∀ i : Fin 72, 59 ≤ i.val → S.R (bank i) = []) :
    ∃ z D n, z.user = u.user ∧ n ≤ ((List.finRange 6).map (intervalHeaderCosts lo hi (w+1) H J)).sum+1 ∧
      Exec body ((directoryControls bank).seq (intervalHeaders bank lo hi)) (mk u S) (((8*H+10)+(6*w+7))+n) (mk z D) ∧
      DirectoryDimensions v w W H J parent (fun i => D.R (bank (i.castLE (by decide)))) ∧
      (D.R (bank 71)).length = w+1 ∧ D.L = S.L ∧
      ∀ k, k ≠ bank 28 → k ≠ bank 44 → k ≠ bank 71 → (∀ i, k ≠ bank (descriptorPorts i)) → D.R k = S.R k := by
  obtain ⟨y,B,yu,init,dims,atom,left,off⟩ := directoryControls_exec body bank w W H J parent u S params short padded clean
  obtain ⟨base,one,tail,blank,pad,clock,weights⟩ := dims
  have port (i : Fin 6) : descriptorPorts i = ((i.natAdd 33).castLE (by decide : 39 ≤ 58)).castLE (by decide : 58 ≤ 72) :=
    Fin.ext rfl
  obtain ⟨z,D,t,zy,time,write,keepLeft,headers,frame⟩ := intervalHeaders_exec body bank lo hi (w+1) H J (prime^(w+1)) W
    hm hw y B base one tail atom (by
      intro i low high
      apply Eq.trans (off _ ?_ ?_ ?_) (clean i low) <;> apply bank.injective.ne <;> intro eq <;> have h := congrArg Fin.val eq
      · change i.val = 28 at h; omega
      · change i.val = 44 at h; omega
      · change i.val = 71 at h; omega) (by intro i; rw [port]; exact blank i)
  have keep (i : Fin 72) (outside : i.val < 33 ∨ 38 < i.val) : D.R (bank i) = B.R (bank i) := by
    apply frame
    intro j
    apply bank.injective.ne
    rw [port]
    intro eq
    have h := congrArg Fin.val eq
    change i.val = 33+j.val at h
    omega
  refine ⟨z,D,t,zy.trans yu,time,Exec.seq init write,?_,(congrArg List.length (keep 71 (by decide))).trans atom,keepLeft.trans left,
    fun k a b c o => (frame k o).trans (off k a b c)⟩
  refine ⟨(keep 2 (by decide)).trans base,(keep 28 (by decide)).trans one,(keep 53 (by decide)).trans tail,?_,
    (keep 44 (by decide)).trans pad,(congrArg List.length (keep 45 (by decide))).trans clock,(keep 55 (by decide)).trans weights⟩
  intro i
  have result := headers i
  rw [port] at result
  exact result.trans (congrArg (fun xs : List Bool => xs.map (bitSymbol (a := prime))) (shape i).symm)

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
  unfold DirectoryHeaders DirectoryDimensions DirectoryWords at headers ⊢
  have hdr (i : Fin 6) : S ((i.natAdd 33).castLE (by decide)) = R ((i.natAdd 33).castLE (by decide)) :=
    frame _ (by change 33+i.val ≠ 46; omega)
  simpa only [hdr,frame 49 (by decide),frame 48 (by decide),frame 2 (by decide),frame 28 (by decide),
    frame 53 (by decide),frame 44 (by decide),frame 45 (by decide),frame 55 (by decide)] using headers

/-- Register 46 receives the archive and register 47 retains its prefix width.
The other builder registers use the directory's private bank. -/
def remainderDirectoryPorts : Fin 15 ↪ Fin 72 :=
  ⟨![58,47,59,60,61,62,63,64,65,66,67,68,69,70,46], by decide⟩

/-- Generate the next scanner archive from the per-record words of one
physical role. Its cost uses the same scaled volume as the parent builder. -/
theorem replayDirectory_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 72 ↪ Fin T) (child : Descriptor) (proj : Matrix (Fin 64) (Fin 64) ℚ) (w W H J : ℕ)
    (weights : Fin 64 → ZMod (prime^(w+1)))
    (v : Descriptor) (positive : v.Positive) (blocks : ℕ)
    (width : v.width = 64*(w+1)) (shape : v.beforeH = blocks*prime^(64*v.width))
    (j : Fin 142080) (archive : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime) :
    let a := w+1
    let atom := bank 71
    let r := remainderDirectoryPorts.trans bank
    let scanner := fun i : Fin 58 => bank (i.castLE (by decide))
    DirectoryHeaders child proj w W H J weights (fun i => S.R (scanner i)) →
    (S.R atom).length = a → (S.R (bank 29)).length = v.beforeRows →
    (S.R (bank 30)).length = v.rows → (S.R (bank 31)).length = v.beforeH →
    (∀ i ∈ ([2,3,5,6,10,11,12] : List (Fin 15)), S.R (r i) = []) →
    (∀ k < v.beforeRows*v.rows*142080*v.beforeH, (archive k).length = (S.R (r 1)).length) →
    (S.R (r 1)).length ≤ prime^v.width →
    let prefixes := fun k => archive (directoryRoleRecord v.beforeH j k)
    S.R (r 0) = (List.range (LabelMask.records v)).flatMap prefixes ++ tail →
    let D := {S with R := Function.update (Function.update S.R (r 0) tail) (r 14) ((List.range (LabelMask.records v)).flatMap (LabelDirectory.entry prefixes 64 a) ++ S.R (r 14))}
    ∃ z n, z.user = u.user ∧ prime^v.width*n ≤ 1324*volume prime v ∧
      Exec body ((LabelSpectators.countRecords (bank 29) (bank 30) (bank 31) (r 2) (r 12) (r 3) (r 5)).seq
        ((LabelDirectorySetup.replayFromCount 64 r atom).seq (uclear (r 12)))) (mk u S) n (mk z D) ∧
      DirectoryScanInput child proj w W H J weights prefixes (S.R (r 14))
        (List.range (LabelMask.records v)) (fun i => D.R (scanner i)) := by
  intro a atom r scanner headers precision br rows bh fresh widths fits prefixes source D
  have apart (i : Fin 15) : atom ≠ r i :=
    bank.injective.ne ((by decide : ∀ i, (71 : Fin 72) ≠ remainderDirectoryPorts i) i)
  have roleWidths (k : ℕ) (hk : k < LabelMask.records v) : (prefixes k).length = (S.R (r 1)).length :=
    widths _ (directoryRoleRecord_lt (groups := v.beforeRows*v.rows) j hk)
  have records : LabelMask.records v = (v.beforeRows*v.rows*blocks)*(prime^a)^(64*64) := by
    simp only [a,LabelMask.records,shape,width,← pow_mul]
    ring_nf
  have nodup : [bank 29,bank 30,bank 31,r 2,r 12,r 3,r 5].Nodup :=
    (by decide : ([29,30,31,59,69,60,62] : List (Fin 72)).Nodup).map bank.injective
  obtain ⟨y,c,same,charge,build⟩ := LabelSpectators.records_exec body _ _ _ _ _ _ _ nodup v positive u S br rows bh (by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> apply fresh <;> decide)
  let N := LabelMask.records v
  let C : Stacks T prime := {S with R := Function.update S.R (r 12) (List.replicate N tick)}
  have off (i : Fin 15) (h : i ≠ 12) : C.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne h) ..
  have run := LabelDirectorySetup.replay_from_count (body := body) 64 (v.beforeRows*v.rows*blocks) r atom apart y C prefixes tail (by
    intro i hi
    have ne : i ≠ 12 := by intro eq; subst i; revert hi; decide
    rw [off _ ne]
    apply fresh
    simp_all)
  have prec : (C.R atom).length = a := by simpa [C,Function.update_of_ne (apart 12)] using precision
  have count : (C.R (r 12)).length = N := by simp [C]
  simp only [prec,count,off 0 (by decide),off 1 (by decide),off 14 (by decide)] at run
  obtain ⟨z,n,user,paid,exec⟩ := run (by dsimp [a]; omega) records source roleWidths
  let F : Stacks T prime := {C with R := Function.update (Function.update C.R (r 0) tail) (r 14) (D.R (r 14))}
  have output : D.R (r 14) = (List.range N).flatMap (LabelDirectory.entry prefixes 64 a) ++ S.R (r 14) := by simp [D,N]
  have middle : Exec body (LabelDirectorySetup.replayFromCount 64 r atom) (mk y C) n (mk z F) := by simpa only [F,output] using exec
  obtain ⟨z',last,clear⟩ := uclear_exec body (r 12) z F
  have len : (F.R (r 12)).length = N := by simpa [F] using count
  rw [len] at clear
  have restored : {F with R := Function.update F.R (r 12) []} = D := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h : k = r 12
    · subst k; simp [D,fresh]
    by_cases dst : k = r 14
    · subst k; simp [F]
    simp [F,C,D,Function.update_apply,h,dst]
  rw [restored] at clear
  refine ⟨z',c+(n+(2*N+2)),last.trans (user.trans same),?_,Exec.seq build (Exec.seq middle clear),?_⟩
  rotate_left
  · have frame (i : Fin 58) (off : i.val ≠ 46) : D.R (scanner i) = S.R (scanner i) := by
      have sep : scanner i ≠ r 14 := bank.injective.ne (fun eq => off (congrArg Fin.val eq))
      have src : scanner i ≠ r 0 := bank.injective.ne (by
        intro eq
        have h := congrArg Fin.val eq
        change i.val = 58 at h
        omega)
      simp [D, Function.update_of_ne sep, Function.update_of_ne src]
    refine ⟨?_,?_,headers.of_frame frame⟩
    · change D.R (r 14) = _
      simp [D,a]
    · intro k hk
      rw [frame 47 (by decide)]
      exact (roleWidths k (List.mem_range.mp hk)).symm
  let scale := prime^v.width
  have hr : 1 ≤ N := Nat.mul_pos (Nat.mul_pos positive.1 positive.2.1) positive.2.2.1
  have hs : 1 ≤ scale := pow_pos Networks.Shared50ModularControl.prime_prime.pos _
  have hw : v.width ≤ scale := (Nat.lt_pow_self (n := v.width) Networks.Shared50ModularControl.prime_prime.one_lt).le
  have perRecord : 6*(S.R (r 1)).length+15*(a*(64*64))+28 ≤ 994*scale := by
    change _ ≤ scale at fits
    omega
  have overhead : 8*a+4*(a*(64*64))+24 ≤ 288*(N*scale) := by
    have := Nat.le_mul_of_pos_left scale hr
    omega
  have budget : n ≤ 1282*(N*scale) := by
    have := Nat.mul_le_mul_left N perRecord
    change n ≤ 8*a+N*_+4*(a*(64*64))+24 at paid
    nlinarith
  have cost : c+(n+(2*N+2)) ≤ 1324*(N*scale) := by
    change c ≤ 28*N+10 at charge
    have := Nat.le_mul_of_pos_right N hs
    omega
  calc
    _ ≤ scale*(1324*(N*scale)) := Nat.mul_le_mul_left _ cost
    _ = 1324*(N*scale*1*scale*1) := by ring
    _ ≤ _ := by
      change _ ≤ 1324*(N*scale*v.between*scale*v.afterD)
      gcongr <;> first | exact positive.2.2.2.1 | exact positive.2.2.2.2

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

/-- At the outermost node the padded unit word supplies all 64 parent weights. -/
noncomputable def rootWeights {T Q : ℕ} {P U : Type} (bank : Fin 72 ↪ Fin T) : Pr P T Q prime U :=
  LabelTraversal.sequence (fun _ : Fin 64 => bcopy (bank 44) (bank 55) (bank 59) (bank 60)) (List.finRange 64)

private theorem rootWeights_writes {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 72 ↪ Fin T) (one : List (Fin (prime+4))) :
    LabelTraversal.Writes body (fun R => R (bank 44) = one ∧ R (bank 59) = [] ∧ R (bank 60) = [])
      (bank 55) (rootWeights bank) (List.ofFn fun _ : Fin 64 => one).flatten (64*(6*one.length+6)+1) := by
  let ok := fun R : Regs T prime => R (bank 44) = one ∧ R (bank 59) = [] ∧ R (bank 60) = []
  have stable (R : Regs T prime) (xs) (h : ok R) : ok (Function.update R (bank 55) xs) := by
    simpa only [ok,Function.update_of_ne (bank.injective.ne (by decide : (44 : Fin 72) ≠ 55)),
      Function.update_of_ne (bank.injective.ne (by decide : (59 : Fin 72) ≠ 55)),
      Function.update_of_ne (bank.injective.ne (by decide : (60 : Fin 72) ≠ 55))] using h
  have copy (_ : Fin 64) : LabelTraversal.Writes body ok (bank 55)
      (bcopy (bank 44) (bank 55) (bank 59) (bank 60)) one (6*one.length+6) := by
    intro u S ⟨word,tmp,saved⟩
    obtain ⟨z,user,run⟩ := bcopy_exec body ((by decide : ([44,55,59,60] : List (Fin 72)).Nodup).map bank.injective) u S tmp saved
    rw [word] at run
    exact ⟨z,_,user,le_rfl,run⟩
  simpa only [rootWeights,List.flatMap_def,List.ofFn_eq_map,List.length_finRange] using
    LabelTraversal.sequence_writes stable copy (List.finRange 64)

def ParentParameters (root : Bool) {w : ℕ} (W H J : ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
    (R : Fin 58 → List (Fin (prime+4))) : Prop :=
  if root then (∀ i, parent i = 1) ∧ DirectorySeed w W H J [] R
  else DirectoryParameters w W H J parent R

noncomputable def weightedDimensions {T Q : ℕ} {P U : Type} (root : Bool)
    (bank : Fin 72 ↪ Fin T) (lo hi : ℕ) : Pr P T Q prime U :=
  let setup := (directoryControls bank).seq (intervalHeaders bank lo hi)
  if root then setup.seq (rootWeights bank) else setup

private theorem weightedDimensions_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 72 ↪ Fin T) (v : Descriptor) (lo hi w W H J : ℕ) (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (shape : ∀ i, M8.RevMachine.Routines.hdr v i = FlatCoordinateSchedule.bits (intervalValues lo hi (w+1) (prime^(w+1)) W i))
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J)
    (u : HS T Q prime U) (S : Stacks T prime)
    (params : ParentParameters root W H J parent (fun i => S.R (bank (i.castLE (by decide)))))
    (short : S.R (bank 28) = []) (padded : S.R (bank 44) = [])
    (clean : ∀ i : Fin 72, 59 ≤ i.val → S.R (bank i) = []) :
    ∃ z D n t, z.user = u.user ∧ n ≤ ((List.finRange 6).map (intervalHeaderCosts lo hi (w+1) H J)).sum+1 ∧ t ≤ 64*(6*H+6)+1 ∧
      Exec body (weightedDimensions root bank lo hi) (mk u S) ((((8*H+10)+(6*w+7))+n)+t) (mk z D) ∧
      DirectoryDimensions v w W H J parent (fun i => D.R (bank (i.castLE (by decide)))) ∧
      (D.R (bank 71)).length = w+1 ∧ D.L = S.L ∧
      ∀ k, k ≠ bank 28 → k ≠ bank 44 → k ≠ bank 71 → k ≠ bank 55 → (∀ i, k ≠ bank (descriptorPorts i)) → D.R k = S.R k := by
  cases root with
  | false =>
    obtain ⟨z,D,n,user,time,run,dims,atom,left,off⟩ :=
      generatedDimensions_exec body bank v lo hi w W H J parent shape hm hw u S params short padded clean
    exact ⟨z,D,n,0,user,time,Nat.zero_le _,run,dims,atom,left,fun k a b c _ => off k a b c⟩
  | true =>
    obtain ⟨units,empty⟩ := params
    obtain ⟨y,B,n,user,time,run,dims,atom,left,off⟩ :=
      generatedDimensions_exec body bank v lo hi w W H J (fun _ : Fin 0 => 1) shape hm hw u S empty short padded clean
    obtain ⟨base,unit,trailing,headers,one,clock,weights⟩ := dims
    have privateFree (i : Fin 72) (hi : 59 ≤ i.val) (away : i ≠ 71) : B.R (bank i) = [] := by
      apply Eq.trans (off _ (bank.injective.ne (by omega)) (bank.injective.ne (by omega)) (bank.injective.ne away) ?_) (clean i hi)
      intro j
      apply bank.injective.ne
      have bound := (by decide : ∀ j, (descriptorPorts j).val ≤ 38) j
      omega
    let single := binSyms (A := prime) H (1 : ZMod (prime^(w+1))).val
    obtain ⟨z,t,zy,cost,write⟩ := rootWeights_writes body bank single y B
      ⟨one,privateFree 59 (by decide) (by decide),privateFree 60 (by decide) (by decide)⟩
    let D := {B with R := Function.update B.R (bank 55) ((List.ofFn fun _ : Fin 64 => single).flatten ++ B.R (bank 55))}
    have keep (i : Fin 72) (hi : i ≠ 55) : D.R (bank i) = B.R (bank i) := Function.update_of_ne (bank.injective.ne hi) ..
    refine ⟨z,D,n,t,zy.trans user,time,by simpa only [single,length_binSyms] using cost,Exec.seq run write,?_,
      (congrArg List.length (keep 71 (by decide))).trans atom,left,fun k a b c e h => (Function.update_of_ne e ..).trans (off k a b c h)⟩
    refine ⟨(keep 2 (by decide)).trans base,(keep 28 (by decide)).trans unit,(keep 53 (by decide)).trans trailing,?_,
      (keep 44 (by decide)).trans one,(congrArg List.length (keep 45 (by decide))).trans clock,?_⟩
    · intro i
      exact (keep _ (by change (⟨33+i.val,_⟩ : Fin 72) ≠ 55; intro eq; have h := congrArg Fin.val eq; change 33+i.val = 55 at h; omega)).trans (headers i)
    · change B.R (bank 55) = _ at weights
      change Function.update B.R (bank 55) _ (bank 55) = _
      simp [Function.update_self,weights,units,single]

def projectorSeedPorts : Fin 5 ↪ Fin 72 := ⟨![49,44,48,59,60],by decide⟩

/-- Initialize the size controls and projector before constructing the directory. -/
noncomputable def remainderOwnerSetup {T Q : ℕ} {P U : Type} (root : Bool) (lo hi : ℕ) (bank : Fin 72 ↪ Fin T) : Pr P T Q prime U :=
  ((weightedDimensions root bank lo hi).seq (writeBinaryMatrix (intervalSeed lo hi) (projectorSeedPorts.trans bank))).seq
    (remainderDirectoryProgram bank)

def directoryHeaderTime (w H : ℕ) := (64*(6*H+6)+1) + ((8*H+10)+(6*w+7)) + (4*H+4 + (64*(64*(6*H+6)+1)+1 + (2*H+2)))

open IntegerMultBounds.Swap.Modular in
/-- Both owner entry paths use the same precision, weight and matrix setup.
All stacks outside the listed right-tape writes are preserved. -/
theorem prepareDirectoryHeaders_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 72 ↪ Fin T) (child : Descriptor) (lo hi w W H J : ℕ)
    (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (fields : ∀ i, M8.RevMachine.Routines.hdr child i = FlatCoordinateSchedule.bits (intervalValues lo hi (w+1) (prime^(w+1)) W i))
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (u : HS T Q prime U) (raw : Stacks T prime)
    (params : ParentParameters root W H J parent (fun i => raw.R (bank (i.castLE (by decide)))))
    (short : raw.R (bank 28) = []) (padded : raw.R (bank 44) = []) (spare : raw.R (bank 49) = [])
    (clean : ∀ i : Fin 72, 59 ≤ i.val → raw.R (bank i) = []) :
    let proj := Matrix.diagonal fun i : Fin 64 => if lo ≤ i.val ∧ i.val < hi then (1 : ℚ) else 0
    let matrix := matrixWords prime H (reduce (prime^(w+1)) proj)
    ∃ z S n, z.user = u.user ∧
      n ≤ directoryHeaderTime w H + (((List.finRange 6).map (intervalHeaderCosts lo hi (w+1) H J)).sum+1) ∧
      Exec body ((weightedDimensions root bank lo hi).seq (writeBinaryMatrix (intervalSeed lo hi) (projectorSeedPorts.trans bank)))
        (mk u raw) n (mk z S) ∧
      DirectoryHeaders child proj w W H J parent (fun i => S.R (bank (i.castLE (by decide)))) ∧
      (S.R (bank 71)).length = w+1 ∧ S.R (bank 48) = matrix ++ raw.R (bank 48) ∧ S.L = raw.L ∧
      ∀ k, (∀ i ∈ ([28,33,34,35,36,37,38,44,48,55,71] : List (Fin 72)), k ≠ bank i) → S.R k = raw.R k := by
  intro proj matrix
  obtain ⟨initial,loaded,d,t,same,descriptorBound,weightBound,units,dims,atom,leftBank,unchanged⟩ :=
    weightedDimensions_exec body bank child lo hi w W H J root parent fields hm hw u raw params short padded clean
  let writes : List (Fin 72) := [28,33,34,35,36,37,38,44,48,55,71]
  have keep (k : Fin T) (off : ∀ i ∈ writes, k ≠ bank i) : loaded.R k = raw.R k :=
    unchanged k (off _ (by decide)) (off _ (by decide)) (off _ (by decide)) (off _ (by decide))
      (fun j => off _ ((by decide : ∀ j, descriptorPorts j ∈ writes) j))
  have frame (i : Fin 72) (outside : i ∉ writes) := keep (bank i)
    (fun j hj => bank.injective.ne (fun h => outside (h ▸ hj)))
  let ports := projectorSeedPorts.trans bank
  have one : loaded.R (bank 44) = binSyms H (1 : ZMod (prime^(w+1))).val := dims.2.2.2.2.1
  obtain ⟨y,n,yu,time,seed⟩ := writeBinaryMatrix_writes (M := prime^(w+1)) body (intervalSeed lo hi) H ports initial loaded
    ⟨one,(frame 49 (by decide)).trans spare,(frame 59 (by decide)).trans (clean 59 (by decide)),
      (frame 60 (by decide)).trans (clean 60 (by decide))⟩
  let S := {loaded with R := Function.update loaded.R (bank 48) (matrix ++ loaded.R (bank 48))}
  have seedRun : Exec body (writeBinaryMatrix (intervalSeed lo hi) ports) (mk initial loaded) n (mk y S) := by
    simpa only [show ports 2 = bank 48 from rfl,S,matrix,proj,reduce_intervalSeed] using seed
  have stay (i : Fin 72) (hi : i.val ≠ 48) : S.R (bank i) = loaded.R (bank i) :=
    Function.update_of_ne (bank.injective.ne (fun h => hi (congrArg Fin.val h))) ..
  have oldMatrix : loaded.R (bank 48) = raw.R (bank 48) := unchanged _ (by simp) (by simp) (by simp) (by simp)
    (fun i => bank.injective.ne ((by decide : ∀ i, (48 : Fin 72) ≠ descriptorPorts i) i))
  refine ⟨y,S,_,yu.trans same,?_,Exec.seq units seedRun,?_,(congrArg List.length (stay 71 (by decide))).trans atom,?_,leftBank,?_⟩
  · unfold directoryHeaderTime; omega
  · refine ⟨(stay 49 (by decide)).trans ((frame 49 (by decide)).trans spare),⟨loaded.R (bank 48),Function.update_self ..⟩,?_⟩
    obtain ⟨base,unit,trailing,desc,one,clock,weights⟩ := dims
    refine ⟨(stay 2 (by decide)).trans base,(stay 28 (by decide)).trans unit,(stay 53 (by decide)).trans trailing,?_,
      (stay 44 (by decide)).trans one,(congrArg List.length (stay 45 (by decide))).trans clock,(stay 55 (by decide)).trans weights⟩
    intro i
    exact (stay _ (by change 33+i.val ≠ 48; omega)).trans (desc i)
  · simp [S,oldMatrix]
  · intro k off
    exact (Function.update_of_ne (off 48 (by decide)) ..).trans (keep k off)

private theorem directoryHeader_charge (v : Descriptor) (positive : v.Positive) (w rows : ℕ)
    (width : v.width = 64*(w+1)) (split : v.rows = 142080*rows) :
    prime^v.width*directoryHeaderTime w (prime^(w+1)).size*142080 ≤ volume prime v := by
  let M := prime^(w+1)
  have two : 2 ≤ M := by
    change 2 ≤ prime^(w+1)
    rw [pow_succ]
    exact (show 2 ≤ prime from Networks.Shared50ModularControl.prime_prime.one_lt).trans
      (Nat.le_mul_of_pos_left _ (pow_pos Networks.Shared50ModularControl.prime_prime.pos _))
  have digits : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have clock : w+1 ≤ M := (Nat.lt_pow_self (n := w+1) Networks.Shared50ModularControl.prime_prime.one_lt).le
  have time : directoryHeaderTime w M.size ≤ prime^v.width := by
    rw [width,Nat.mul_comm 64,pow_mul]
    change _ ≤ M^64
    calc
      _ ≤ 65536*M := by unfold directoryHeaderTime; omega
      _ ≤ M^16*M := Nat.mul_le_mul_right _ (show 2^16 ≤ M^16 from Nat.pow_le_pow_left two _)
      _ = M^17 := (pow_succ M 16).symm
      _ ≤ M^64 := Nat.pow_le_pow_right (by omega) (by decide)
  have rowsFit : 142080 ≤ v.rows := by
    have pos := positive.2.1
    rw [split] at pos ⊢
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left pos)
  calc
    _ = 1*142080*1*prime^v.width*1*directoryHeaderTime w M.size*1 := by ring
    _ ≤ volume prime v := by
      unfold volume
      gcongr <;> first | exact positive.1 | exact rowsFit | exact positive.2.2.1 | exact positive.2.2.2.1 | exact time | exact positive.2.2.2.2

private theorem descriptor_charge (v : Descriptor) (positive : v.Positive) (w rows lo hi H J W n : ℕ)
    (width : v.width = 64*(w+1)) (split : v.rows = 142080*rows) (tail : W = v.between*v.afterD)
    (ordered : lo ≤ hi) (fits : hi ≤ 64) (precision : H = (prime^(w+1)).size) (digits : J = W.size)
    (time : n ≤ ((List.finRange 6).map (intervalHeaderCosts lo hi (w+1) H J)).sum+1) :
    prime^v.width*n*142080 ≤ volume prime v := by
  let M := prime^(w+1)
  have two : 2 ≤ M := (show 2 ≤ prime from Networks.Shared50ModularControl.prime_prime.one_lt).trans
    (Nat.le_self_pow (by omega : w+1 ≠ 0) prime)
  have budget := time.trans (intervalHeaderCost_le lo hi (w+1) H J M W ordered fits
    (Nat.lt_pow_self Networks.Shared50ModularControl.prime_prime.one_lt).le
    (precision ▸ Nat.size_le.mpr Nat.lt_two_pow_self) (digits ▸ Nat.size_le.mpr Nat.lt_two_pow_self)
    two (tail ▸ Nat.mul_pos positive.2.2.2.1 positive.2.2.2.2))
  have scale : M^64 = prime^v.width := by rw [width,Nat.mul_comm 64,pow_mul]
  rw [scale] at budget
  have rowsFit : 142080 ≤ v.rows := by
    have pos := positive.2.1
    rw [split] at pos ⊢
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mul_pos_left pos)
  calc
    _ = 1*142080*1*prime^v.width*n := by ring
    _ ≤ v.beforeRows*v.rows*v.beforeH*prime^v.width*(prime^v.width*W) := by
      gcongr <;> first | exact positive.1 | exact rowsFit | exact positive.2.2.1
    _ = volume prime v := by rw [tail]; unfold volume; ring

private theorem replayOwnerTime_le (scale copies n k clear volume : ℕ)
    (setup : scale*n*copies ≤ volume+volume) (core : scale*k*copies ≤ 1324*volume)
    (release : scale*clear*copies ≤ volume) : scale*(n+(k+clear))*copies ≤ 1327*volume := by
  rw [Nat.mul_add, Nat.mul_add, Nat.add_mul, Nat.add_mul]
  omega

open IntegerMultBounds.Swap.Modular in
/-- Prepare the scanner's shared bank from inherited labels while keeping all five
owner registers available for the packed role and the subsequent row counter. -/
theorem remainderDirectory_prepareOwner {K Q : ℕ} {P U : Type} (room : 72 ≤ K)
    (body : P → Pr P (K+5) Q prime U) (layout child : Descriptor) (w rows B W H J : ℕ)
    (positive : layout.Positive) (width : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
    (shape : layout.beforeH = B*prime^(64*((w+1)*64))) (lo hi : ℕ) (precision : H = (prime^(w+1)).size) (digits : J = W.size)
    (tailSize : W = layout.between*layout.afterD) (ordered : lo ≤ hi) (hiFits : hi ≤ 64)
    (fields : ∀ i, M8.RevMachine.Routines.hdr child i = FlatCoordinateSchedule.bits (intervalValues lo hi (w+1) (prime^(w+1)) W i))
    (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1))) (word : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
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
    (raw.R (bank 31)).length = layout.beforeH →
    (∀ i : Fin K, 59 ≤ i.val → raw.R (i.castAdd 5) = []) →
    raw.R (bank 58) = (List.range parents).flatMap word ++ tail →
    (∀ i < parents, (word i).length = (raw.R (bank 47)).length) →
    (raw.R (bank 47)).length ≤ prime^layout.width →
    raw.R (bank 28) = [] → raw.R (bank 44) = [] → raw.R (bank 49) = [] → ParentParameters root W H J parent (fun i => raw.R (bank (i.castLE (by decide)))) →
    ∃ z D elapsed, z.user = u.user ∧
      prime^layout.width*elapsed*142080 ≤ (366+16*64*64+19*64+344)*volume prime layout + prime^layout.width*inherited*142080 ∧
      Exec body (remainderOwnerSetup root lo hi bank) (mk u raw) elapsed (mk z D) ∧
      DirectoryScanInput child proj w W H J parent (fun j => word (j/box)) (raw.R (bank 46))
        (List.range (LabelMask.records directory)) (fun i => D.R (bank (i.castLE (by decide)))) ∧
      (∀ i : Fin K, 58 ≤ i.val → D.R (i.castAdd 5) = []) ∧
      D.R (bank 48) = matrix ++ raw.R (bank 48) ∧
      (∀ i : Fin 58, i ∉ ([28,33,34,35,36,37,38,44,46,48,55] : List (Fin 58)) → D.R (bank (i.castLE (by decide))) = raw.R (bank (i.castLE (by decide)))) ∧
      (∀ i : Fin 58, D.L (bank (i.castLE (by decide))) = raw.L (bank (i.castLE (by decide)))) ∧
      (∀ k, (D.L k).length ≤ (raw.L k).length) ∧
      (∀ i : Fin 5, D.R (i.natAdd K) = raw.R (i.natAdd K) ∧ D.L (i.natAdd K) = raw.L (i.natAdd K)) := by
  intro proj matrix bank r parents box directory scratch inherited br nr bh clean source widths fits short padded spare params
  obtain ⟨y,S,n,same,time,setup,headers,atom,matrixReady,leftBank,unchanged⟩ :=
    prepareDirectoryHeaders_exec body bank child lo hi w W H J root parent fields
      (precision ▸ Nat.lt_size_self _) (digits ▸ Nat.lt_size_self _) u raw params short padded spare (fun i hi => clean (i.castLE room) hi)
  let writes : List (Fin 72) := [28,33,34,35,36,37,38,44,48,55,71]
  have frame (i : Fin 72) (outside : i ∉ writes) : S.R (bank i) = raw.R (bank i) :=
    unchanged _ (fun j hj => bank.injective.ne (fun eq => outside (eq ▸ hj)))
  have privateClean (i : Fin K) (hi : 59 ≤ i.val) (away : i.val ≠ 71) : S.R (i.castAdd 5) = [] := by
    apply Eq.trans (unchanged _ ?_) (clean i hi)
    intro j hj eq
    have h := congrArg Fin.val eq
    change i.val = j.val at h
    have := (by decide : ∀ j ∈ writes, j.val ≤ 55 ∨ j.val = 71) j hj
    omega
  have unit : (S.R (bank 28)).length = 1 := by
    have one : S.R (bank 28) = binSyms 1 1 := headers.2.2.2.1
    rw [one,length_binSyms]
  have fresh (i : Fin 15) (hi : i ∈ ([2,3,4,5,6,7,9,10,11,12,13] : List (Fin 15))) : S.R (r i) = [] := by
    have bounds := (by decide : ∀ j ∈ ([2,3,4,5,6,7,9,10,11,12,13] : List (Fin 15)),
      59 ≤ (remainderDirectoryPorts j).val ∧ (remainderDirectoryPorts j).val ≠ 71) i hi
    exact privateClean ((remainderDirectoryPorts i).castLE room) bounds.1 bounds.2
  obtain ⟨z,t,user,paid,run,input,right,left,size,cleared,off⟩ :=
    remainderDirectory_build body bank layout w rows B positive width split shape word tail y S
      ((congrArg List.length (frame 29 (by decide))).trans br) ((congrArg List.length (frame 30 (by decide))).trans nr)
      ((congrArg List.length (frame 31 (by decide))).trans bh) atom
      unit fresh ((frame 58 (by decide)).trans source)
      (fun i hi => (widths i hi).trans (congrArg List.length (frame 47 (by decide))).symm)
      ((congrArg List.length (frame 47 (by decide))).le.trans fits)
  have ready := input _ _ _ _ _ _ headers
  rw [frame 46 (by decide)] at ready
  refine ⟨z,_,n+t,user.trans same,?_,Exec.seq setup run,ready,?_,
    (right 48 (by decide)).trans matrixReady,?_,?_,?_,?_⟩
  · have controls := directoryHeader_charge layout positive w rows width split
    rw [← precision] at controls
    have desc := descriptor_charge layout positive w rows lo hi H J W _ width split tailSize ordered hiFits precision digits le_rfl
    have bound := Nat.mul_le_mul_right 142080 (Nat.mul_le_mul_left (prime^layout.width) time)
    rw [Nat.mul_add,Nat.add_mul] at bound
    change prime^layout.width*t*142080 ≤ _ + prime^layout.width*((scratch.map (fun i => 4*(S.L i).length)).sum + 2*tail.length)*142080 at paid
    rw [leftBank] at paid
    rw [Nat.mul_add,Nat.add_mul]
    exact (Nat.add_le_add (bound.trans (Nat.add_le_add controls desc)) paid).trans_eq (by dsimp only [inherited]; ring)
  · intro i high
    by_cases low : i.val < 72
    · exact cleared (privateClean ((65 : Fin 72).castLE room) (by decide : 59 ≤ 65) (by decide : (65 : ℕ) ≠ 71)) ⟨i.val,low⟩ high
    · have outside (j : Fin 72) : bank j ≠ i.castAdd 5 := by
        intro eq
        have h := congrArg Fin.val eq
        change j.val = i.val at h
        omega
      exact (off _ outside).1.trans (privateClean i (by omega) (by omega))
  · intro i hi
    have apart := (by decide : ∀ j : Fin 58, j ∉ ([28,33,34,35,36,37,38,44,46,48,55] : List (Fin 58)) →
      j.val ≠ 46 ∧ j.castAdd 14 ∉ writes) i hi
    exact (right i apart.1).trans (frame _ apart.2)
  · intro i; exact (left i).trans (congrFun leftBank _)
  · intro k; exact (size k).trans_eq (congrArg List.length (congrFun leftBank k))
  · intro i
    have outside (j : Fin 72) : bank j ≠ i.natAdd K := by
      intro eq
      have h := congrArg Fin.val eq
      change j.val = K+i.val at h
      omega
    exact ⟨(off _ outside).1.trans (unchanged _ (fun j _ => (outside j).symm)),(off _ outside).2.trans (congrFun leftBank _)⟩

open IntegerMultBounds.Swap.Modular in
/-- Enter a recursive role scanner from the physical parameter bank and its
routed replay stream; release the private precision tape before the scan. -/
theorem prepareReplayOwner_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 72 ↪ Fin T) (layout child : Descriptor) (w rows blocks W H J lo hi : ℕ)
    (positive : layout.Positive) (width : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
    (shape : layout.beforeH = blocks*prime^(64*layout.width))
    (precision : H = (prime^(w+1)).size) (digits : J = W.size) (tailSize : W = layout.between*layout.afterD)
    (ordered : lo ≤ hi) (hiFits : hi ≤ 64)
    (fields : ∀ i, M8.RevMachine.Routines.hdr child i = FlatCoordinateSchedule.bits (intervalValues lo hi (w+1) (prime^(w+1)) W i))
    (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1))) (j : Fin 142080)
    (archive : ℕ → List (Fin (prime+4))) (u : HS T Q prime U) (raw : Stacks T prime) :
    let v := role layout 142080
    let r := remainderDirectoryPorts.trans bank
    let scanner := fun i : Fin 58 => bank (i.castLE (by decide))
    let prefixes := fun k => archive (directoryRoleRecord v.beforeH j k)
    let proj := Matrix.diagonal fun i : Fin 64 => if lo ≤ i.val ∧ i.val < hi then (1 : ℚ) else 0
    (raw.R (bank 29)).length = layout.beforeRows → (raw.R (bank 30)).length = rows →
    (raw.R (bank 31)).length = layout.beforeH →
    raw.R (bank 58) = (List.range (LabelMask.records v)).flatMap prefixes →
    (∀ k < layout.beforeRows*rows*142080*layout.beforeH, (archive k).length = (raw.R (bank 47)).length) →
    (raw.R (bank 47)).length ≤ prime^layout.width →
    raw.R (bank 28) = [] → raw.R (bank 44) = [] → raw.R (bank 49) = [] →
    (∀ i : Fin 72, 59 ≤ i.val → raw.R (bank i) = []) →
    ParentParameters root W H J parent (fun i => raw.R (scanner i)) →
    let setup := (weightedDimensions root bank lo hi).seq (writeBinaryMatrix (intervalSeed lo hi) (projectorSeedPorts.trans bank))
    let replay := (LabelSpectators.countRecords (bank 29) (bank 30) (bank 31) (r 2) (r 12) (r 3) (r 5)).seq
      ((LabelDirectorySetup.replayFromCount 64 r (bank 71)).seq (uclear (r 12)))
    ∃ z D n, z.user = u.user ∧ prime^layout.width*n*142080 ≤ 1327*volume prime layout ∧
      Exec body (setup.seq (replay.seq (uclear (bank 71)))) (mk u raw) n (mk z D) ∧
      DirectoryScanInput child proj w W H J parent prefixes (raw.R (bank 46))
        (List.range (LabelMask.records v)) (fun i => D.R (scanner i)) ∧
      (∀ i : Fin 72, 58 ≤ i.val → D.R (bank i) = []) ∧ D.L = raw.L ∧
      ∀ k, (∀ i : Fin 72, k ≠ bank i) → D.R k = raw.R k := by
  intro v r scanner prefixes proj br nr bh source widths fits short padded spare clean params setup replay
  obtain ⟨y,S,n,same,time,head,headers,atom,_,left,unchanged⟩ :=
    prepareDirectoryHeaders_exec body bank child lo hi w W H J root parent fields
      (precision ▸ Nat.lt_size_self _) (digits ▸ Nat.lt_size_self _) u raw params short padded spare clean
  let writes : List (Fin 72) := [28,33,34,35,36,37,38,44,48,55,71]
  have frame (i : Fin 72) (outside : i ∉ writes) : S.R (bank i) = raw.R (bank i) :=
    unchanged _ (fun l hl => bank.injective.ne (fun eq => outside (eq ▸ hl)))
  have vr : v.rows = rows := by simp [v,role,split]
  have hp := RecursiveRowsNodeLayout.role_positive 142080 layout (by decide) positive ⟨rows,split⟩
  let word := (List.range (LabelMask.records v)).flatMap (LabelDirectory.entry prefixes 64 (w+1)) ++ S.R (bank 46)
  let F : Stacks T prime := {S with R := Function.update (Function.update S.R (bank 58) []) (bank 46) word}
  have run := replayDirectory_exec body bank child proj w W H J parent v hp blocks width shape j archive [] y S headers atom
    ((congrArg List.length (frame 29 (by decide))).trans br) ((congrArg List.length (frame 30 (by decide))).trans (nr.trans vr.symm))
    ((congrArg List.length (frame 31 (by decide))).trans bh)
  obtain ⟨b,k,user,paid,exec,input⟩ := run (by
    intro l hl
    have off := (by decide : ∀ l ∈ ([2,3,5,6,10,11,12] : List (Fin 15)), remainderDirectoryPorts l ∉ writes ∧ 59 ≤ (remainderDirectoryPorts l).val) l hl
    exact (frame _ off.1).trans (clean _ off.2)) (by
    intro k hk
    rw [vr] at hk
    exact (widths k hk).trans (congrArg List.length (frame 47 (by decide))).symm)
    ((congrArg List.length (frame 47 (by decide))).le.trans fits)
    (by change S.R (bank 58) = (List.range (LabelMask.records v)).flatMap prefixes ++ []; rw [List.append_nil]; exact (frame 58 (by decide)).trans source)
  obtain ⟨z,last,clear⟩ := uclear_exec body (bank 71) b F
  let D := {F with R := Function.update F.R (bank 71) []}
  have size : (F.R (bank 71)).length = w+1 := by simpa [F] using atom
  rw [size] at clear
  refine ⟨z,D,n+(k+(2*(w+1)+2)),last.trans (user.trans same),?_,Exec.seq head (Exec.seq exec clear),?_,?_,left,?_⟩
  · have controls := directoryHeader_charge layout positive w rows width split
    rw [← precision] at controls
    have desc := descriptor_charge layout positive w rows lo hi H J W _ width split tailSize ordered hiFits precision digits le_rfl
    have bound := Nat.mul_le_mul_right 142080 (Nat.mul_le_mul_left (prime^layout.width) time)
    rw [Nat.mul_add,Nat.add_mul] at bound
    have release : 2*(w+1)+2 ≤ directoryHeaderTime w H := by unfold directoryHeaderTime; omega
    have close := (Nat.mul_le_mul_right 142080 (Nat.mul_le_mul_left (prime^layout.width) release)).trans controls
    have vol : volume prime v*142080 = volume prime layout := by
      unfold volume; rw [vr,split]; dsimp only [v,role]; ring
    have core := Nat.mul_le_mul_right 142080 paid
    change prime^layout.width*k*142080 ≤ 1324*volume prime v*142080 at core
    rw [Nat.mul_assoc 1324,vol] at core
    exact replayOwnerTime_le _ _ _ _ _ _ (bound.trans (Nat.add_le_add controls desc)) core close
  · have equal (i : Fin 58) : D.R (scanner i) = F.R (scanner i) :=
      Function.update_of_ne (bank.injective.ne (by intro eq; have h := congrArg Fin.val eq; change i.val = 71 at h; omega)) ..
    change DirectoryScanInput _ _ _ _ _ _ _ _ (S.R (bank 46)) _ (fun i => F.R (scanner i)) at input
    simpa only [equal,frame 46 (by decide)] using input
  · intro i hi
    by_cases src : i = 58
    · subst i; simp [D,F]
    by_cases prec : i = 71
    · subst i; simp [D]
    have off : i ∉ writes := by
      intro h
      have := (by decide : ∀ l ∈ writes, l.val ≤ 55 ∨ l = 71) i h
      omega
    have ne : i ≠ 46 := by intro eq; subst i; exact (by decide : ¬ 58 ≤ (46 : Fin 72).val) hi
    simpa [D,F,Function.update_of_ne (bank.injective.ne prec),Function.update_of_ne (bank.injective.ne ne),
      Function.update_of_ne (bank.injective.ne src)] using (frame i off).trans (clean i (by
        have : i.val ≠ 58 := fun eq => src (Fin.ext eq)
        omega))
  · intro k off
    simpa [D,F,Function.update_of_ne (off 71),Function.update_of_ne (off 46),Function.update_of_ne (off 58)] using
      unchanged k (fun l _ => off l)

end IntegerMultBounds.MathlibTM2.M6.BitNode
