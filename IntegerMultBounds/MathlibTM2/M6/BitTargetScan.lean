module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedStage
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFiberBank
public import IntegerMultBounds.MathlibTM2.Host.BinArithMul
public import IntegerMultBounds.MathlibTM2.Host.EmitRun
public import IntegerMultBounds.MathlibTM2.M6.BitCopyRecordSetup

/-! Place the complete target scan on the restored stage owner and its accumulator. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)
open Certificates.PR589
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

noncomputable def scanInput {V : ℕ} (word : Fin V → ZMod 2) (H : ℕ) : Tapes 2 prime :=
  ⟨fun _ => 0, ![putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (word i)),
    putWord (fun _ => blank) 0 (List.replicate H (SparseRoleCircuit.encode 0))]⟩

private theorem scanInput_source {V H : ℕ} (word : Fin V → ZMod 2) (i : Fin V) :
    (scanInput word H).tape 0 ((scanInput word H).head 0+i.val) = SparseRoleCircuit.encode (word i) := by
  change putWord _ 0 _ (0+i.val) = _
  rw [BinaryDivide.putWord_getElem _ _ _ _ (by simpa only [List.length_ofFn] using i.isLt)]
  simp

private theorem scanInput_zero {V H : ℕ} (word : Fin V → ZMod 2) (i : Fin H) :
    (scanInput word H).tape 1 ((scanInput word H).head 1+i.val) = SparseRoleCircuit.encode 0 := by
  change putWord _ 0 _ (0+i.val) = _
  rw [BinaryDivide.putWord_getElem _ _ _ _ (by simpa only [List.length_replicate] using i.isLt)]
  simp

noncomputable def scanFrame (K N D : ℕ) (v : Tapes 2 prime) :=
  CountedLoopReuseAlphabet.bank (LabelRowXor.bank v (FlatCoordinateSchedule.bits K) (FlatCoordinateSchedule.bits N))
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary (FlatCoordinateSchedule.bits D)) 1 1

/-- Repeat a width-sized rewind for every block, using the same two counters
that bounded the forward scan. -/
def returnAccumulator (a : ℕ) :=
  CountedLoopReuseAlphabet.program (extend (RoleArrayStackMoves.moveProgram (a := a) LabelRowXor.rewind) 2)

private theorem returnAccumulator_hoare (K N D : ℕ) (hk : 0 < K) (hn : 0 < N) (hd : 0 < D)
    (v : Tapes 2 prime) :
    HoareTime (returnAccumulator prime) (· = scanFrame K N D v)
      (· = scanFrame K N D (RoleArrayStackMoves.shifted v LabelRowXor.rewind (D*K))) (99*(D*(N*K))) := by
  let bits := FlatCoordinateSchedule.bits
  let state := fun i => RoleArrayStackMoves.shifted v LabelRowXor.rewind (i*K)
  let row := extend (RoleArrayStackMoves.moveProgram (a := prime) LabelRowXor.rewind) 2
  have run := CountedLoopReuseAlphabet.loop_hoare row (bits D) D
    (fun i => LabelRowXor.bank (state i) (bits K) (bits N)) (fun _ => 7*K+7*(bits K).length+16)
    (FlatCoordinateSchedule.bits_value _) (by
      intro i _
      have next : RoleArrayStackMoves.shifted (state i) LabelRowXor.rewind K = state (i+1) := by
        apply congrArg₂ Tapes.mk
        · funext j; simp only [state,RoleArrayStackMoves.shifted,Nat.cast_mul,Nat.cast_add,Nat.cast_one]; ring
        · rfl
      have move := hoare_extend_eq (RoleArrayStackMoves.move_hoare (state i) LabelRowXor.rewind (bits K) K
        (FlatCoordinateSchedule.bits_value _))
        (CountedLoopReuseAlphabet.controls CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary (bits N)) 1 1)
      rw [next] at move
      exact move)
  have start : state 0 = v := by
    cases v
    simp [state,RoleArrayStackMoves.shifted]
  rw [start] at run
  apply run.consequence (fun _ h => h) (fun _ h => h)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]
  have width := FlatCoordinateDimensions.bits_length_le_twice (le_refl K) hk
  have count := FlatCoordinateDimensions.bits_length_le_twice (le_refl D) hd
  have d := Nat.le_mul_of_pos_right D hk
  have vol := Nat.mul_le_mul_left D (Nat.le_mul_of_pos_left K hn)
  have bound := Nat.mul_le_mul_left D width
  dsimp only [bits]
  nlinarith only [bound,count,d,vol,hd]

/-- The accumulator is followed by the reusable width, row and block counters.
Each counter pair starts just to the right of its separator. -/
noncomputable def scanPrivateWords (K N D : ℕ) : Fin 7 → List (Fin (prime+4)) :=
  let bits := fun n => (FlatCoordinateSchedule.bits n).map (bitSymbol (a := prime))
  ![List.replicate (D*K) (SparseRoleCircuit.encode 0),[],bits K,[],bits N,[],bits D]

/-- Right stacks holding width, row count and block count in the nested scan. -/
def scanDimensionTargets : Fin 3 ↪ Fin 8 := ⟨![3,5,7], by decide⟩

theorem scanDimensions_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 8 ↪ Fin T) (src : Fin 3 → Fin T) (apart : ∀ i j, src i ≠ bank j)
    (dims : Fin 3 → ℕ) (v : HS T Q prime U) (S : Stacks T prime)
    (words : ∀ i z, readAt blank (S.L (src i)) (S.R (src i)) (z-1) =
      RadixZeroFill.encodedBinary (FlatCoordinateSchedule.bits (dims i)) z)
    (free : S.L (bank 2) = [] ∧ S.R (bank 2) = [])
    (empty : ∀ i, S.R (bank (scanDimensionTargets i)) = []) :
    let dst := scanDimensionTargets.trans bank
    let markers := ([2,3,4,5,6,7] : List (Fin 8)).map bank
    ∃ u F, u.user = v.user ∧ Exec body
      (.seq (loadDimensions src dst (bank 2) (List.finRange 3)) (.act (Cover.Fallback.pushMarkers markers)))
      (mk v S) (((List.finRange 3).map (fun i => 8*(FlatCoordinateSchedule.bits (dims i)).length+8)).sum+2)
      (mk u F) ∧ (∀ j, F.L j = if j ∈ markers then separator :: S.L j else S.L j) ∧
      (∀ i, F.R (dst i) = (FlatCoordinateSchedule.bits (dims i)).map bitSymbol) ∧
      ∀ j, (∀ i, dst i ≠ j) → F.R j = S.R j := by
  intro dst markers
  have ports (i : Fin 3) : [src i,bank 2,dst i].Nodup := by
    have nd := ((by decide : ∀ i, [2,scanDimensionTargets i].Nodup) i).map bank.injective
    exact List.nodup_cons.mpr ⟨by simp [dst,apart],nd⟩
  obtain ⟨u,F,user,run,left,loaded,off⟩ := loadDimensions_exec body src dst (bank 2)
    (fun i => FlatCoordinateSchedule.bits (dims i)) (fun i j => apart i _) ports _
    (List.nodup_finRange 3) v S words free (fun i _ => empty i)
  have unique : markers.Nodup :=
    (by decide : ([2,3,4,5,6,7] : List (Fin 8)).Nodup).map bank.injective
  have mark := Exec.act (body := body) (Cover.Fallback.pushMarkers markers) (mk u F)
  rw [Cover.Fallback.pushMarkers_run _ unique] at mark
  have execute := Exec.seq run mark
  exact ⟨u,{F with L := fun i => if i ∈ markers then separator :: F.L i else F.L i},user,by simpa only [Nat.add_assoc] using execute,fun j => by simp [left],
    fun i => loaded i (List.mem_finRange i),fun j h => off j (fun i _ => h i)⟩

private theorem scanPrivate_ready {V T : ℕ} (K N D : ℕ) (word : Fin V → ZMod 2)
    (bank : Fin 8 ↪ Fin T) (S : Stacks T prime)
    (stored : ∀ j : Fin 7, S.L (bank j.succ) = (if j = 0 then [] else [separator]) ∧
      S.R (bank j.succ) = scanPrivateWords K N D j) :
    let ready := scanFrame K N D (scanInput word (D*K))
    ∀ i : Fin 8, i ≠ 0 → ∀ z, ready.tape i z = readAt blank (S.L (bank i)) (S.R (bank i)) (z-ready.head i) := by
  intro ready i
  refine Fin.cases (fun h => False.elim (h rfl)) (fun j _ z => ?_) i
  rw [(stored j).1,(stored j).2]
  have counter (bs : List Bool) : CountedLoopReuseAlphabet.binary bs z =
      readAt (blank : Fin (prime+4)) [separator] (bs.map bitSymbol) (z-1) := by
    rw [← CountedLoopReuseAlphabet.encoding_binary]
    change RadixZeroFill.encodedBinary _ z = _
    rw [encodedBinary_eq,readAt_single]
  fin_cases j
  · change putWord (fun _ => blank) 0 _ z = readAt blank [] _ (z-0)
    rw [sub_zero,readAt_nil_left,putWord_blank_zero]
    rfl
  all_goals first | exact counter [] | exact counter _

/-- The three unused clock stacks and a shared temporary suffice to fill
the accumulator from its retained binary length. Only the accumulator changes. -/
theorem scanAccumulator_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin 8 ↪ Fin T) (length tmp : Fin T) (apart : ∀ i, length ≠ bank i ∧ tmp ≠ bank i)
    (distinct : length ≠ tmp) (H bits : ℕ) (fits : H < 2^bits) (u : HS T Q prime U) (S : Stacks T prime)
    (size : S.R length = binSyms bits H) (free : S.R tmp = [])
    (clocks : ∀ i ∈ ([2,4,6] : List (Fin 8)), S.R (bank i) = []) :
    ∃ z steps, z.user = u.user ∧ steps ≤ 8*H+11*bits+8 ∧
      Exec body (emitRun length (bank 2) (bank 1) (bank 4) (bank 6) tmp (SparseRoleCircuit.encode 0))
        (mk u S) steps (mk z {S with R := Function.update S.R (bank 1) (List.replicate H (SparseRoleCircuit.encode 0)++S.R (bank 1))}) := by
  have nd : [length,bank 2,bank 1,bank 4,bank 6,tmp].Nodup := by
    have inner := ((by decide : ([2,1,4,6] : List (Fin 8)).Nodup).map bank.injective)
    simp only [List.map_cons,List.map_nil,List.nodup_cons,List.mem_cons,List.mem_singleton,
      List.not_mem_nil,not_false_eq_true,not_or,List.nodup_nil,and_true] at inner ⊢
    simp_all [Ne.symm (apart _).2,(apart _).1]
  apply emitRun_exec nd bits H fits _ u S size
  intro k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact clocks 2 (by decide)
  · exact clocks 4 (by decide)
  · exact clocks 6 (by decide)
  · exact free

/-- Read a target sum in the physical order of the unlabelled accumulator. -/
noncomputable def stageTargetWord (n : Fin 9) (k : (Fin 32 × Fin 5) × Fin 111) (w B K : ℕ)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*K)) → ZMod 2)
    (i : Fin ((prime^w)^16*(B*K))) : ZMod 2 :=
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n k.1.1 k.1.2,ownerTape_injective ..⟩
  let pair : Fin ((prime^w)^16) × Fin (B*K) := finProdFinEquiv.symm i
  let initial := fun j => (selectedFrame w (Frames.initialRefs j)).symm (phaseRead owner x pair.2 j)
  let dst := 111+k.2.val
  selectedFrame w (Frames.finalRefs dst) (initial dst + initial k.2.val) (copyActive.symm pair.1)

private theorem readStageTargetWord (n : Fin 9) (k : (Fin 32 × Fin 5) × Fin 111) (w B K : ℕ) (x)
    (L R : List (Fin (prime+4))) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n k.1.1 k.1.2,ownerTape_injective ..⟩
    (∀ (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (b : Fin B) (j : Fin K),
      let initial := fun i => (selectedFrame w (Frames.initialRefs i)).symm
        (phaseRead owner x (finProdFinEquiv (b,j)) i)
      let dst := 111+k.2.val
      readAt blank L R ((FlatCoordinateLayout.index (AffineFieldCoordinates.embed s)
        (finProdFinEquiv (b,j))).val : ℤ) = SparseRoleCircuit.encode
        (selectedFrame w (Frames.finalRefs dst) (initial dst + initial k.2.val) s)) →
    ∀ i, readAt blank L R (i.val : ℤ) = SparseRoleCircuit.encode (stageTargetWord n k w B K x i) := by
  intro owner read i
  obtain ⟨⟨a,t⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨s,rfl⟩ := copyActive.surjective a
  obtain ⟨⟨b,j⟩,rfl⟩ := finProdFinEquiv.surjective t
  have h := read s b j
  rw [show FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) (finProdFinEquiv (b,j)) = finProdFinEquiv (copyActive s,finProdFinEquiv (b,j)) from rfl] at h
  simpa only [stageTargetWord,owner,Equiv.symm_apply_apply] using h

/-- Specify both the indexed word and the blank exterior at head zero. -/
def WordAtZero {V : ℕ} (word : Fin V → ZMod 2) (L R : List (Fin (prime+4))) : Prop :=
  ∀ z, readAt blank L R z = putWord (fun _ => blank) 0
    (List.ofFn fun i => SparseRoleCircuit.encode (word i)) z

private theorem wordAtZero_of_reads {V : ℕ} (word : Fin V → ZMod 2) (L R : List (Fin (prime+4)))
    (inside : ∀ i, readAt blank L R (i.val : ℤ) = SparseRoleCircuit.encode (word i))
    (outside : ∀ z, z < 0 ∨ (V : ℤ) ≤ z → readAt blank L R z = blank) : WordAtZero word L R := by
  intro z
  by_cases h : 0 ≤ z ∧ z < V
  · let i : Fin V := ⟨z.toNat,by omega⟩
    have pos : (i.val : ℤ) = z := by dsimp [i]; omega
    rw [← pos]
    have cell := BinaryDivide.putWord_getElem (a := prime) (fun _ => blank) 0
      (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (word i)) i.val (by simpa using i.isLt)
    simpa using (inside i).trans (by simpa using cell.symm)
  · have off : z < 0 ∨ (V : ℤ) ≤ z := by omega
    rw [putWord_outside _ _ _ _ (by simpa using off),outside z off]

theorem restoredTarget_host (n : Fin 9) (run : Fin 32 × Fin 5) (t : Fin 111) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n run.1 run.2,ownerTape_injective ..⟩
    let dst : Fin 661 := ⟨111+t.val,by omega⟩
    ∃ states : ℕ, ∀ {T Q : ℕ} {P U : Type} (fan : Fin (142081+2) ↪ Fin T) (bank : Fin 8 ↪ Fin T),
    bank 0 = fan ((owner dst).castAdd 2) → states ≤ Q → ∀ body : P → Pr P T Q prime U,
    ∃ code, ∀ (w B W : ℕ) (label : Cover.LabelPadding.Label 64 w) (x y out),
    let K := (prime^w)^112*W
    let N := prime^(64*(w*64))
    let D := (prime^w)^16*B
    stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k w B W a b ∧ next b)
      (fun a => a = y) (singleLabelBank label x) →
    HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
    0 < K → 0 < B → ∀ u S, Cover.Fallback.RecordPayload (fan ((owner dst).castAdd 2)) (fun _ => blank) 0 (out (owner dst)) S →
    (∀ j : Fin 7, S.L (bank j.succ) = (if j = 0 then [] else [separator]) ∧
      S.R (bank j.succ) = scanPrivateWords K N D j) →
    ∃ z F steps, Exec body code (mk u S) steps (mk z F) ∧ steps ≤ 3900*(D*(N*K))+6 ∧ z.user = u.user ∧
      WordAtZero (stageTargetWord n (run,t) w B K x) (F.L (bank 1)) (F.R (bank 1)) ∧
      ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro owner dst
  let count := fun {q : ℕ} (_ : Program 8 q prime) => q
  refine ⟨count (seq (LabelRowXor.blocksProgram prime) (returnAccumulator prime)),?_⟩
  intro T Q P U fan bank selected fits body
  refine ⟨embProg bank (Empty.elim : Empty → P) (foreign (liftQ (seq (LabelRowXor.blocksProgram prime) (returnAccumulator prime)) fits)),?_⟩
  intro w B W label x y out K N D trace restored pos hb u S live stored
  let v := scanInput (out (owner dst)) (D*K)
  let ready := scanFrame K N D v
  have privateReady := scanPrivate_ready K N D (out (owner dst)) bank S stored
  obtain ⟨Y,scan,hs,hd,src,exterior,values⟩ := restoredStage_targetScan n run w B W label x y out trace restored t v pos hb
    (scanInput_source (H := D*K) (out (owner dst))) (scanInput_zero (out (owner dst)))
  have rep : RepT ready (embStk bank S).L (embStk bank S).R := by
    intro i z
    by_cases eqn : i = 0
    · subst i
      have h := live z
      rw [encodedOwnerCell] at h
      change putWord _ 0 _ z = readAt blank (S.L (bank 0)) (S.R (bank 0)) (z-0)
      rw [selected]
      exact h.symm
    · exact privateReady i eqn z
  have rows : 0 < N := pow_pos Shared50ModularControl.prime_prime.pos _
  have blocks : 0 < D := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hb
  have volume := Nat.mul_pos blocks (Nat.mul_pos rows pos)
  have both := scan.seq (returnAccumulator_hoare K N D pos rows blocks Y)
  have cost : 200*(D*(N*K))+1+99*(D*(N*K)) ≤ 300*(D*(N*K)) := by omega
  have linear := both.consequence (fun _ h => h) (fun _ h => h) cost
  obtain ⟨z,F,steps,exec,paid,user,done,off⟩ := placedHoare_exec _ bank fits body linear u S rep
  refine ⟨z,F,steps,exec,?_,user,?_,off⟩
  · exact paid.trans_eq (by ring)
  · have h0 : v.head 1 = 0 := rfl
    have cell (z : ℤ) : readAt blank (F.L (bank 1)) (F.R (bank 1)) z = Y.tape 1 z := by
      have h := done 1 z
      change Y.tape 1 z = readAt blank (F.L (bank 1)) (F.R (bank 1)) (z-(Y.head 1+(D*K : ℕ)*(-1))) at h
      rw [hd,h0] at h
      simpa [D,K,Nat.cast_mul] using h.symm
    apply wordAtZero_of_reads
    · apply readStageTargetWord
      intro s b j
      rw [cell]
      simpa only [h0,zero_add] using values s b j
    · intro z hz
      have outside : z < 0 ∨ (D*K : ℕ) ≤ z := by simpa [D,Nat.mul_assoc] using hz
      have ext : ¬(v.head 1 ≤ z ∧ z < v.head 1+(D : ℤ)*K) := by rw [h0]; push_cast at outside; omega
      rw [cell,exterior z ext]
      change putWord (fun _ => blank) 0 (List.replicate (D*K) (SparseRoleCircuit.encode 0)) z = _
      exact putWord_outside _ _ _ _ (by simpa using outside)

/-- The target stacks of distinct scheduled scans are disjoint. -/
noncomputable def targetOwner (n : Fin 9) (k : (Fin 32 × Fin 5) × Fin 111) : Fin 142081 :=
  ownerTape n k.1.1 k.1.2 ⟨111+k.2.val,by omega⟩

theorem targetOwner_injective (n : Fin 9) : Function.Injective (targetOwner n) := by
  rintro ⟨p,t⟩ ⟨q,u⟩ eqn
  have same : p = q := by
    by_contra other
    exact otherRunMissesPort n p q other _ ⟨111+u.val,by omega⟩ (by dsimp; omega) eqn
  subst q
  have val := congrArg Fin.val (ownerTape_injective n p.1 p.2 eqn)
  change 111+t.val = 111+u.val at val
  exact Prod.ext rfl (Fin.ext (Nat.add_left_cancel val))

/-- The restored label sum is the same ordinary target word returned by the host scan. -/
theorem restoredStage_targetWord (n : Fin 9) (k : (Fin 32 × Fin 5) × Fin 111) (w B W : ℕ)
    (label : Cover.LabelPadding.Label 64 w) (x y out)
    (trace : stageRuns.foldr (fun p next a => ∃ b, packedStageEffect n p w B W a b ∧ next b)
      (fun a => a = y) (singleLabelBank label x))
    (restore : HelperLabelTrace w (B*prime^(64*(w*64))) W (restoreSlotChanges (stageFinalSlot n)) y out) :
    let K := (prime^w)^112*W
    collapseLabelBank (B := B) (K := K) out (targetOwner n k) = stageTargetWord n k w B K x := by
  intro K
  funext i
  obtain ⟨⟨a,t⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨s,rfl⟩ := copyActive.surjective a
  obtain ⟨⟨b,j⟩,rfl⟩ := finProdFinEquiv.surjective t
  let z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B :=
    ⟨⟨0,pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _⟩,⟨0,Nat.zero_lt_one⟩,b,
      ⟨0,by simp [copyLabelLayout,ActualAffineScaling.modulus]⟩,⟨0,Nat.zero_lt_one⟩,
      ⟨0,by simp [copyLabelLayout,ActualAffineScaling.modulus]⟩,j⟩
  have sum := congrFun (restoredStage_active n k.1 w B W _ y out trace restore k.2 z).1 s
  rw [collapse_singleLabelBank] at sum
  have dst : 111+k.2.val < 661 := by omega
  simp only [phaseRead,Copy.extendStored,dite_eq_left dst] at sum
  have index (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (j : Fin (B*K)) :
      FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j = finProdFinEquiv (copyActive s,j) := rfl
  simpa only [stageTargetWord,Equiv.symm_apply_apply,phaseRead,Copy.extendStored,dite_eq_left dst,targetOwner,z,index,Function.Embedding.coeFn_mk] using sum

/-- Each target retains its original owner tape and has seven private tapes
indexed by that owner. Thus one scan can move both heads freely. -/
noncomputable def targetScanBank {T : ℕ} (fan : Fin (142081+2) ↪ Fin T) (t : Fin 142081) :
    Fin 8 ↪ Fin (T+142081*7) where
  toFun := Fin.cases ((fan (t.castAdd 2)).castAdd _) (fun j => (finProdFinEquiv (t,j)).natAdd T)
  inj' := by
    intro i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
    · exact fun _ => rfl
    · intro h
      have val := congrArg Fin.val h
      change (fan (t.castAdd 2)).val = T+_ at val
      omega
    · intro h
      have val := congrArg Fin.val h
      change T+_ = (fan (t.castAdd 2)).val at val
      omega
    · intro h
      have same := finProdFinEquiv.injective ((Fin.natAddEmb T).injective h)
      exact congrArg Fin.succ (congrArg Prod.snd same)

theorem targetScanBank_disjoint {T : ℕ} (fan : Fin (142081+2) ↪ Fin T) {t u : Fin 142081}
    (distinct : t ≠ u) (i j : Fin 8) : targetScanBank fan t i ≠ targetScanBank fan u j := by
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · exact fun h => distinct ((Fin.castAddEmb 2).injective (fan.injective ((Fin.castAddEmb _).injective h)))
  · intro h
    have val := congrArg Fin.val h
    change (fan (t.castAdd 2)).val = T+_ at val
    omega
  · intro h
    have val := congrArg Fin.val h
    change T+_ = (fan (u.castAdd 2)).val at val
    omega
  · exact fun h => distinct (congrArg Prod.fst (finProdFinEquiv.injective ((Fin.natAddEmb T).injective h)))

noncomputable def scanCounters {T Q : ℕ} {P U : Type} (bank : Fin 8 ↪ Fin T) (src : Fin 3 → Fin T) :
    Pr P T Q prime U :=
  .seq (loadDimensions src (scanDimensionTargets.trans bank) (bank 2) (List.finRange 3))
    (.act (Cover.Fallback.pushMarkers (([2,3,4,5,6,7] : List (Fin 8)).map bank)))

def scanCounterCost (dims : Fin 3 → ℕ) :=
  ((List.finRange 3).map (fun i => 8*(FlatCoordinateSchedule.bits (dims i)).length+8)).sum+2

private theorem scanCounters_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 8 ↪ Fin T) (src : Fin 3 → Fin T) (apart : ∀ i j, src i ≠ bank j)
    (K N D : ℕ) (v : HS T Q prime U) (S : Stacks T prime)
    (words : ∀ i z, readAt blank (S.L (src i)) (S.R (src i)) (z-1) =
      RadixZeroFill.encodedBinary (FlatCoordinateSchedule.bits (![K,N,D] i)) z)
    (empty : ∀ i : Fin 7, S.L (bank i.succ) = [] ∧ S.R (bank i.succ) = []) :
    ∃ u F, u.user = v.user ∧ Exec body (scanCounters bank src) (mk v S)
      (scanCounterCost ![K,N,D]) (mk u F) ∧
      (∀ j : Fin 7, F.L (bank j.succ) = (if j = 0 then [] else [separator]) ∧
        F.R (bank j.succ) = (if j = 0 then [] else scanPrivateWords K N D j)) ∧
      ∀ j, (∀ i : Fin 7, bank i.succ ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨u,F,user,run,left,loaded,off⟩ := scanDimensions_exec body bank src apart _ v S words
    (empty 1) (fun i => by fin_cases i <;> first | exact (empty 2).2 | exact (empty 4).2 | exact (empty 6).2)
  have outside (j) (h : ∀ i : Fin 7, bank i.succ ≠ j) : F.L j = S.L j ∧ F.R j = S.R j := by
    constructor
    · rw [left,if_neg]
      simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact And.intro (h 1).symm ⟨(h 2).symm,(h 3).symm,(h 4).symm,(h 5).symm,(h 6).symm⟩
    · apply off
      intro i
      fin_cases i <;> first | exact h 2 | exact h 4 | exact h 6
  refine ⟨u,F,user,run,?_,outside⟩
  intro j
  constructor
  · rw [left,(empty j).1]
    fin_cases j <;> simp
  · fin_cases j <;> first | exact loaded 0 | exact loaded 1 | exact loaded 2 |
      (rw [off _ (by intro i; apply bank.injective.ne; fin_cases i <;> decide)]
       first | exact (empty 0).2 | exact (empty 1).2 | exact (empty 3).2 | exact (empty 5).2)

def stageScanCost (targets K N D : ℕ) :=
  D.size*(12*(D.size+K.size)+20)+16*(D.size+K.size)+24 +
    (targets*(3900*(D*(N*K))+6+(8*(D*K)+11*(D.size+K.size)+8)+scanCounterCost ![K,N,D])+1) + (2*(D.size+K.size)+2)

/-- The shared binary product and the per-target counters fit the same linear
volume bound as the payload scans. -/
theorem stageScanCost_le (targets K N D : ℕ) (hk : 0 < K) (hn : 0 < N) (hd : 0 < D) :
    stageScanCost targets K N D ≤ (4300*targets+200)*(D*(N*K)) := by
  let V := D*(N*K)
  have d : D ≤ V := Nat.le_mul_of_pos_right _ (Nat.mul_pos hn hk)
  have nk : N*K ≤ V := Nat.le_mul_of_pos_left _ hd
  have k : K ≤ V := (Nat.le_mul_of_pos_left _ hn).trans nk
  have n : N ≤ V := (Nat.le_mul_of_pos_right _ hk).trans nk
  have dk : D*K ≤ V := Nat.mul_le_mul_left D (Nat.le_mul_of_pos_left _ hn)
  have pos := hd.trans_le d
  have size (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self
  have cross := (Nat.mul_le_mul (size D) (size K)).trans dk
  have sq : D.size*D.size ≤ 4*V := by
    simpa only [pow_two] using (Cover.Fallback.size_square_le D hd).trans (Nat.mul_le_mul_left 4 d)
  have headers : scanCounterCost ![K,N,D] ≤ 74*V := by
    change (8*(FlatCoordinateSchedule.bits K).length+8)+
      ((8*(FlatCoordinateSchedule.bits N).length+8)+((8*(FlatCoordinateSchedule.bits D).length+8)+0))+2 ≤ _
    have := FlatCoordinateDimensions.bits_length_le_twice k pos
    have := FlatCoordinateDimensions.bits_length_le_twice n pos
    have := FlatCoordinateDimensions.bits_length_le_twice d pos
    omega
  have ds := (size D).trans d
  have ks := (size K).trans k
  have each : 3900*V+6+(8*(D*K)+11*(D.size+K.size)+8)+scanCounterCost ![K,N,D] ≤ 4300*V := by omega
  have shared : D.size*(12*(D.size+K.size)+20)+16*(D.size+K.size)+24+1+(2*(D.size+K.size)+2) ≤ 200*V := by
    nlinarith only [sq,cross,ds,ks,pos]
  have all := Nat.mul_le_mul_left targets each
  change _ ≤ (4300*targets+200)*V
  unfold stageScanCost
  change _ + (targets*(3900*V+6+(8*(D*K)+11*(D.size+K.size)+8)+scanCounterCost ![K,N,D])+1) + _ ≤ _
  rw [Nat.add_mul]
  rw [show targets*(4300*V) = 4300*targets*V by ring] at all
  omega

/-- Scan the restored targets in stage order. Each accumulator retains its
output while all subsequent scans execute on disjoint banks. -/
theorem stageTargets_host (n : Fin 9) :
    let I := (Fin 32 × Fin 5) × Fin 111
    let order := stageRuns.product (List.finRange 111)
    ∃ states : ℕ, ∀ {T Q : ℕ} {P U : Type} (fan : Fin (142081+2) ↪ Fin T), states ≤ Q →
    let full := fan.trans (Fin.castAddEmb (142081*7))
    let bank := fun k : I => targetScanBank fan (targetOwner n k)
    ∀ length tmp, length ≠ tmp → (∀ k i, length ≠ bank k i ∧ tmp ≠ bank k i) →
    ∀ (src : Fin 3 → Fin (T+142081*7)), (∀ k i j, src i ≠ bank k j) →
    ∀ (scratch : Fin 5 → Fin (T+142081*7)),
    [src 2,src 0,length,scratch 0,scratch 1,scratch 2,scratch 3,scratch 4].Nodup →
    (∀ i, src i ≠ length) →
    ∀ body : P → Pr P (T+142081*7) Q prime U, ∃ code,
    ∀ (w B W : ℕ) (label : Cover.LabelPadding.Label 64 w) (x y out),
    let K := (prime^w)^112*W
    let N := prime^(64*(w*64))
    let D := (prime^w)^16*B
    stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k w B W a b ∧ next b)
      (fun a => a = y) (singleLabelBank label x) →
    HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
    0 < K → 0 < B → ∀ u S, HelperFan full out S →
    S.R (src 2) = binSyms D.size D → S.R (src 0) = binSyms K.size K →
    S.R length = [] → (∀ i, S.R (scratch i) = []) → S.R tmp = [] →
    (∀ i z, readAt blank (S.L (src i)) (S.R (src i)) (z-1) =
      RadixZeroFill.encodedBinary (FlatCoordinateSchedule.bits (![K,N,D] i)) z) →
    (∀ k (j : Fin 7), S.L (bank k j.succ) = [] ∧ S.R (bank k j.succ) = []) →
    let result := fun k => WordAtZero (stageTargetWord n k w B K x)
    ∃ z F steps, Exec body code (mk u S) steps (mk z F) ∧ steps ≤ stageScanCost order.length K N D ∧
      z.user = u.user ∧ (∀ k, result k (F.L (bank k 1)) (F.R (bank k 1))) ∧
      ∀ j, (∀ k i, bank k i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  classical
  intro I order
  choose req scan using fun k : I => restoredTarget_host n k.1 k.2
  refine ⟨Finset.univ.sup req,?_⟩
  intro T Q P U fan fits full bank length tmp distinct apart src srcApart scratch regs srcOff body
  choose code execute using fun k => scan k full (bank k) rfl ((Finset.le_sup (Finset.mem_univ k)).trans fits) body
  let placed := fun k => Prog.seq (scanCounters (bank k) src) (Prog.seq (emitRun length (bank k 2) (bank k 1) (bank k 4) (bank k 6) tmp
    (SparseRoleCircuit.encode 0)) (code k))
  let product : Pr P (T+142081*7) Q prime U := bmul (src 2) (src 0) length (scratch 0) (scratch 1) (scratch 2) (scratch 3) (scratch 4) (src 2)
  refine ⟨Prog.seq product (.seq (Prog.seqList (order.map placed)) (bclear length)),?_⟩
  intro w B W label x y out K N D trace restored pos hb u S live blockWord widthWord fresh work free words empty result
  let price := 3900*(D*(N*K))+6+(8*(D*K)+11*(D.size+K.size)+8)+scanCounterCost ![K,N,D]
  have run (ks : List I) (unique : ks.Nodup) (v : HS _ Q prime U) (A : Stacks _ prime)
      (sizeA : A.R length = binSyms (D.size+K.size) (D*K)) (freeA : A.R tmp = [])
      (headers : ∀ i z, readAt blank (A.L (src i)) (A.R (src i)) (z-1) =
        RadixZeroFill.encodedBinary (FlatCoordinateSchedule.bits (![K,N,D] i)) z)
      (ready : ∀ k ∈ ks, ∀ i, A.L (bank k i) = S.L (bank k i) ∧ A.R (bank k i) = S.R (bank k i)) :
      ∃ z F steps, Exec body (Prog.seqList (ks.map placed)) (mk v A) steps (mk z F) ∧
        steps ≤ ks.length*price+1 ∧ z.user = v.user ∧
        (∀ k ∈ ks, result k (F.L (bank k 1)) (F.R (bank k 1))) ∧
        ∀ j, (∀ k ∈ ks, ∀ i, bank k i ≠ j) → F.L j = A.L j ∧ F.R j = A.R j := by
    induction ks generalizing v A with
    | nil => exact ⟨v,A,1,Exec.act .done _,by simp,rfl,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
    | cons k ks ih =>
      obtain ⟨fresh,nd⟩ := List.nodup_cons.mp unique
      have input := fanPayload live (targetOwner n k)
      obtain ⟨v₀,C,user₀,setup,stored,keepC⟩ := scanCounters_exec body (bank k) src (srcApart k)
        K N D v A headers (fun i => by
          obtain ⟨hl,hr⟩ := ready k List.mem_cons_self i.succ
          rw [hl,hr]
          exact empty k i)
      have right (i : Fin 7) := (stored i).2
      obtain ⟨u₁,e,ue,fillBill,fill⟩ := scanAccumulator_exec body (bank k) length tmp (apart k) distinct
        (D*K) (D.size+K.size) (by rw [pow_add]; exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self _) (Nat.le_of_lt (Nat.lt_size_self _)) (by positivity)) v₀ C
        ((keepC _ (fun i => (apart k i.succ).1.symm)).2.trans sizeA)
        ((keepC _ (fun i => (apart k i.succ).2.symm)).2.trans freeA) (by
          intro i hi
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl
          · exact right 1
          · exact right 3
          · exact right 5)
      let G : Stacks _ prime := {C with R := Function.update C.R (bank k 1) (List.replicate (D*K) (SparseRoleCircuit.encode 0)++C.R (bank k 1))}
      have kept (j) (ne : j ≠ bank k 1) : G.R j = C.R j := Function.update_of_ne ne _ _
      obtain ⟨v',A',m,scan,paid,user,done,offG⟩ := execute k w B W label x y out trace restored pos hb u₁ G (by
        intro j
        change readAt blank (C.L (bank k 0)) (G.R (bank k 0)) _ = _
        rw [kept _ ((bank k).injective.ne (by decide))]
        have payload := keepC (bank k 0) (fun i => (bank k).injective.ne (Fin.succ_ne_zero i))
        rw [payload.1,payload.2,(ready k List.mem_cons_self 0).1,(ready k List.mem_cons_self 0).2]
        exact input j) (fun j => by
          refine ⟨(stored j).1,?_⟩
          by_cases h : j = 0
          · subst j
            change Function.update _ (bank k 1) _ (bank k 1) = _
            rw [Function.update_self,show C.R (bank k 1) = [] from right 0,List.append_nil]
            rfl
          · rw [kept _ ((bank k).injective.ne (by intro eq; exact h (Fin.succ_injective _ eq)))]
            simpa [h] using right j)
      have first := Exec.seq setup (Exec.seq fill scan)
      have off (j) (outside : ∀ i, bank k i ≠ j) :=
        And.intro ((offG j outside).1.trans (keepC j (fun i => outside i.succ)).1)
          (((offG j outside).2.trans (kept j (outside 1).symm)).trans (keepC j (fun i => outside i.succ)).2)
      have disjoint (h) (mem : h ∈ ks) := targetScanBank_disjoint fan
        ((targetOwner_injective n).ne (fun eqn : k = h => fresh (eqn ▸ mem)))
      obtain ⟨z,F,t,rest,bill,same,outputs,keep⟩ := ih nd v' A'
        ((off length (fun i => (apart k i).1.symm)).2.trans sizeA)
        ((off tmp (fun i => (apart k i).2.symm)).2.trans freeA) (fun i z => by
          obtain ⟨hl,hr⟩ := off _ (fun j => (srcApart k i j).symm)
          rw [hl,hr,headers]) (fun h mem i => by
        obtain ⟨hl,hr⟩ := off _ (fun a => disjoint h mem a i)
        have old := ready h (List.mem_cons_of_mem _ mem) i
        exact ⟨hl.trans old.1,hr.trans old.2⟩)
      refine ⟨z,F,(scanCounterCost ![K,N,D]+(e+m))+t,Exec.seq first rest,?_,same.trans (user.trans (ue.trans user₀)),?_,?_⟩
      · have cost : scanCounterCost ![K,N,D]+(e+m) ≤ price := by
          rw [Nat.add_comm (scanCounterCost _) _,Nat.add_comm e m]
          exact Nat.add_le_add_right (Nat.add_le_add paid fillBill) _
        simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
      · intro h mem
        rcases List.mem_cons.mp mem with rfl | tail
        · obtain ⟨hl,hr⟩ := keep _ (fun a ha i => (disjoint a ha 1 i).symm)
          rw [hl,hr]
          exact done
        · exact outputs h tail
      · intro j hj
        have tail := keep j (fun h mem => hj h (List.mem_cons_of_mem _ mem))
        have head := off j (hj k List.mem_cons_self)
        exact ⟨tail.1.trans head.1,tail.2.trans head.2⟩
  have carry : src 2 ≠ scratch 0 := fun eq => (List.nodup_cons.mp regs).1 (by simp [eq])
  obtain ⟨v,m,userMul,mulBill,mul⟩ := bmul_exec (body := body) regs (srcOff 2) carry
    (Nat.lt_size_self D) (Nat.lt_size_self K) u S blockWord widthWord fresh
    (work 0) (work 1) (work 2) (work 3) (work 4)
  let A : Stacks _ prime := {S with R := Function.update S.R length (binSyms (D.size+K.size) (D*K))}
  have unchanged (j) (h : j ≠ length) : A.R j = S.R j := Function.update_of_ne h _ _
  obtain ⟨z,F,t,exec,paid,user,done,off⟩ := run order (stageRuns_nodup.product (List.nodup_finRange _))
    v A (by simp [A]) ((unchanged tmp distinct.symm).trans free)
    (fun i z => by change readAt blank (S.L _) (A.R _) _ = _; rw [unchanged _ (srcOff i),words])
    (fun k _ i => ⟨rfl,unchanged _ (apart k i).1.symm⟩)
  have retained := (off length (fun k _ i => (apart k i).1.symm)).2
  have width : (F.R length).length = D.size+K.size := by rw [retained]; simp [A,length_binSyms]
  obtain ⟨z',userClear,_,clear⟩ := bclear_exec body length z F
  rw [width] at clear
  refine ⟨z',_,_,Exec.seq mul (Exec.seq exec clear),?_,userClear.trans (user.trans userMul),?_,?_⟩
  · dsimp only [stageScanCost]
    dsimp only [price] at paid
    omega
  · intro k
    change result k (F.L (bank k 1)) (Function.update F.R length [] (bank k 1))
    rw [show (Function.update F.R length [] (bank k 1)) = F.R (bank k 1) from Function.update_of_ne (apart k 1).1.symm _ _]
    exact done k (List.mem_flatMap.mpr ⟨k.1,mem_stageRuns _,
      List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩)
  · intro j outside
    obtain ⟨left,right⟩ := off j (fun h _ => outside h)
    refine ⟨left,?_⟩
    by_cases h : j = length
    · subst j; simpa using fresh.symm
    · exact (Function.update_of_ne h _ _).trans (right.trans (unchanged j h))


/-- Owners outside the target set still hold their restored word at head zero. -/
def RestoredOwnerPayloads {T V : ℕ} (n : Fin 9) (fan : Fin (142081+2) ↪ Fin T)
    (out : Fin 142081 → Fin V → ZMod 2) (F : Stacks T prime) : Prop :=
  ∀ t, (∀ k, targetOwner n k ≠ t) →
    Cover.Fallback.RecordPayload (fan (t.castAdd 2)) (fun _ => blank) 0 (out t) F

theorem RestoredOwnerPayloads.source {T V : ℕ} {n : Fin 9} {fan : Fin (142081+2) ↪ Fin T}
    {out : Fin 142081 → Fin V → ZMod 2} {F : Stacks T prime} (live : RestoredOwnerPayloads n fan out F)
    (run : Fin 32 × Fin 5) (s : Fin 111) :
    let src := ownerTape n run.1 run.2 (s.castLE (by decide))
    Cover.Fallback.RecordPayload (fan (src.castAdd 2)) (fun _ => blank) 0 (out src) F := by
  intro src
  apply live
  rintro ⟨p,t⟩
  by_cases same : p = run
  · subst p
    apply (ownerTape_injective n run.1 run.2).ne
    intro eq
    have h := congrArg Fin.val eq
    change 111+t.val = s.val at h
    omega
  · exact otherRunMissesPort n p run same _ _ (by change s.val < 222; omega)

theorem RestoredOwnerPayloads.inactive {T V : ℕ} {n : Fin 9} {fan : Fin (142081+2) ↪ Fin T}
    {out : Fin 142081 → Fin V → ZMod 2} {F : Stacks T prime} (live : RestoredOwnerPayloads n fan out F)
    (ρ : Role) (off : ρ.bank.val / 2 ≠ BitHosting.activePair n.val) :
    let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
    Cover.Fallback.RecordPayload (fan (tape.castAdd 2)) (fun _ => blank) 0 (out tape) F := by
  intro tape
  apply live
  rintro ⟨p,t⟩ eq
  have same := (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ eq))
  apply off
  change owner n p.1 p.2 (111+t.val) = ρ at same
  rw [← same]
  simp only [owner,show 111+t.val < 222 by omega,ite_true]
  apply side_pair
  unfold regSide
  split <;> omega

/-- Run the packed stage on its original tapes, then scan the restored owners.
The additional shared tapes hold the three dimensions and arithmetic workspace. -/
theorem packedStageTargets_host (n : Fin 9) :
    let I := (Fin 32 × Fin 5) × Fin 111
    let order := stageRuns.product (List.finRange 111)
    ∃ states : ℕ, ∀ {T Q : ℕ} {P U : Type} (fan : Fin (142081+2) ↪ Fin T), states ≤ Q →
    let inner := (Fin.castAddEmb 14 (n := T)).trans (Fin.castAddEmb (142081*7))
    let placedFan := fan.trans (Fin.castAddEmb 14)
    let bank := fun k : I => targetScanBank placedFan (targetOwner n k)
    let reg := (Fin.castAddEmb 4 (n := 10)).trans ((Fin.natAddEmb T (m := 14)).trans (Fin.castAddEmb (142081*7)))
    ∀ (body : P → Pr P T Q prime U) (stage : Pr P T Q prime U), ∃ code,
    ∀ (w B W : ℕ) (label : Cover.LabelPadding.Label 64 w) (x),
    let K := (prime^w)^112*W
    let N := prime^(64*(w*64))
    let D := (prime^w)^16*B
    0 < K → 0 < B → ∀ u S v A time y out,
    Exec body stage (mk (embDn inner u) (embStk inner S)) time (mk v A) →
    v.user = u.user → HelperFan fan out A →
    stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k w B W a b ∧ next b)
      (fun a => a = y) (singleLabelBank label x) →
    HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
    (∀ i : Fin 3, S.L (reg (i.castAdd 7)) = [separator] ∧
      S.R (reg (i.castAdd 7)) = binSyms (![K,N,D] i).size (![K,N,D] i)) →
    (∀ i : Fin 7, S.R (reg (i.natAdd 3)) = []) →
    (∀ k (j : Fin 7), S.L (bank k j.succ) = [] ∧ S.R (bank k j.succ) = []) →
    let result := fun k => WordAtZero (stageTargetWord n k w B K x)
    ∃ z F steps, Exec (fun g => embProg inner id (body g)) code (mk u S) steps (mk z F) ∧
      steps ≤ time + (4300*order.length+200)*(D*(N*K)) ∧ z.user = u.user ∧
      (∀ k, result k (F.L (bank k 1)) (F.R (bank k 1))) ∧
      RestoredOwnerPayloads n (fan.trans inner) out F := by
  intro I order
  obtain ⟨states,chooseScan⟩ := stageTargets_host n
  refine ⟨states,?_⟩
  intro T Q P U fan fits inner placedFan bank reg body stage
  let outer := fun g => embProg inner id (body g)
  let src := fun i : Fin 3 => reg (i.castAdd 7)
  let scratch := fun i : Fin 5 => reg (i.natAdd 5)
  have regOutside (i : Fin 10) (j : Fin T) : inner j ≠ reg i := by
    intro eq
    have h := congrArg Fin.val eq
    change j.val = T+i.val at h
    omega
  have away (i : Fin 10) (k : I) (j : Fin 8) : reg i ≠ bank k j := by
    refine Fin.cases ?_ (fun b => ?_) j
    · exact (regOutside i _).symm
    · intro eq
      have h := congrArg Fin.val eq
      change T+i.val = T+14+_ at h
      omega
  have regs : [src 2,src 0,reg 3,scratch 0,scratch 1,scratch 2,scratch 3,scratch 4].Nodup :=
    ((by decide : ([2,0,3,5,6,7,8,9] : List (Fin 10)).Nodup).map reg.injective)
  obtain ⟨scan,run⟩ := chooseScan placedFan fits (reg 3) (reg 4) (reg.injective.ne (by decide))
    (fun k i => ⟨away 3 k i,away 4 k i⟩) src (fun k i => away _ k) scratch regs
    (fun i => reg.injective.ne (by fin_cases i <;> decide)) outer
  refine ⟨.seq (embProg inner id stage) scan,?_⟩
  intro w B W label x K N D pos hb u S v A time y out exec user live trace restore words free empty result
  obtain ⟨v',A',placed,_,same,view,off⟩ := exec_emb (ι := id) (body' := outer) inner.injective
    (fun _ => rfl) exec u rfl S rfl
  have keep (i) := off _ (regOutside i)
  have live' : HelperFan (placedFan.trans (Fin.castAddEmb (142081*7))) out A' := by
    rw [← view] at live
    exact live
  have headers (i : Fin 3) := (keep (i.castAdd 7)).2.trans (words i).2
  obtain ⟨z,F,t,scanned,paid,saved,done,untouched⟩ := run w B W label x y out trace restore pos hb v' A'
    live' (headers 2) (headers 0) ((keep 3).2.trans (free 0))
    (fun i => (keep _).2.trans (by fin_cases i <;> first | exact free 2 | exact free 3 | exact free 4 | exact free 5 | exact free 6)) ((keep 4).2.trans (free 1))
    (fun i z => by
      change readAt blank (A'.L (reg _)) (A'.R (reg _)) _ = _
      rw [(keep _).1,(words i).1,headers i,← Cover.Fallback.canonicalBits_symbols,encodedBinary_eq,readAt_single])
    (fun k j => by
      have untouched := off (bank k j.succ) (fun a eq => by
        have h := congrArg Fin.val eq
        change a.val = T+14+_ at h
        omega)
      exact ⟨untouched.1.trans (empty k j).1,untouched.2.trans (empty k j).2⟩)
  have blocks : 0 < D := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hb
  have linear := stageScanCost_le order.length K N D pos (pow_pos Shared50ModularControl.prime_prime.pos _) blocks
  refine ⟨z,F,_,Exec.seq placed scanned,Nat.add_le_add_left (paid.trans linear) time,
    saved.trans (same.trans user),done,?_⟩
  intro owner other z
  let port := inner (fan (owner.castAdd 2))
  have outside (k : I) (i : Fin 8) : bank k i ≠ port := by
    refine Fin.cases ?_ (fun j eq => ?_) i
    · exact inner.injective.ne (fan.injective.ne ((Fin.castAddEmb 2).injective.ne (other k)))
    · have h := congrArg Fin.val eq
      change T+14+_ = (fan (owner.castAdd 2)).val at h
      omega
  obtain ⟨hl,hr⟩ := untouched port outside
  change readAt blank (F.L port) (F.R port) _ = _
  rw [hl,hr]
  exact fanPayload live' owner z

/-- The common counters and six scratch tapes for padding successive owners. -/
noncomputable def ownerPadFrame (D N K : ℕ) : Tapes 12 prime :=
  RowPaddingConstructedAlphabet.bank (fun _ => blank) (fun _ => blank) 0 0
    (FlatCoordinateSchedule.bits D) (FlatCoordinateSchedule.bits 1)
    (FlatCoordinateSchedule.bits N) (FlatCoordinateSchedule.bits K)

private theorem ownerPad_aux (src dst : ℤ → Fin (prime+4)) (D N K : ℕ)
    (j : Fin 12) (hs : j ≠ 0) (hd : j ≠ 1) :
    let v := RowPaddingConstructedAlphabet.bank src dst 0 0
      (FlatCoordinateSchedule.bits D) (FlatCoordinateSchedule.bits 1)
      (FlatCoordinateSchedule.bits N) (FlatCoordinateSchedule.bits K)
    v.tape j = (ownerPadFrame D N K).tape j ∧ v.head j = (ownerPadFrame D N K).head j := by
  fin_cases j <;> first | contradiction | exact ⟨rfl,rfl⟩

/-- Run the same host code on each ordinary owner. Only the selected payload
ports change their represented words; the dimension counters are reusable. -/
theorem placedOwnerPad {w B K T Q : ℕ} {P U : Type} (hB : 0 < B) (hK : 0 < K)
    (fits : 215 ≤ Q) (body : P → Pr P T Q prime U) :
    let label := firstRowLabel w
    ∀ port : Fin 12 ↪ Fin T,
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    let frame := ownerPadFrame (A*B) N K
    let aux := fun (S : Stacks T prime) => ∀ j : Fin 12, j ≠ 0 → j ≠ 1 → ∀ z,
      frame.tape j z = readAt blank (S.L (port j)) (S.R (port j)) (z-frame.head j)
    let code := embProg port (Empty.elim : Empty → P) (foreign (liftQ RowPaddingConstructedAlphabet.program fits))
    ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) i u S,
      Cover.Fallback.RecordPayload (port 0) (fun _ => blank) 0 (x i) S →
      (∀ z, readAt blank (S.L (port 1)) (S.R (port 1)) z = blank) → aux S →
      ∃ z F steps, Exec body code (mk u S) steps (mk z F) ∧
        steps ≤ 7021*(A*B)*(N*K)+6 ∧ z.user = u.user ∧
        Cover.Fallback.RecordPayload (port 1) (fun _ => blank) 0 (singleLabelBank label x i) F ∧
        aux F ∧ ∀ j, (∀ i, port i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  have pad := singleLabelBank_pad_hoare (w := w) hB hK
  intro label port A N frame aux code x i u S payload empty ready
  obtain ⟨z,F,steps,exec,paid,user,done,off⟩ := placedHoare_exec _ port fits body (pad x i) u S (by
    intro j z
    by_cases hs : j = 0
    · subst j
      have h := payload z
      rw [encodedOwnerCell] at h
      exact h.symm
    by_cases hd : j = 1
    · subst j
      exact (empty _).symm
    rw [(ownerPad_aux _ _ (A*B) N K j hs hd).1,(ownerPad_aux _ _ (A*B) N K j hs hd).2]
    exact ready j hs hd z)
  refine ⟨z,F,steps,exec,paid.trans_eq (by ring),user,?_,?_,off⟩
  · intro l
    rw [encodedOwnerCell]
    exact (done 1 l).symm
  · intro j hs hd l
    have h := done j l
    rw [(ownerPad_aux _ _ (A*B) N K j hs hd).1,(ownerPad_aux _ _ (A*B) N K j hs hd).2] at h
    exact h

/-- Read the scan accumulators in place. The new owner bank follows the stage
tapes, with ten shared counter and work tapes after it. -/
noncomputable def stagePadPort {T : ℕ} (fan : Fin (142081+2) ↪ Fin T)
    (i : Fin 142081) : Fin 12 ↪ Fin ((T+142081*7)+142081+10) where
  toFun j := ⟨if j.val = 0 then (targetScanBank fan i 1).val else
    if j.val = 1 then T+142081*7+i.val else T+142081*7+142081+(j.val-2), by
      have hs := (targetScanBank fan i 1).isLt
      split_ifs <;> omega⟩
  inj' := by
    intro j k h
    apply Fin.ext
    have eq := congrArg Fin.val h
    dsimp only at eq
    have hs := (targetScanBank fan i 1).isLt
    split_ifs at eq <;> omega

private theorem stagePadPort_shared {T : ℕ} (fan : Fin (142081+2) ↪ Fin T)
    (i k : Fin 142081) (j : Fin 12) (h0 : j ≠ 0) (h1 : j ≠ 1) :
    stagePadPort fan i j = stagePadPort fan k j := by
  apply Fin.ext
  have b : j.val ≠ 1 := fun h => h1 (Fin.ext h)
  simp [stagePadPort,h0,b]

private theorem stagePadPort_apart {T : ℕ} (fan : Fin (142081+2) ↪ Fin T)
    (i k : Fin 142081) (ne : i ≠ k) (j : Fin 12) :
    stagePadPort fan i j ≠ stagePadPort fan k 0 ∧ stagePadPort fan i j ≠ stagePadPort fan k 1 := by
  have ns : (targetScanBank fan i 1).val ≠ (targetScanBank fan k 1).val :=
    fun h => targetScanBank_disjoint fan ne 1 1 (Fin.ext h)
  have nd : i.val ≠ k.val := fun h => ne (Fin.ext h)
  have hi := (targetScanBank fan i 1).isLt
  have hk := (targetScanBank fan k 1).isLt
  constructor <;> intro h <;> have eq := congrArg Fin.val h <;>
    simp only [stagePadPort, Function.Embedding.coeFn_mk, Fin.val_zero, Fin.val_one,
      ite_true, Nat.one_ne_zero, ite_false] at eq <;> split_ifs at eq <;> omega

/-- Pad a list of distinct owners, reusing the same four counters and scratch tapes. -/
theorem placedOwnerPads {w B K T Q : ℕ} {P U : Type} (hB : 0 < B) (hK : 0 < K)
    (fan : Fin (142081+2) ↪ Fin T) (fits : 215 ≤ Q)
    (body : P → Pr P ((T+142081*7)+142081+10) Q prime U) :
    let port := stagePadPort fan
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    let frame := ownerPadFrame (A*B) N K
    let aux := fun (S : Stacks ((T+142081*7)+142081+10) prime) => ∀ j : Fin 12, j ≠ 0 → j ≠ 1 → ∀ z,
      frame.tape j z = readAt blank (S.L (port 0 j)) (S.R (port 0 j)) (z-frame.head j)
    let code := fun i => embProg (port i) (Empty.elim : Empty → P)
      (foreign (liftQ RowPaddingConstructedAlphabet.program fits))
    let label := firstRowLabel w
    ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) (order : List (Fin 142081)), order.Nodup → ∀ u S, aux S →
      (∀ i ∈ order, Cover.Fallback.RecordPayload (port i 0) (fun _ => blank) 0 (x i) S) →
      (∀ i ∈ order, ∀ z, readAt blank (S.L (port i 1)) (S.R (port i 1)) z = blank) →
      ∃ z F steps, Exec body (Prog.seqList (order.map code)) (mk u S) steps (mk z F) ∧
        steps ≤ order.length*(7021*(A*B)*(N*K)+6)+1 ∧ z.user = u.user ∧ aux F ∧
        (∀ i ∈ order, Cover.Fallback.RecordPayload (port i 1) (fun _ => blank) 0 (singleLabelBank label x i) F) ∧
        ∀ j, (∀ i ∈ order, ∀ h, port i h ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro port A N frame aux code
  have shared := stagePadPort_shared fan
  have apart := stagePadPort_apart fan
  have pad := placedOwnerPad (w := w) hB hK fits body
  intro label x order
  induction order with
  | nil =>
    intro _ u S auxS _ _
    exact ⟨u,S,1,Exec.act .done _,by simp,rfl,auxS,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
  | cons i ks ih =>
    intro unique u S auxS inputs empty
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp unique
    obtain ⟨v,C,m,first,paid,user,out,ready,off⟩ := pad (port i) x i u S
      (inputs i List.mem_cons_self) (empty i List.mem_cons_self) (by
        intro j h0 h1 l
        rw [shared i 0 j h0 h1]
        exact auxS j h0 h1 l)
    have ne (k) (hk : k ∈ ks) : i ≠ k := fun eq => fresh (eq ▸ hk)
    obtain ⟨z,F,n,rest,bill,same,auxF,outputs,keep⟩ := ih nd v C (by
      intro j h0 h1 l
      rw [← shared i 0 j h0 h1]
      exact ready j h0 h1 l) (by
      intro k hk l
      obtain ⟨hl,hr⟩ := off _ (fun j => (apart i k (ne k hk) j).1)
      change readAt blank (C.L _) (C.R _) _ = _
      rw [hl,hr]
      exact inputs k (List.mem_cons_of_mem _ hk) l) (by
      intro k hk l
      obtain ⟨hl,hr⟩ := off _ (fun j => (apart i k (ne k hk) j).2)
      rw [hl,hr]
      exact empty k (List.mem_cons_of_mem _ hk) l)
    refine ⟨z,F,m+n,Exec.seq first rest,?_,same.trans user,auxF,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      change m ≤ 7021*(A*B)*(N*K)+6 at paid
      omega
    · intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · obtain ⟨hl,hr⟩ := keep _ (fun a ha j => (apart a k (ne a ha).symm j).2)
        intro l
        change readAt blank (F.L _) (F.R _) _ = _
        rw [hl,hr]
        exact out l
      · exact outputs k hk
    · intro j outside
      obtain ⟨hl,hr⟩ := keep j (fun k hk => outside k (List.mem_cons_of_mem _ hk))
      obtain ⟨ll,rr⟩ := off j (outside i List.mem_cons_self)
      exact ⟨hl.trans ll,hr.trans rr⟩

private theorem stagePadPort_off_original {T : ℕ} (fan : Fin (142081+2) ↪ Fin T)
    (i : Fin 142081) (j : Fin 12) (k : Fin T) :
    stagePadPort fan i j ≠ ((k.castAdd (142081*7)).castAdd 142081).castAdd 10 := by
  intro eq
  have h := congrArg Fin.val eq
  change (if j.val = 0 then T+(finProdFinEquiv (i,(0 : Fin 7))).val else
    if j.val = 1 then T+142081*7+i.val else T+142081*7+142081+(j.val-2)) = k.val at h
  split_ifs at h <;> omega

/-- A target moves to its new tape, while every other role keeps its original tape. -/
noncomputable def stageOutputBank {T : ℕ} (n : Fin 9) (fan : Fin (142081+2) ↪ Fin T) :
    Fin 142081 ↪ Fin ((T+142081*7)+142081+10) := by
  classical
  let old := fun i : Fin 142081 => (((fan (i.castAdd 2)).castAdd (142081*7)).castAdd 142081).castAdd 10
  let dst := fun i => stagePadPort fan i 1
  refine ⟨fun i => if ∃ k, targetOwner n k = i then dst i else old i,?_⟩
  intro i j eq
  dsimp only at eq
  split_ifs at eq
  · by_contra ne
    exact (stagePadPort_apart fan i j ne 1).2 eq
  · exact (stagePadPort_off_original fan i 1 _ eq).elim
  · exact (stagePadPort_off_original fan j 1 _ eq.symm).elim
  · apply (Fin.castAddEmb 2).injective
    apply fan.injective
    have val := congrArg Fin.val eq
    exact Fin.ext val

private theorem role_active_owner (n : Fin 9) (ρ : Role) (active : ρ.bank.val / 2 = BitHosting.activePair n.val) :
    let tape := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
    tape = targetOwner n ((ρ.replica,ρ.cls),ρ.port) ∨
      tape = ownerTape n ρ.replica ρ.cls (ρ.port.castLE (by decide)) := by
  intro tape
  have side := role_side n ρ active
  let addr := fun r : Role => ((Fin.cast card_role) (Fintype.equivFin Role r)).castSucc
  have bound := ρ.port.isLt
  by_cases src : ρ.bank.val % 2 = n.val % 2
  · right
    apply congrArg addr
    rw [src] at side
    simpa [owner,regSide,Nat.mod_eq_of_lt bound,show ρ.port.val < 222 by omega] using side
  · left
    apply congrArg addr
    rw [show ρ.bank.val % 2 = 1 - n.val % 2 by omega] at side
    simpa [owner,regSide,show 111+ρ.port.val < 222 by omega,Nat.add_mod,bound,Nat.mod_eq_of_lt bound] using side

/-- Put every updated target into the next labeled bank. Use the restored row sums
as the common ordinary bank for targets and retained owners. -/
theorem stageTargets_pad {T Q : ℕ} {P U : Type} (n : Fin 9)
    (fan : Fin (142081+2) ↪ Fin T) (fits : 215 ≤ Q)
    (body : P → Pr P ((T+142081*7)+142081+10) Q prime U) :
    ∃ code, ∀ w B W : ℕ, 0 < B → 0 < (prime^w)^112*W →
    let K := (prime^w)^112*W
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    let port := stagePadPort fan
    let frame := ownerPadFrame (A*B) N K
    let aux := fun (S : Stacks ((T+142081*7)+142081+10) prime) => ∀ j : Fin 12, j ≠ 0 → j ≠ 1 → ∀ z,
      frame.tape j z = readAt blank (S.L (port 0 j)) (S.R (port 0 j)) (z-frame.head j)
    let label := firstRowLabel w
    let retained := fan.trans (((Fin.castAddEmb (142081*7)).trans (Fin.castAddEmb 142081)).trans (Fin.castAddEmb 10))
    ∀ x y out,
      stageRuns.foldr (fun p cont a => ∃ b, packedStageEffect n p w B W a b ∧ cont b)
        (fun a => a = y) (singleLabelBank label x) →
      HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
      let next := collapseLabelBank (B := B) (K := K) out
      ∀ u S, aux S → RestoredOwnerPayloads n retained out S →
      (∀ k, Cover.Fallback.RecordPayload (port (targetOwner n k) 0) (fun _ => blank) 0
        (stageTargetWord n k w B K x) S) →
      (∀ k z, readAt blank (S.L (port (targetOwner n k) 1)) (S.R (port (targetOwner n k) 1)) z = blank) →
      ∃ z F steps, Exec body code (mk u S) steps (mk z F) ∧
        steps ≤ 17760*(7021*(A*B)*(N*K)+6)+1 ∧ z.user = u.user ∧ aux F ∧
        (∀ ρ : Role, let i := ((Fin.cast card_role) (Fintype.equivFin Role ρ)).castSucc
          Cover.Fallback.RecordPayload (stageOutputBank n fan i) (fun _ => blank) 0 (singleLabelBank label next i) F) ∧
        ∀ j, (∀ k h, port (targetOwner n k) h ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let targets := stageRuns.product (List.finRange 111)
  let order := targets.map (targetOwner n)
  let pad : Fin 142081 → Pr P ((T+142081*7)+142081+10) Q prime U := fun i => embProg (stagePadPort fan i) (Empty.elim : Empty → P)
    (foreign (liftQ RowPaddingConstructedAlphabet.program fits))
  refine ⟨Prog.seqList (order.map pad),?_⟩
  intro w B W hb hk K A N port frame aux
  have run := placedOwnerPads (w := w) hb hk fan fits body
  intro label retained x y out trace restore next u S ready live inputs empty
  have targetWords := fun k => restoredStage_targetWord n k w B W label x y out trace restore
  have unique : order.Nodup := (stageRuns_nodup.product (List.nodup_finRange _)).map (targetOwner_injective n)
  obtain ⟨z,F,t,exec,paid,user,headers,padded,off⟩ := run next order unique u S ready (by
    intro i hi
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hi
    rw [show next (targetOwner n k) = _ from targetWords k]
    exact inputs k) (by
    intro i hi
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hi
    exact empty k)
  have kept : RestoredOwnerPayloads n retained out F := by
    intro i hi l
    obtain ⟨hl,hr⟩ := off _ (fun a _ j => stagePadPort_off_original fan a j (fan (i.castAdd 2)))
    change F.L (retained (i.castAdd 2)) = S.L _ at hl
    change F.R (retained (i.castAdd 2)) = S.R _ at hr
    change readAt blank (F.L _) (F.R _) _ = _
    rw [hl,hr]
    exact live i hi l
  refine ⟨z,F,t,exec,?_,user,headers,?_,?_⟩
  · have count : order.length = 17760 := by
      rw [List.length_map]
      exact (List.length_product stageRuns (List.finRange 111)).trans (by rw [stageRuns_length,List.length_finRange])
    rw [count] at paid
    exact paid
  · intro ρ i
    classical
    by_cases hit : ∃ k, targetOwner n k = i
    · obtain ⟨k,hk⟩ := hit
      have pos : stageOutputBank n fan i = port i 1 := by
        have mem : ∃ a, targetOwner n a = i := ⟨k,hk⟩
        simp only [stageOutputBank,Function.Embedding.coeFn_mk,ite_eq_left mem]
        rfl
      rw [pos,← hk]
      exact padded _ (List.mem_map.mpr ⟨k,List.mem_flatMap.mpr ⟨k.1,mem_stageRuns _,
        List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩,rfl⟩)
    · have pos : stageOutputBank n fan i = retained (i.castAdd 2) := by simp only [stageOutputBank,Function.Embedding.coeFn_mk,ite_eq_right hit]; rfl
      rw [pos]
      have word : out i = singleLabelBank label next i := by
        by_cases active : ρ.bank.val / 2 = BitHosting.activePair n.val
        · obtain target | source := role_active_owner n ρ active
          · exact (hit ⟨_,target.symm⟩).elim
          · change i = _ at source
            rw [source]
            exact restoredStage_sourceWord n (ρ.replica,ρ.cls) w B W label x y out trace restore ρ.port
        · exact restoredStage_inactiveWord n w B W label x y out trace restore ρ active
      rw [← word]
      exact kept i (fun k h => hit ⟨k,h⟩)
  · intro j outside
    apply off
    intro i hi
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hi
    exact outside k

end IntegerMultBounds.MathlibTM2.M6.BitNode
