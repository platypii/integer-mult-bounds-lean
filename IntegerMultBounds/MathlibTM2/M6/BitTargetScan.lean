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
    ∃ z F steps, Exec body code (mk u S) steps (mk z F) ∧ steps ≤ 2600*(D*(N*K))+6 ∧ z.user = u.user ∧
      (∀ (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (b : Fin B) (j : Fin K),
        let initial := fun i => (selectedFrame w (Frames.initialRefs i)).symm
          (phaseRead owner x (finProdFinEquiv (b,j)) i)
        readAt blank (F.L (bank 1)) (F.R (bank 1))
          ((FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) (finProdFinEquiv (b,j))).val-(D*K) : ℤ) =
          SparseRoleCircuit.encode (selectedFrame w (Frames.finalRefs dst.val) (initial dst.val + initial t.val) s)) ∧
      ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro owner dst
  let count := fun {q : ℕ} (_ : Program 8 q prime) => q
  refine ⟨count (LabelRowXor.blocksProgram prime),?_⟩
  intro T Q P U fan bank selected fits body
  refine ⟨embProg bank (Empty.elim : Empty → P) (foreign (liftQ (LabelRowXor.blocksProgram prime) fits)),?_⟩
  intro w B W label x y out K N D trace restored pos hb u S live stored
  let v := scanInput (out (owner dst)) (D*K)
  let ready := scanFrame K N D v
  have privateReady := scanPrivate_ready K N D (out (owner dst)) bank S stored
  obtain ⟨Y,scan,hs,hd,src,values⟩ := restoredStage_targetScan n run w B W label x y out trace restored t v pos hb
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
  obtain ⟨z,F,steps,exec,paid,user,done,off⟩ := placedHoare_exec _ bank fits body scan u S rep
  refine ⟨z,F,steps,exec,?_,user,?_,off⟩
  · exact paid.trans_eq (by ring)
  · intro s b j
    let i := FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) (finProdFinEquiv (b,j))
    have h := done 1 (v.head 1+i.val)
    change Y.tape 1 _ = readAt blank (F.L (bank 1)) (F.R (bank 1)) (_-Y.head 1) at h
    rw [hd] at h
    have h0 : v.head 1 = 0 := rfl
    have result := h.symm.trans (values s b j)
    simpa only [h0,zero_add,D,K,owner,dst,Nat.cast_mul,i] using result

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
    (targets*(2600*(D*(N*K))+6+(8*(D*K)+11*(D.size+K.size)+8)+scanCounterCost ![K,N,D])+1) + (2*(D.size+K.size)+2)

/-- The shared binary product and the per-target counters fit the same linear
volume bound as the payload scans. -/
theorem stageScanCost_le (targets K N D : ℕ) (hk : 0 < K) (hn : 0 < N) (hd : 0 < D) :
    stageScanCost targets K N D ≤ (3000*targets+200)*(D*(N*K)) := by
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
  have each : 2600*V+6+(8*(D*K)+11*(D.size+K.size)+8)+scanCounterCost ![K,N,D] ≤ 3000*V := by omega
  have shared : D.size*(12*(D.size+K.size)+20)+16*(D.size+K.size)+24+1+(2*(D.size+K.size)+2) ≤ 200*V := by
    nlinarith only [sq,cross,ds,ks,pos]
  have all := Nat.mul_le_mul_left targets each
  change _ ≤ (3000*targets+200)*V
  unfold stageScanCost
  change _ + (targets*(2600*V+6+(8*(D*K)+11*(D.size+K.size)+8)+scanCounterCost ![K,N,D])+1) + _ ≤ _
  rw [Nat.add_mul]
  rw [show targets*(3000*V) = 3000*targets*V by ring] at all
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
    let result := fun (k : I) (L R : List (Fin (prime+4))) =>
      let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n k.1.1 k.1.2,ownerTape_injective ..⟩
      ∀ (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (b : Fin B) (j : Fin K),
        let initial := fun i => (selectedFrame w (Frames.initialRefs i)).symm
          (phaseRead owner x (finProdFinEquiv (b,j)) i)
        let dst := 111+k.2.val
        readAt blank L R ((FlatCoordinateLayout.index (AffineFieldCoordinates.embed s)
          (finProdFinEquiv (b,j))).val-(D*K) : ℤ) = SparseRoleCircuit.encode
          (selectedFrame w (Frames.finalRefs dst) (initial dst + initial k.2.val) s)
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
  let price := 2600*(D*(N*K))+6+(8*(D*K)+11*(D.size+K.size)+8)+scanCounterCost ![K,N,D]
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
    let result := fun (k : I) (L R : List (Fin (prime+4))) =>
      let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n k.1.1 k.1.2,ownerTape_injective ..⟩
      ∀ (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (b : Fin B) (j : Fin K),
        let initial := fun i => (selectedFrame w (Frames.initialRefs i)).symm
          (phaseRead owner x (finProdFinEquiv (b,j)) i)
        let dst := 111+k.2.val
        readAt blank L R ((FlatCoordinateLayout.index (AffineFieldCoordinates.embed s)
          (finProdFinEquiv (b,j))).val-(D*K) : ℤ) = SparseRoleCircuit.encode
          (selectedFrame w (Frames.finalRefs dst) (initial dst + initial k.2.val) s)
    ∃ z F steps, Exec (fun g => embProg inner id (body g)) code (mk u S) steps (mk z F) ∧
      steps ≤ time + (3000*order.length+200)*(D*(N*K)) ∧ z.user = u.user ∧
      ∀ k, result k (F.L (bank k 1)) (F.R (bank k 1)) := by
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
  obtain ⟨z,F,t,scanned,paid,saved,done,_⟩ := run w B W label x y out trace restore pos hb v' A'
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
  exact ⟨z,F,_,Exec.seq placed scanned,Nat.add_le_add_left (paid.trans linear) time,
    saved.trans (same.trans user),done⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
