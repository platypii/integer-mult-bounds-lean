module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedStage

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

/-- Scan the restored targets in stage order. Each accumulator retains its
output while all subsequent scans execute on disjoint banks. -/
theorem stageTargets_host (n : Fin 9) :
    let I := (Fin 32 × Fin 5) × Fin 111
    let order := stageRuns.product (List.finRange 111)
    ∃ states : ℕ, ∀ {T Q : ℕ} {P U : Type} (fan : Fin (142081+2) ↪ Fin T), states ≤ Q →
    let full := fan.trans (Fin.castAddEmb (142081*7))
    let bank := fun k : I => targetScanBank fan (targetOwner n k)
    ∀ body : P → Pr P (T+142081*7) Q prime U, ∃ code,
    ∀ (w B W : ℕ) (label : Cover.LabelPadding.Label 64 w) (x y out),
    let K := (prime^w)^112*W
    let N := prime^(64*(w*64))
    let D := (prime^w)^16*B
    stageRuns.foldr (fun k next a => ∃ b, packedStageEffect n k w B W a b ∧ next b)
      (fun a => a = y) (singleLabelBank label x) →
    HelperLabelTrace w (B*N) W (restoreSlotChanges (stageFinalSlot n)) y out →
    0 < K → 0 < B → ∀ u S, HelperFan full out S →
    (∀ k j, S.L (bank k (Fin.succ j)) = (if j = 0 then [] else [separator]) ∧
      S.R (bank k j.succ) = scanPrivateWords K N D j) →
    let result := fun (k : I) (L R : List (Fin (prime+4))) =>
      let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n k.1.1 k.1.2,ownerTape_injective ..⟩
      ∀ (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) (b : Fin B) (j : Fin K),
        let initial := fun i => (selectedFrame w (Frames.initialRefs i)).symm
          (phaseRead owner x (finProdFinEquiv (b,j)) i)
        let dst := 111+k.2.val
        readAt blank L R ((FlatCoordinateLayout.index (AffineFieldCoordinates.embed s)
          (finProdFinEquiv (b,j))).val-(D*K) : ℤ) = SparseRoleCircuit.encode
          (selectedFrame w (Frames.finalRefs dst) (initial dst + initial k.2.val) s)
    ∃ z F steps, Exec body code (mk u S) steps (mk z F) ∧ steps ≤ order.length*(2600*(D*(N*K))+6)+1 ∧
      z.user = u.user ∧ (∀ k, result k (F.L (bank k 1)) (F.R (bank k 1))) ∧
      ∀ j, (∀ k i, bank k i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  classical
  intro I order
  choose req scan using fun k : I => restoredTarget_host n k.1 k.2
  refine ⟨Finset.univ.sup req,?_⟩
  intro T Q P U fan fits full bank body
  choose code execute using fun k => scan k full (bank k) rfl ((Finset.le_sup (Finset.mem_univ k)).trans fits) body
  refine ⟨Prog.seqList (order.map code),?_⟩
  intro w B W label x y out K N D trace restored pos hb u S live stored result
  let price := 2600*(D*(N*K))+6
  have run (ks : List I) (unique : ks.Nodup) (v : HS _ Q prime U) (A : Stacks _ prime)
      (ready : ∀ k ∈ ks, ∀ i, A.L (bank k i) = S.L (bank k i) ∧ A.R (bank k i) = S.R (bank k i)) :
      ∃ z F steps, Exec body (Prog.seqList (ks.map code)) (mk v A) steps (mk z F) ∧
        steps ≤ ks.length*price+1 ∧ z.user = v.user ∧
        (∀ k ∈ ks, result k (F.L (bank k 1)) (F.R (bank k 1))) ∧
        ∀ j, (∀ k ∈ ks, ∀ i, bank k i ≠ j) → F.L j = A.L j ∧ F.R j = A.R j := by
    induction ks generalizing v A with
    | nil => exact ⟨v,A,1,Exec.act .done _,by simp,rfl,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
    | cons k ks ih =>
      obtain ⟨fresh,nd⟩ := List.nodup_cons.mp unique
      have input := fanPayload live (targetOwner n k)
      obtain ⟨v',A',m,first,paid,user,done,off⟩ := execute k w B W label x y out trace restored pos hb v A (by
        intro j
        change readAt blank (A.L (bank k 0)) (A.R (bank k 0)) _ = _
        rw [(ready k List.mem_cons_self 0).1,(ready k List.mem_cons_self 0).2]
        exact input j) (fun j => by
          rw [(ready k List.mem_cons_self j.succ).1,(ready k List.mem_cons_self j.succ).2]
          exact stored k j)
      have apart (h) (mem : h ∈ ks) := targetScanBank_disjoint fan
        ((targetOwner_injective n).ne (fun eqn : k = h => fresh (eqn ▸ mem)))
      obtain ⟨z,F,t,rest,bill,same,outputs,keep⟩ := ih nd v' A' (fun h mem i => by
        obtain ⟨hl,hr⟩ := off _ (fun a => apart h mem a i)
        have old := ready h (List.mem_cons_of_mem _ mem) i
        exact ⟨hl.trans old.1,hr.trans old.2⟩)
      refine ⟨z,F,m+t,Exec.seq first rest,?_,same.trans user,?_,?_⟩
      · change m ≤ price at paid
        simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
      · intro h mem
        rcases List.mem_cons.mp mem with rfl | tail
        · obtain ⟨hl,hr⟩ := keep _ (fun a ha i => (apart a ha 1 i).symm)
          rw [hl,hr]
          exact done
        · exact outputs h tail
      · intro j hj
        have tail := keep j (fun h mem => hj h (List.mem_cons_of_mem _ mem))
        have head := off j (hj k List.mem_cons_self)
        exact ⟨tail.1.trans head.1,tail.2.trans head.2⟩
  obtain ⟨z,F,t,exec,paid,user,done,off⟩ := run order (stageRuns_nodup.product (List.nodup_finRange _))
    u S (fun _ _ _ => ⟨rfl,rfl⟩)
  exact ⟨z,F,t,exec,paid,user,fun k => done k (List.mem_flatMap.mpr ⟨k.1,mem_stageRuns _,
    List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩),fun j outside => off j (fun h _ => outside h)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
