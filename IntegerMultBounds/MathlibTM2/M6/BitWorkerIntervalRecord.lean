module

public import IntegerMultBounds.MathlibTM2.M6.BitWorkerIntervalMerge
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleReturn

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Node Mult.PhaseCellToeplitz
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

/-- Load a positioned record, split it into physical rows and run the recursive
row merge. Its result represents the transpose of the entire interleaved record. -/
theorem workerRecordTranspose {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (splitter returned : Fin intervalSplitTapes ↪ Fin T) (merge : Pr P T Q prime U)
    (src tmp : Fin T) (apart : [src,tmp,splitter 0].Nodup)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
      (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
    ∀ lane : Descriptor, let V := volume prime lane
      let wide := {lane with afterD := lane.afterD*142080}
      let size : V*142080 = volume prime wide := by simp [V,wide,volume,Nat.mul_assoc]
      ∀ (word : Fin (volume prime wide) → ZMod 2) u S (price : List (Fin T) → ℕ) (reserve : List (Fin T) → Stacks T prime → ℕ),
      let input := fun k => word (Fin.cast size k)
      let target := putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode (a := prime) ∘ input))
      let data := fun r (i : Fin V) => input (finProdFinEquiv (i,r))
      let rows := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
      let output := fun k : Fin (V*142080) => let p := finProdFinEquiv.symm k
                                              SparseRoleCircuit.encode (a := prime) (rows p.2 p.1)
      ∀ preserved : Fin T → Prop, 0 < V → RecordPayload src (fun _ => blank) 0 word S →
      S.L tmp = [] → S.R tmp = [] → (∀ i, S.L (splitter i) = [] ∧ S.R (splitter i) = []) →
      (∀ v D, RepT (intervalOwnerBank target data) (embStk splitter D).L (embStk splitter D).R →
        (∀ j, (∀ i, splitter i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        (∀ js : List _, js.Nodup → tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+
          2*(V*142080)+6*(Fast.Main.mnProgPush split*((149*(intervalSplitTapes+5)+5)*(V*142080)+24))) →
        ∃ z F t, Exec body merge (mk v D) t (mk z F) ∧ (∀ js, js.Nodup → t + reserve js F ≤ price js) ∧ z.user = v.user ∧
          RepT (intervalOwnerBank (putWord target 0 (List.ofFn output)) rows) (embStk returned F).L (embStk returned F).R ∧
          ∀ j, preserved j → F.L j = S.L j ∧ F.R j = S.R j) →
      ∃ z F t, Exec body (((loadCompactWord src tmp (splitter 0)).seq (embProg splitter Empty.elim split)).seq merge)
        (mk u S) t (mk z F) ∧ (∀ js, js.Nodup → t + reserve js F ≤ (149*(intervalSplitTapes+5)+13)*(V*142080)+34+price js) ∧
        z.user = u.user ∧ RecordPayload (returned 0) (fun _ => blank) 0
          (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word) F ∧
        ∀ j, preserved j → F.L j = S.L j ∧ F.R j = S.R j := by
  intro split lane V wide size word u S price reserve input target data rows output preserved positive source tl tr empty run
  have payload : WordAtZero input (S.L src) (S.R src) := by
    have reads : WordAtZero word (S.L src) (S.R src) := by
      intro k
      rw [← encodedOwnerCell]
      simpa only [sub_zero,List.map_ofFn] using source k
    have castRead {m n : ℕ} (h : m = n) (x : Fin n → ZMod 2) {l r} :
        WordAtZero x l r → WordAtZero (fun k => x (k.cast h)) l r := by subst n; exact id
    exact castRead size word reads
  obtain ⟨v,user,load⟩ := loadCompactWord_exec body src tmp (splitter 0) apart input u S payload tl tr
  rw [(empty 0).2,List.append_nil] at load
  let B := {S with R := Function.update S.R (splitter 0) (List.ofFn (SparseRoleCircuit.encode (a := prime) ∘ input))}
  obtain ⟨a,D,k,prepare,initial,paid,rep,off,growth⟩ := splitEncodedWithCharge body splitter capacity positive input v B
    (Function.update_self ..) (fun i => (empty i).1)
    (fun i ne => (Function.update_of_ne (splitter.injective.ne ne) ..).trans (empty i).2)
  obtain ⟨z,F,t,ran,bill,same,result,frame⟩ := run a D rep (fun j away =>
    ⟨(off j away).1,(off j away).2.trans (Function.update_of_ne (away 0).symm ..)⟩) (by
      intro js unique
      have copied := prependedWordCharge S (splitter 0) (List.ofFn (SparseRoleCircuit.encode (a := prime) ∘ input)) js unique
      simp only [(empty 0).2,List.append_nil,List.length_ofFn] at copied
      have splitGrowth := growth js unique
      have bound := Nat.mul_le_mul_left (6*Fast.Main.mnProgPush split) paid
      change tapeCharge cleanupWeight js B ≤ _ at copied
      linarith only [copied,splitGrowth,bound])
  let y := Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word
  have eq (k : Fin (V*142080)) : rows (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1 = y (k.cast size) := by
    obtain ⟨⟨i,r⟩,rfl⟩ := finProdFinEquiv.surjective k
    simpa only [Equiv.symm_apply_apply] using (transpose_trailingRows lane 142080 word i r).symm
  change RepT (intervalOwnerBank (putWord target 0 (List.ofFn fun k => SparseRoleCircuit.encode (a := prime)
    (rows (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1))) rows) _ _ at result
  simp only [eq] at result
  have overwrite := FlatControlledShiftArray.overwrite (fun _ => blank) 0
    (List.ofFn (SparseRoleCircuit.encode (a := prime) ∘ input))
    (List.ofFn fun k => SparseRoleCircuit.encode (a := prime) (y (k.cast size))) (by simp)
  rw [show putWord target 0 _ = _ from overwrite] at result
  refine ⟨z,F,_,(load.seq prepare).seq ran,?_,same.trans (initial.trans user),
    castPayload size (returned 0) F y (intervalOwnerPayload returned F _ _ result),frame⟩
  intro js distinct
  specialize bill js distinct
  simp only [Nat.add_mul] at paid ⊢
  omega

/-- Charge the child once on the union of the cleared bank and the caller's
observed tapes. A cleared tape has minimum weight even when the caller observes it. -/
theorem cleanupBound_clearBank {T : ℕ} {S D F : Stacks T prime} {n m price localCost : ℕ}
    (work : List (Fin T)) (unique : work.Nodup) (child : CleanupBound S D n price)
    (time : m ≤ tapeCharge cleanupWeight work D + localCost)
    (empty : ∀ j ∈ work, F.L j = [] ∧ F.R j = [])
    (stock : ∀ j, (F.L j).length ≤ (D.L j).length ∧ (F.R j).length ≤ (D.R j).length) :
    CleanupBound S F (n+m) (price+tapeCharge cleanupWeight work S+localCost) := by
  intro js distinct
  let outside := js.filter fun j => j ∉ work
  have disjoint : work.Disjoint outside := by
    intro j hj hout
    exact (of_decide_eq_true (List.mem_filter.mp hout).2) hj
  have paid := child (work++outside) (List.nodup_append.mpr
    ⟨unique,distinct.filter _,fun _ ha _ hb eq => disjoint ha (eq ▸ hb)⟩)
  change n+tapeCharge cleanupWeight (work++outside) D ≤ tapeCharge cleanupWeight (work++outside) S+price at paid
  simp only [tapeCharge,List.map_append,List.sum_append] at paid
  have split (xs : List (Fin T)) :
      tapeCharge cleanupWeight xs F + tapeCharge cleanupWeight (xs.filter fun j => j ∉ work) S ≤
      tapeCharge cleanupWeight xs S + tapeCharge cleanupWeight (xs.filter fun j => j ∉ work) D := by
    induction xs with
    | nil => simp [tapeCharge]
    | cons j xs ih =>
      by_cases h : j ∈ work
      · obtain ⟨left,right⟩ := empty j h
        simp [tapeCharge,h,cleanupWeight,left,right] at ih ⊢
        omega
      · obtain ⟨left,right⟩ := stock j
        simp [tapeCharge,h,cleanupWeight] at ih ⊢
        omega
  have bound := split js
  change n+m+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
  dsimp only [outside,tapeCharge] at paid time bound ⊢
  omega

/-- A row continuation can pay for private tape cleanup at merge exit. Its
budget then appears once in the cost of the complete return to the caller. -/
theorem finishIntervalRecord {T Q m : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    {prepare : Pr P T Q prime U} {count src dst saved tmp : Fin T}
    (apart : [count,src,dst,saved,tmp].Nodup) (work : List (Fin T))
    (distinct : work.Nodup) (inside : src ∈ work) (outside : dst ∉ work)
    {old changed : Fin m → ZMod 2} {u v : HS T Q prime U} {S D : Stacks T prime}
    {steps budget : ℕ} (run : Exec body prepare (mk u S) steps (mk v D))
    (paid : steps + (work.map fun j => 4*(D.L j).length+2*(D.R j).length+4).sum ≤ budget)
    (oldRecord : RecordPayload dst (fun _ => blank) 0 old D)
    (newRecord : RecordPayload src (fun _ => blank) 0 changed D)
    (hc : D.R count = []) (hs : D.R saved = []) (hl : D.L tmp = []) (hr : D.R tmp = []) :
    let write := (loadCompactWord src tmp count).seq
      (((usub count dst tmp).seq (movePrefix count src dst saved tmp)).seq (bclear count))
    ∃ z F n, Exec body (prepare.seq (write.seq (clearWorkTapes work))) (mk u S) n (mk z F) ∧
      n ≤ budget+18*m+23 ∧ z.user = v.user ∧ RecordPayload dst (fun _ => blank) 0 changed F ∧
      (∀ j ∈ work, F.L j = [] ∧ F.R j = []) ∧
      ∀ j, j ≠ dst → j ∉ work → F.L j = D.L j ∧ F.R j = D.R j := by
  obtain ⟨z,F,n,finish,cost,user,result,empty,frame⟩ := returnIdleBank_exec body apart work
    distinct inside outside old changed v D oldRecord newRecord hc hs hl hr
  exact ⟨z,F,_,run.seq finish,by omega,user,result,empty,frame⟩

/-- Execute a packed-order child, return its transpose in place and clear its entire private bank. -/
theorem packedIntervalRecordClean {P U : Type} {M N Q price w : ℕ} (lane : Descriptor)
    (width : lane.width = 64*w) (positive : 0 < volume prime lane)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P N Q prime U} {code} {src dst : Fin (142081+2) ↪ Fin N} {seed : Stacks N prime}
    (child : PackedPieceHandoffWithCharge cleanupWeight (volume prime lane)
      (packedChildOutput w (volume prime lane)) body code src dst seed price) :
    let T := intervalSplitTapes
    let H := 142082+T+N
    let split : Pr Empty T Q prime U := intervalPrepare.seq (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
    ∀ (place : Fin H ↪ Fin M),
    let caller := ((Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)).trans place
    let V := volume prime lane
    ∀ (payload tmp count saved : Fin M), [count,caller 0,payload,saved,tmp].Nodup →
    (∀ i, place i ≠ payload ∧ place i ≠ tmp ∧ place i ≠ count ∧ place i ≠ saved) →
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) M Q prime U) (program : Pr (Empty ⊕ P) M Q prime U),
    let wide := {lane with afterD := lane.afterD*142080}
    let size : V*142080 = volume prime wide := by simp [V,wide,volume,Nat.mul_assoc]
    let logical := (packedChildPosition wide size.symm).symm
    ∀ (word : Fin (volume prime wide) → ZMod 2) (u : HS M Q prime U) (S : Stacks M prime),
      RecordPayload payload (fun _ => blank) 0 (word ∘ logical) S → S.R count = [] → S.R saved = [] → S.L tmp = [] → S.R tmp = [] →
      (∀ i, S.L (caller i) = [] ∧ S.R (caller i) = []) →
      (∀ i : Fin 142082, let j := place ((i.castAdd T).castAdd N)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := place (i.natAdd (142082+T))
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      let changed := Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word
      let work := List.ofFn place
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧ z.user = u.user ∧
        RecordPayload payload (fun _ => blank) 0 (changed ∘ logical) F ∧
        n ≤ tapeCharge cleanupWeight work S+(10*(V*142080)+10)+
          (1+6*Fast.Main.mnProgPush split)*((149*(T+5)+5)*(V*142080)+24)+
          (142081*(8*V+10+2*V)+1+price)+13*(149*(V*142080)*(T+5)+6)+18*(V*142080)+23 ∧
        (∀ i, F.L (place i) = [] ∧ F.R (place i) = []) ∧
        ∀ j, j ≠ payload → (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro T H split place caller V payload tmp count saved apart off
  have distinct := apart
  regs_ne distinct
  obtain ⟨host,program,bank,target,run⟩ := packedIntervalFromWordWithCharge lane width positive capacity child place
    payload tmp (by simp [‹payload ≠ tmp›]; exact ⟨(off _).1.symm,(off _).2.1.symm⟩)
  let work := List.ofFn place
  have unique : work.Nodup := List.nodup_ofFn.mpr place.injective
  have mem (j) : j ∈ work ↔ ∃ i, place i = j := List.mem_ofFn
  let write : Pr (Empty ⊕ P) M Q prime U := (loadCompactWord (bank 0) tmp count).seq
    (((usub count payload tmp).seq (movePrefix count (bank 0) payload saved tmp)).seq (bclear count))
  refine ⟨host,program.seq (write.seq (clearWorkTapes work)),?_⟩
  intro wide size logical word u S before hc hs hl hr empty fresh prepared changed _
  obtain ⟨v,D,n,exec,user,result,bill,frame⟩ := run word u S (by
    intro i
    rw [← encodedOwnerCell]
    simpa only [sub_zero,List.map_ofFn] using before i) hl hr empty fresh prepared
  have old := frame payload (fun i => (off i).1)
  have original : RecordPayload payload (fun _ => blank) 0 (word ∘ logical) D := by
    intro i
    simpa only [old.1,old.2] using before i
  have packed := intervalOwnerPayload bank D _ _ result
  have merged : RecordPayload (bank 0) (fun _ => blank) 0 (changed ∘ logical) D := by
    simpa only [Function.comp_def,Prod.mk.eta,Equiv.apply_symm_apply] using packed
  have temp := frame tmp (fun i => (off i).2.1)
  obtain ⟨z,F,t,done,cost,same,out,clean,keep⟩ := finishIntervalRecord host (by simpa only [target] using apart)
    work unique ((mem _).2 ⟨_,target.symm⟩) (fun h => by obtain ⟨i,e⟩ := (mem _).1 h; exact (off i).1 e)
    exec (bill work unique) original merged ((frame count (fun i => (off i).2.2.1)).2.trans hc)
    ((frame saved (fun i => (off i).2.2.2)).2.trans hs) (temp.1.trans hl) (temp.2.trans hr)
  refine ⟨z,F,t,done,same.trans user,out,cost,fun i => clean _ ((mem _).2 ⟨i,rfl⟩),?_⟩
  intro j ne away
  have h := keep j ne (fun h => by obtain ⟨i,e⟩ := (mem _).1 h; exact away i e)
  exact ⟨h.1.trans (frame j away).1,h.2.trans (frame j away).2⟩

local notation "N" => rowSwapBlock.tapes

/-- Execute the packed child from the caller's record. The original payload and
writeback registers lie outside the splitter and private dimension bank. -/
theorem recursiveIntervalRecord {P U : Type} {T B Q w W atom price lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoff ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    (splitter : Fin intervalSplitTapes ↪ Fin T) (directory : Fin 72 ↪ Fin T)
    (apart : ∀ i j, splitter i ≠ directory j) (source : Fin 72 ↪ Fin T)
    (separate : ∀ i j, directory i ≠ source j) (outside : ∀ i j, splitter i ≠ source j) :
    let live := (intervalOwners 142080).trans splitter
    let H := 142082+T+B
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
    let extend := Fin.castAddEmb (n := H) (142080*(N+35))
    let initial := (splitter.trans caller).trans extend
    let regs := (directory.trans caller).trans extend
    let raw := (source.trans caller).trans extend
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let V := volume prime lane
    let wide := {lane with afterD := lane.afterD*142080}
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (bank : Fin intervalSplitTapes ↪ Fin (H+142080*(N+35))),
    bank 0 = initial 0 ∧ ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      RecordPayload (raw 24) (fun _ => blank) 0 word S → S.L (raw 59) = [] → S.R (raw 59) = [] → S.R (raw 60) = [] → S.R (raw 61) = [] →
      (∀ i, S.L (initial i) = [] ∧ S.R (initial i) = []) →
      S.R (raw 2) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (raw 53) = binSyms W.size W → S.R (raw 28) = binSyms 1 1 →
      (S.R (raw 71)).length = w+1 →
      (∀ i, S.L (regs i) = [] ∧ S.R (regs i) = []) →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd B)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin B, let j := extend (i.natAdd (142082+T))
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (149*(intervalSplitTapes+5)+13)*(V*142080)+34+((6*((prime^(w+1)).size+W.size)+27*(w+1)+44) + (intervalChildToll U lo hi w W axes + price + (149*(V*142080)*(intervalSplitTapes+5)+6)))+(20*(V*142080)+22) ∧
        z.user = u.user ∧ RecordPayload (raw 24) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word) F ∧
        ∀ j, j ≠ source 24 → (∀ i, splitter i ≠ j) → (∀ i, directory i ≠ j) →
          F.L (extend (caller j)) = S.L (extend (caller j)) ∧ F.R (extend (caller j)) = S.R (extend (caller j)) := by
  intro live H caller extend initial regs raw small ports lane V wide
  obtain ⟨host,merge,bank,targetBank,run⟩ := workerIntervalMerge capacity mergeCap ordered fits positive
    widthAt child splitter directory apart source separate
  have rawOff (i j) : initial i ≠ raw j := extend.injective.ne (caller.injective.ne (outside i j))
  have distinct : [raw 24,raw 59,initial 0].Nodup := by
    simp [raw.injective.eq_iff,(rawOff 0 24).symm,(rawOff 0 59).symm]
  have wrapper := workerRecordTranspose host initial bank merge (raw 24) (raw 59) distinct mergeCap lane
  let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
    (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) mergeCap))
  let copy : Pr (Empty ⊕ P) _ Q prime U := (loadCompactWord (raw 24) (raw 59) (initial 0)).seq (embProg initial Empty.elim split)
  let write : Pr (Empty ⊕ P) _ Q prime U := (loadCompactWord (bank 0) (raw 59) (raw 60)).seq
    (((usub (raw 60) (raw 24) (raw 59)).seq (movePrefix (raw 60) (bank 0) (raw 24) (raw 61) (raw 59))).seq (bclear (raw 60)))
  refine ⟨host,((copy.seq merge).seq write),bank,targetBank,?_⟩
  intro word u S payload tl tr hc hs freshSplit base suffix unit atom dims free fresh seedReady
  have vol : 0 < V := by
    change 0 < volume prime (phaseIntervalChild lo hi (w+1) W axes)
    rw [intervalChild_volume ordered fits]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive
  let preserved j := ∃ t, j = extend (caller t) ∧ (∀ i, splitter i ≠ t) ∧ (∀ i, directory i ≠ t)
  obtain ⟨z,F,n,exec,paid,user,read,frame⟩ := wrapper word u S (fun _ => _) (fun _ _ => 0) preserved vol payload tl tr freshSplit (by
    intro v D rep off _
    have rawSame j := off (raw j) (fun i => rawOff i j)
    obtain ⟨y,G,t,ran,bill,same,result,keep⟩ := run _ _ v D rep
      ((rawSame 2).2.trans base) ((rawSame 53).2.trans suffix) ((rawSame 28).2.trans unit)
      ((congrArg List.length (rawSame 71).2).trans atom)
      (fun j => by
        have h := off (regs j) (fun i => extend.injective.ne (caller.injective.ne (apart i j)))
        exact ⟨h.1.trans (dims j).1,h.2.trans (dims j).2⟩)
      (fun r k ne => by
        have h := off (ports r k) (by
          intro i eq
          change (caller (splitter i)).castAdd _ = intervalRecordBank _ (small 24) r k at eq
          change k ≠ small 24 at ne
          change finSumFinEquiv (Sum.inl (caller (splitter i))) = finSumFinEquiv _ at eq
          have contra := finSumFinEquiv.injective eq
          simp [ne] at contra)
        exact ⟨h.1.trans (free r k ne).1,h.2.trans (free r k ne).2⟩)
      (fun i => by
        have h := off (extend ((i.castAdd T).castAdd B)) (fun j => extend.injective.ne (by
          intro eq
          have e := congrArg Fin.val eq
          change 142082+(splitter j).val = i.val at e
          omega))
        exact ⟨h.1.trans (fresh i).1,h.2.trans (fresh i).2⟩)
      (fun i => by
        have h := off (extend (i.natAdd (142082+T))) (fun j => extend.injective.ne (by
          intro eq
          have e := congrArg Fin.val eq
          change 142082+(splitter j).val = 142082+T+i.val at e
          omega))
        exact ⟨h.1.trans (seedReady i).1,h.2.trans (seedReady i).2⟩)
    refine ⟨y,G,t,ran,fun _ _ => bill,same,result,?_⟩
    rintro j ⟨k,rfl,notSplit,notWork⟩
    have h := off _ (fun i => extend.injective.ne (caller.injective.ne (notSplit i)))
    exact ⟨(keep k notSplit notWork).1.trans h.1,(keep k notSplit notWork).2.trans h.2⟩)
  have rawSame (i) := frame (raw i) ⟨source i,rfl,fun j => outside j i,fun j => separate j i⟩
  have payloadF : RecordPayload (raw 24) (fun _ => blank) 0 word F := by
    intro j
    simpa only [(rawSame 24).1,(rawSame 24).2] using payload j
  have portsApart : [raw 60,bank 0,raw 24,raw 61,raw 59].Nodup := by
    rw [targetBank]
    simp [raw.injective.eq_iff]
    exact ⟨(rawOff 0 60).symm,rawOff 0 24,rawOff 0 61,rawOff 0 59⟩
  obtain ⟨v,G,back,same,result,_,_,left,right⟩ := returnIdlePayloadFromBlank_exec host portsApart word _ z F
    payloadF read ((rawSame 60).2.trans hc) ((rawSame 61).2.trans hs)
    ((rawSame 59).1.trans tl) ((rawSame 59).2.trans tr)
  have size : volume prime wide = V*142080 := by simp [wide,volume,V,Nat.mul_assoc]
  refine ⟨v,G,_,exec.seq back,by rw [size]; exact Nat.add_le_add_right (paid [] (by simp)) _,same.trans user,result,?_⟩
  intro j ne hs hd
  have keep := frame _ ⟨j,rfl,hs,hd⟩
  have original := right (extend (caller j)) (extend.injective.ne (caller.injective.ne ne))
    (by rw [targetBank]; exact extend.injective.ne (caller.injective.ne (hs 0).symm))
  exact ⟨(left _).trans keep.1,original.trans keep.2⟩

/-- Return the ordinary-order transpose to its caller and reclaim the selected private tapes. -/
theorem recursiveIntervalRecordClean {P U : Type} {T B Q w W atom price lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoffWithCharge cleanupWeight ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    (splitter : Fin intervalSplitTapes ↪ Fin T) (directory : Fin 72 ↪ Fin T)
    (apart : ∀ i j, splitter i ≠ directory j) (source : Fin 72 ↪ Fin T)
    (separate : ∀ i j, directory i ≠ source j) (outside : ∀ i j, splitter i ≠ source j) :
    let live := (intervalOwners 142080).trans splitter
    let H := 142082+T+B
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
    let extend := Fin.castAddEmb (n := H) (142080*(N+35))
    let initial := (splitter.trans caller).trans extend
    let regs := (directory.trans caller).trans extend
    let raw := (source.trans caller).trans extend
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let V := volume prime lane
    let wide := {lane with afterD := lane.afterD*142080}
    ∀ work : List (Fin (H+142080*(N+35))), work.Nodup → initial 0 ∈ work → raw 24 ∉ work →
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (bank : Fin intervalSplitTapes ↪ Fin (H+142080*(N+35))) (setupRate passRate : ℕ),
    bank 0 = initial 0 ∧ ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      RecordPayload (raw 24) (fun _ => blank) 0 word S → S.L (raw 59) = [] → S.R (raw 59) = [] → S.R (raw 60) = [] → S.R (raw 61) = [] →
      (∀ i, S.L (initial i) = [] ∧ S.R (initial i) = []) →
      S.R (raw 2) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (raw 53) = binSyms W.size W → S.R (raw 28) = binSyms 1 1 →
      (S.R (raw 71)).length = w+1 →
      (∀ i, S.L (regs i) = [] ∧ S.R (regs i) = []) →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd B)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin B, let j := extend (i.natAdd (142082+T))
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
        (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) mergeCap))
      let M := prime^(w+1)
        let pass := intervalPassTime U lo hi w W axes
        let header := 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58
        let volume := V*142080
        let entryGrowth := 2*volume+6*(Fast.Main.mnProgPush split*((149*(intervalSplitTapes+5)+5)*volume+24))
        let localCost := setupRate*(6*(M.size+W.size)+27*(w+1)+44)+
          passRate*(142080*(header+pass)+1+(142080*pass+1))+
          (142081*(8*V+10+2*V)+1+price)+13*(149*volume*(intervalSplitTapes+5)+6)
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        CleanupBound S F n ((149*(intervalSplitTapes+5)+13)*volume+34+
          (tapeCharge cleanupWeight work S+entryGrowth+localCost)+18*volume+23) ∧
        z.user = u.user ∧ RecordPayload (raw 24) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word) F ∧
        (∀ j ∈ work, F.L j = [] ∧ F.R j = []) ∧
        ∀ j, extend (caller j) ∉ work → j ≠ source 24 → (∀ i, splitter i ≠ j) → (∀ i, directory i ≠ j) →
          F.L (extend (caller j)) = S.L (extend (caller j)) ∧ F.R (extend (caller j)) = S.R (extend (caller j)) := by
  intro live H caller extend initial regs raw small ports lane V wide work unique inside away
  obtain ⟨host,merge,bank,setupRate,passRate,targetBank,run⟩ := workerIntervalMergeWithCharge capacity mergeCap ordered fits positive
    widthAt child splitter directory apart source separate
  have rawOff (i j) : initial i ≠ raw j := extend.injective.ne (caller.injective.ne (outside i j))
  have distinct : [raw 24,raw 59,initial 0].Nodup := by
    simp [raw.injective.eq_iff,(rawOff 0 24).symm,(rawOff 0 59).symm]
  have wrapper := workerRecordTranspose host initial bank merge (raw 24) (raw 59) distinct mergeCap lane
  let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
    (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) mergeCap))
  let copy : Pr (Empty ⊕ P) _ Q prime U := (loadCompactWord (raw 24) (raw 59) (initial 0)).seq (embProg initial Empty.elim split)
  let write : Pr (Empty ⊕ P) _ Q prime U := (loadCompactWord (bank 0) (raw 59) (raw 60)).seq
    (((usub (raw 60) (raw 24) (raw 59)).seq (movePrefix (raw 60) (bank 0) (raw 24) (raw 61) (raw 59))).seq (bclear (raw 60)))
  refine ⟨host,((copy.seq merge).seq (write.seq (clearWorkTapes work))),bank,setupRate,passRate,targetBank,?_⟩
  intro word u S payload tl tr hc hs freshSplit base suffix unit atom dims free fresh seedReady _ M pass header volume entryGrowth localCost
  have vol : 0 < V := by
    change 0 < RecursiveInterchangeLayout.volume prime (phaseIntervalChild lo hi (w+1) W axes)
    rw [intervalChild_volume ordered fits]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive
  let preserved j := ∃ t, j = extend (caller t) ∧ (∀ i, splitter i ≠ t) ∧ (∀ i, directory i ≠ t)
  obtain ⟨z,F,n,exec,paid,user,read,frame⟩ := wrapper word u S (fun js => tapeCharge cleanupWeight js S+entryGrowth+localCost) (tapeCharge cleanupWeight) preserved vol payload tl tr freshSplit (by
    intro v D rep off stock
    have rawSame j := off (raw j) (fun i => rawOff i j)
    obtain ⟨y,G,t,ran,bill,same,result,keep⟩ := run _ _ v D rep
      ((rawSame 2).2.trans base) ((rawSame 53).2.trans suffix) ((rawSame 28).2.trans unit)
      ((congrArg List.length (rawSame 71).2).trans atom)
      (fun j => by
        have h := off (regs j) (fun i => extend.injective.ne (caller.injective.ne (apart i j)))
        exact ⟨h.1.trans (dims j).1,h.2.trans (dims j).2⟩)
      (fun r k ne => by
        have h := off (ports r k) (by
          intro i eq
          change (caller (splitter i)).castAdd _ = intervalRecordBank _ (small 24) r k at eq
          change k ≠ small 24 at ne
          change finSumFinEquiv (Sum.inl (caller (splitter i))) = finSumFinEquiv _ at eq
          have contra := finSumFinEquiv.injective eq
          simp [ne] at contra)
        exact ⟨h.1.trans (free r k ne).1,h.2.trans (free r k ne).2⟩)
      (fun i => by
        have h := off (extend ((i.castAdd T).castAdd B)) (fun j => extend.injective.ne (by
          intro eq
          have e := congrArg Fin.val eq
          change 142082+(splitter j).val = i.val at e
          omega))
        exact ⟨h.1.trans (fresh i).1,h.2.trans (fresh i).2⟩)
      (fun i => by
        have h := off (extend (i.natAdd (142082+T))) (fun j => extend.injective.ne (by
          intro eq
          have e := congrArg Fin.val eq
          change 142082+(splitter j).val = 142082+T+i.val at e
          omega))
        exact ⟨h.1.trans (seedReady i).1,h.2.trans (seedReady i).2⟩)
    refine ⟨y,G,t,ran,?_,same,result,?_⟩
    · intro js nd
      have h := bill js nd
      have g := stock js nd
      dsimp only at h
      have g' : tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+entryGrowth := by
        simpa only [entryGrowth,Nat.add_assoc] using g
      have h' : t+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js D+localCost := by
        have group {x a b c d e : ℕ} (le : x ≤ a+b+c+d+e) : x ≤ a+(b+c+d+e) := by omega
        exact group h
      exact h'.trans (Nat.add_le_add_right g' _)
    rintro j ⟨k,rfl,notSplit,notWork⟩
    have h := off _ (fun i => extend.injective.ne (caller.injective.ne (notSplit i)))
    exact ⟨(keep k notSplit notWork).1.trans h.1,(keep k notSplit notWork).2.trans h.2⟩)
  have rawSame (i) := frame (raw i) ⟨source i,rfl,fun j => outside j i,fun j => separate j i⟩
  have payloadF : RecordPayload (raw 24) (fun _ => blank) 0 word F := by
    intro j
    simpa only [(rawSame 24).1,(rawSame 24).2] using payload j
  have portsApart : [raw 60,bank 0,raw 24,raw 61,raw 59].Nodup := by
    rw [targetBank]
    simp [raw.injective.eq_iff]
    exact ⟨(rawOff 0 60).symm,rawOff 0 24,rawOff 0 61,rawOff 0 59⟩
  obtain ⟨v,G,t,done,cost,same,result,stock,clean,keep⟩ := returnIdleBankWithStock_exec host portsApart work unique
    (by rw [targetBank]; exact inside) away word _ z F payloadF read ((rawSame 60).2.trans hc)
    ((rawSame 61).2.trans hs) ((rawSame 59).1.trans tl) ((rawSame 59).2.trans tr)
  have size : RecursiveInterchangeLayout.volume prime wide = V*142080 := by simp [wide,RecursiveInterchangeLayout.volume,V,Nat.mul_assoc]
  have core : CleanupBound S F n ((149*(intervalSplitTapes+5)+13)*volume+34+entryGrowth+localCost) := by
    intro js nd
    have h := paid js nd
    change n+tapeCharge cleanupWeight js F ≤ (149*(intervalSplitTapes+5)+13)*volume+34+(tapeCharge cleanupWeight js S+entryGrowth+localCost) at h
    change n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
    omega
  rw [size] at cost
  have joined := cleanupBound_clearBank work unique core (Nat.le_trans cost (Nat.le_of_eq (Nat.add_comm ..))) clean stock
  refine ⟨v,G,_,exec.seq done,?_,same.trans user,result,clean,?_⟩
  · convert joined using 1; omega
  intro j outside ne hs hd
  have h := keep _ (extend.injective.ne (caller.injective.ne ne)) outside
  have original := frame _ ⟨j,rfl,hs,hd⟩
  exact ⟨h.1.trans original.1,h.2.trans original.2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
