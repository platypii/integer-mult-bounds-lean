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
      ∀ (word : Fin (volume prime wide) → ZMod 2) u S price,
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
        ∃ z F t, Exec body merge (mk v D) t (mk z F) ∧ t ≤ price ∧ z.user = v.user ∧
          RepT (intervalOwnerBank (putWord target 0 (List.ofFn output)) rows) (embStk returned F).L (embStk returned F).R ∧
          ∀ j, preserved j → F.L j = S.L j ∧ F.R j = S.R j) →
      ∃ z F t, Exec body (((loadCompactWord src tmp (splitter 0)).seq (embProg splitter Empty.elim split)).seq merge)
        (mk u S) t (mk z F) ∧ t ≤ (149*(intervalSplitTapes+5)+13)*(V*142080)+34+price ∧
        z.user = u.user ∧ RecordPayload (returned 0) (fun _ => blank) 0
          (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word) F ∧
        ∀ j, preserved j → F.L j = S.L j ∧ F.R j = S.R j := by
  intro split lane V wide size word u S price input target data rows output preserved positive source tl tr empty run
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
  obtain ⟨a,D,k,prepare,initial,paid,rep,off⟩ := splitEncoded_exec body splitter capacity positive input v B
    (Function.update_self ..) (fun i => (empty i).1)
    (fun i ne => (Function.update_of_ne (splitter.injective.ne ne) ..).trans (empty i).2)
  obtain ⟨z,F,t,ran,bill,same,result,frame⟩ := run a D rep (fun j away =>
    ⟨(off j away).1,(off j away).2.trans (Function.update_of_ne (away 0).symm ..)⟩)
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
  simp only [Nat.add_mul] at paid ⊢
  omega

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
  obtain ⟨z,F,n,exec,paid,user,read,frame⟩ := wrapper word u S _ preserved vol payload tl tr freshSplit (by
    intro v D rep off
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
    refine ⟨y,G,t,ran,bill,same,result,?_⟩
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
  obtain ⟨v,G,back,same,result,_,left,right⟩ := returnIdlePayloadFromBlank_exec host portsApart word _ z F
    payloadF read ((rawSame 60).2.trans hc) ((rawSame 61).2.trans hs)
    ((rawSame 59).1.trans tl) ((rawSame 59).2.trans tr)
  have size : volume prime wide = V*142080 := by simp [wide,volume,V,Nat.mul_assoc]
  refine ⟨v,G,_,exec.seq back,by rw [size]; exact Nat.add_le_add_right paid _,same.trans user,result,?_⟩
  intro j ne hs hd
  have keep := frame _ ⟨j,rfl,hs,hd⟩
  have original := right (extend (caller j)) (extend.injective.ne (caller.injective.ne ne))
    (by rw [targetBank]; exact extend.injective.ne (caller.injective.ne (hs 0).symm))
  exact ⟨(left _).trans keep.1,original.trans keep.2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
