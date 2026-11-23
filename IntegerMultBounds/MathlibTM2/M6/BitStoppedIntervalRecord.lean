module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalFlatHeaders
public import IntegerMultBounds.MathlibTM2.M6.BitStoppedPackedRecord

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Node Mult.PhaseCellToeplitz
open Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout IntervalDescriptor

local notation "N" => rowSwapBlock.tapes

/-- Run a stopped interval from the ordinary caller headers. The product
register belongs to the cleanup list and is returned empty. -/
theorem stoppedIntervalRecord {U : Type} {Q : ℕ}
    (leafCap : columnCapacity ≤ Q) (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (B : ℕ), 0 ≤ C ∧ ∀ {T w W atom lo hi axes : ℕ},
    lo ≤ hi → hi ≤ axes → 0 < W → 0 < atom →
    (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom →
    ∀ (splitter : Fin intervalSplitTapes ↪ Fin T) (directory : Fin 72 ↪ Fin T)
    (_apart : ∀ i j, splitter i ≠ directory j) (source : Fin 72 ↪ Fin T)
    (_separate : ∀ i j, directory i ≠ source j) (_outside : ∀ i j, splitter i ≠ source j),
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
    ∀ work : List (Fin (H+142080*(N+35))), work.Nodup → initial 0 ∈ work → raw 65 ∈ work → raw 24 ∉ work →
    ∃ (host : Empty ⊕ Empty → Pr (Empty ⊕ Empty) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ Empty) (H+142080*(N+35)) Q prime U)
      (bank : Fin intervalSplitTapes ↪ Fin (H+142080*(N+35))) (setupRate passRate : ℕ),
    bank 0 = initial 0 ∧ ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      RecordPayload (raw 24) (fun _ => blank) 0 word S → S.L (raw 59) = [] → (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (raw i) = []) →
      (∀ i, S.L (initial i) = [] ∧ S.R (initial i) = []) →
      S.R (raw 2) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (raw 53) = binSyms W.size W → S.R (raw 28) = binSyms 1 1 →
      (S.R (raw 71)).length = w+1 →
      (∀ i, S.L (regs i) = [] ∧ S.R (regs i) = []) →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd B)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin B, let j := extend (i.natAdd (142082+T))
        S.L j = [] ∧ S.R j = []) →
      (∀ i, S.R (raw (descriptorPorts i)) = (Routines.hdr lane i).map bitSymbol) →
      let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
        (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) mergeCap))
      let M := prime^(w+1)
      let pass := intervalPassTime U lo hi w W axes
      let header := 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58
      let volume := V*142080
      let entryGrowth := 2*volume+6*(Fast.Main.mnProgPush split*((149*(intervalSplitTapes+5)+5)*volume+24))
      let price := ⌊(C*((64*atom : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)*(V*142080 : ℕ)⌋₊
      let localCost := setupRate*(6*(M.size+W.size)+27*(w+1)+44)+
          passRate*(142080*(header+pass)+1+(142080*pass+1))+
          (142081*(8*V+10+2*V)+1+price)+13*(149*volume*(intervalSplitTapes+5)+6)
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (149*(intervalSplitTapes+5)+13)*volume+34+
          (tapeCharge cleanupWeight work S+entryGrowth+localCost)+18*volume+23+567*V ∧
        z.user = u.user ∧ RecordPayload (raw 24) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word) F ∧
        (∀ j ∈ work, F.L j = [] ∧ F.R j = []) ∧
        ∀ j, extend (caller j) ∉ work → j ≠ source 24 → (∀ i, splitter i ≠ j) → (∀ i, directory i ≠ j) →
          F.L (extend (caller j)) = S.L (extend (caller j)) ∧ F.R (extend (caller j)) = S.R (extend (caller j)) := by
  obtain ⟨C,B,body,code,src,dst,slots,nonneg,_,_,leaf⟩ := stoppedPackedRecord (U := U) leafCap
  refine ⟨C,B,nonneg,?_⟩
  intro T w W atom lo hi axes ordered fits positive active width splitter directory apart source separate outside
    live H caller extend initial regs raw small ports lane V wide work unique inside scratch away
  let count := CopyChildLayout.spectators lane
  let flat := flatNodeDescriptor atom count
  have size : volume prime flat = V := flatSpectatorVolume lane width
  have volumeEq : V = (prime^(w+1))^(axes+axes)*W := intervalChild_volume ordered fits _ _
  have countPos : 0 < count := by
    simp only [count,CopyChildLayout.spectators,lane,phaseIntervalChild,one_mul]
    have hm := pow_pos Shared50ModularControl.prime_prime.pos (w+1)
    exact Nat.mul_pos (Nat.mul_pos (pow_pos hm _) (pow_pos hm _)) (Nat.mul_pos (pow_pos hm _) positive)
  obtain ⟨seed,headers,left,unused,child⟩ := leaf atom count active countPos
  change PackedPieceHandoffWithCharge cleanupWeight (volume prime flat) (packedChildOutput atom _)
    body code src dst seed ⌊(C*((64*atom : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)*(volume prime flat*142080 : ℕ)⌋₊ at child
  rw [size] at child
  let leafPrice := ⌊(C*((64*atom : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)*(V*142080 : ℕ)⌋₊
  change PackedPieceHandoffWithCharge cleanupWeight V (packedChildOutput atom V) body code src dst seed leafPrice at child
  have handoff : PackedPieceHandoffWithCharge cleanupWeight _ (packedChildOutput atom ((prime^(w+1))^(axes+axes)*W)) body code src dst seed leafPrice := volumeEq ▸ child
  have posV : 0 < V := volumeEq ▸ Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive
  have seedBill := descriptorSeedBill flat (size.symm ▸ posV)
  rw [size] at seedBill
  have build := seededIntervalRecord (T := T) (B := B) (Q := Q) (w := w) (W := W) (axes := axes) capacity mergeCap
    ordered fits positive width handoff slots _ intervalFlatSources (133*V) seedBill (by decide) left headers unused
    splitter directory apart source separate outside
  obtain ⟨host,worker,bank,setupRate,passRate,target,run⟩ := build work unique inside away
  refine ⟨host,(middleRowDescriptor (intervalSpectatorPorts.trans raw)).seq worker,bank,setupRate,passRate,target,?_⟩
  intro word u S payload tl free fresh base suffix unit atomWord dims portsFree front empty fields
    split M pass header total entryGrowth price localCost
  obtain ⟨v,D,k,prepare,user,_,words,bill,leftSame,off⟩ := intervalFlatHeaders_exec host raw lo hi (w+1) W axes atom positive
    width u S fields free
  have rawOff (i : Fin 72) (ne : i ≠ 65) := off _ (raw.injective.ne ne)
  have rawRead : RecordPayload (raw 24) (fun _ => blank) 0 word D := by
    intro j
    simpa only [leftSame,rawOff 24 (by decide)] using payload j
  obtain ⟨z,F,n,exec,paid,same,result,clean,frame⟩ := run word v D rawRead (leftSame ▸ tl)
    ((rawOff 59 (by decide)).trans (free _ (by decide) (by decide)))
    ((rawOff 60 (by decide)).trans (free _ (by decide) (by decide)))
    ((rawOff 61 (by decide)).trans (free _ (by decide) (by decide)))
    (fun i => ⟨leftSame ▸ (fresh i).1,(off _ (extend.injective.ne (caller.injective.ne (outside i 65)))).trans (fresh i).2⟩)
    ((rawOff 2 (by decide)).trans base) ((rawOff 53 (by decide)).trans suffix)
    ((rawOff 28 (by decide)).trans unit) ((congrArg List.length (rawOff 71 (by decide))).trans atomWord)
    (fun i => ⟨leftSame ▸ (dims i).1,(off _ (extend.injective.ne (caller.injective.ne (separate i 65)))).trans (dims i).2⟩)
    (fun r j ne => ⟨leftSame ▸ (portsFree r j ne).1,(off _ (intervalRecordBank_outside (live.trans caller) (small 24)
      (caller (source 65)) (fun i => caller.injective.ne (outside _ _)) r j)).trans (portsFree r j ne).2⟩)
    (fun i => ⟨leftSame ▸ (front i).1,(off _ (extend.injective.ne (by
      intro eq
      have h := congrArg Fin.val eq
      change i.val = 142082+(source 65).val at h
      omega))).trans (front i).2⟩)
    (fun i => ⟨leftSame ▸ (empty i).1,(off _ (extend.injective.ne (by
      intro eq
      have h := congrArg Fin.val eq
      change 142082+T+i.val = 142082+(source 65).val at h
      omega))).trans (empty i).2⟩) words
  refine ⟨z,F,k+n,prepare.seq exec,?_,same.trans user,result,clean,?_⟩
  · have loadCost := bill work unique
    have bound := flatSpectators_le_volume lane
    change k+tapeCharge cleanupWeight work D ≤ tapeCharge cleanupWeight work S+434*count at loadCost
    change count ≤ V at bound
    change n ≤ (149*(intervalSplitTapes+5)+13)*total+34+
      (tapeCharge cleanupWeight work D+entryGrowth+localCost)+18*total+23+133*V at paid
    omega
  · intro j miss ne hs hd
    have h := frame j miss ne hs hd
    exact ⟨h.1.trans (congrFun leftSame _),h.2.trans (off _ (fun eq => miss (eq ▸ scratch)))⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
