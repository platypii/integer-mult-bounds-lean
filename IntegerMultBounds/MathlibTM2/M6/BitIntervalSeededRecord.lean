module

public import IntegerMultBounds.MathlibTM2.M6.BitWorkerIntervalRecord
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderHeaders

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Node Mult.PhaseCellToeplitz
open Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout IntervalDescriptor

local notation "N" => rowSwapBlock.tapes

/-- Seed the recursive bank from the caller’s designated header words, execute the
ordinary-order transpose, and pay the seed load at the actual lane volume. -/
theorem seededIntervalRecord {P U : Type} {T B Q w W atom price lo hi axes fields : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoffWithCharge cleanupWeight ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    (slots : Fin fields ↪ Fin B) (words : Fin fields → List (Fin (prime+4)))
    (headerSource : Fin fields → Fin 72) (seedPrice : ℕ) (seedBill : seedLoadBill words ≤ seedPrice)
    (sourceFree : ∀ i, headerSource i ≠ 59 ∧ headerSource i ≠ 60)
    (leftSeed : ∀ j, seed.L j = []) (headers : ∀ i, seed.R (slots i) = words i)
    (unused : ∀ j, (∀ i, slots i ≠ j) → seed.R j = [])
    (splitter : Fin intervalSplitTapes ↪ Fin T) (directory : Fin 72 ↪ Fin T)
    (apart : ∀ i j, splitter i ≠ directory j) (source : Fin 72 ↪ Fin T)
    (separate : ∀ i j, directory i ≠ source j) (outside : ∀ i j, splitter i ≠ source j)
    (charged : Bool := false) :
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
        S.L j = [] ∧ S.R j = []) →
      (∀ i, S.R (raw (headerSource i)) = words i) →
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
        workerCost charged S F n ((149*(intervalSplitTapes+5)+13)*volume+34+
          (tapeCharge cleanupWeight work S+entryGrowth+localCost)+18*volume+23+seedPrice+(if charged then seedPrice else 0)) ∧
        z.user = u.user ∧ RecordPayload (raw 24) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word) F ∧
        (∀ j ∈ work, F.L j = [] ∧ F.R j = []) ∧
        ∀ j, extend (caller j) ∉ work → j ≠ source 24 → (∀ i, splitter i ≠ j) → (∀ i, directory i ≠ j) →
          F.L (extend (caller j)) = S.L (extend (caller j)) ∧ F.R (extend (caller j)) = S.R (extend (caller j)) := by
  intro live H caller extend initial regs raw small ports lane V wide work unique inside away
  obtain ⟨host,worker,bank,setupRate,passRate,target,run⟩ := recursiveIntervalRecordClean capacity mergeCap
    ordered fits positive widthAt child splitter directory apart source separate outside work unique inside away
  let childBank := (Fin.natAddEmb (142082+T) (m := B)).trans extend
  have disjoint (i : Fin B) (j : Fin T) : childBank i ≠ extend (caller j) := by
    apply extend.injective.ne
    intro eq
    have val := congrArg Fin.val eq
    change 142082+T+i.val = 142082+j.val at val
    omega
  obtain ⟨load,install⟩ := installChildSeed host childBank slots (fun i => raw (headerSource i))
    (raw 59) (raw 60) (fun i j => disjoint _ _) (by
      intro i
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,
        List.nodup_nil,not_false_eq_true,and_true,not_or]
      exact ⟨⟨(disjoint _ _).symm,raw.injective.ne (sourceFree i).1,raw.injective.ne (sourceFree i).2⟩,
        ⟨disjoint _ _,disjoint _ _⟩,raw.injective.ne (by decide)⟩)
  refine ⟨host,load.seq worker,bank,setupRate,passRate,target,?_⟩
  intro word u S payload tl tr hc hs fresh base suffix unit atom dims free front empty sourceWords
    split M pass header volume entryGrowth localCost
  obtain ⟨v,R,k,loaded,user,bill,filled,off⟩ := install seed u S
    (fun i => (sourceWords i).trans (headers i).symm) (fun i => (empty _).2) tr hc
  let D := {S with R := R}
  have keep j : R (extend (caller j)) = S.R (extend (caller j)) := off _ (fun i => disjoint _ _)
  have atRaw i : R (raw i) = S.R (raw i) := keep _
  have record : RecordPayload (raw 24) (fun _ => blank) 0 word D := by
    intro j
    simpa only [D,atRaw] using payload j
  obtain ⟨z,F,n,exec,paid,same,out,cleared,frame⟩ := run word v D record tl ((atRaw _).trans tr)
    ((atRaw _).trans hc) ((atRaw _).trans hs)
    (fun i => ⟨(fresh i).1,(keep _).trans (fresh i).2⟩)
    ((atRaw _).trans base) ((atRaw _).trans suffix) ((atRaw _).trans unit)
    ((congrArg List.length (atRaw _)).trans atom)
    (fun i => ⟨(dims i).1,(keep _).trans (dims i).2⟩)
    (fun r j ne => by
      refine ⟨(free r j ne).1,(off _ ?_).trans (free r j ne).2⟩
      intro i
      exact (intervalRecordBank_outside (live.trans caller) (small 24) ((slots i).natAdd (142082+T))
        (fun h eq => disjoint (slots i) _ (congrArg extend eq.symm)) r j).symm)
    (fun i => by
      refine ⟨(front i).1,(off _ ?_).trans (front i).2⟩
      intro j
      apply extend.injective.ne
      have apartBanks {a b : ℕ} (h : Fin a) (l : Fin b) : h.natAdd b ≠ l.castAdd a := by
        intro eq
        have val := congrArg Fin.val eq
        change b+h.val = l.val at val
        omega
      exact apartBanks (slots j) (i.castAdd T))
    (fun i => ⟨(empty i).1.trans (leftSeed i).symm,filled i (fun h => (empty i).2.trans (unused i h).symm)⟩)
  refine ⟨z,F,k+n,loaded.seq exec,?_,same.trans user,out,cleared,?_⟩
  · have charge := bill work unique
    rw [show (fun i => seed.R (slots i)) = words from funext headers] at charge
    change k+tapeCharge cleanupWeight work D ≤ _ at charge
    have core (js) (nd : js.Nodup) := paid js nd
    cases charged with
    | false =>
      have h := core [] (by simp)
      change n+0 ≤ 0+((149*(intervalSplitTapes+5)+13)*volume+34+
        (tapeCharge cleanupWeight work D+entryGrowth+localCost)+18*volume+23) at h
      change k+n ≤ _
      simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
      omega
    | true =>
      intro js nd
      have h := core js nd
      change n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+
        ((149*(intervalSplitTapes+5)+13)*volume+34+
        (tapeCharge cleanupWeight work D+entryGrowth+localCost)+18*volume+23) at h
      have observed := bill js nd
      rw [show (fun i => seed.R (slots i)) = words from funext headers] at observed
      change k+tapeCharge cleanupWeight js D ≤ _ at observed
      change k+n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
      simp only [ite_true]
      omega
  · intro j miss ne splitOff dirOff
    have h := frame j miss ne splitOff dirOff
    exact ⟨h.1,h.2.trans (keep j)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
