module

public import IntegerMultBounds.MathlibTM2.M6.BitDirectoryIntervalMerge
public import IntegerMultBounds.MathlibTM2.M6.BitWorkerIntervalRecord

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout IntervalDescriptor

private theorem splitCharge {n final overhead initial growth localCost : ℕ}
    (bound : n+final ≤ overhead+(initial+growth+localCost)) :
    n+final ≤ initial+(overhead+growth+localCost) := by omega

/-- Split the interleaved word, execute the scheduled child, and restore the transposed word on the original payload tape. -/
theorem splitDirectoryInterval {A U : Type} {N T Q : ℕ}
    (i : Fin 9) (j : Fin idleCopies.length)
    (splitter : Fin intervalSplitTapes ↪ Fin T)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (record : Fin 34 ↪ Fin T) (dst : Fin (142081+2) ↪ Fin N)
    (bank : Fin N ↪ Fin (142082+T+N)) (bankFrame : ChildBankFrame ((intervalOwners 142080).trans splitter) bank)
    (outer : A → Pr A (intervalHostSize T N) Q prime U) (worker : Pr A (intervalHostSize T N) Q prime U)
    (fields : Fin 6 → Fin T) (h : Fin 12 ↪ Fin T)
    (layout : ∀ k : Fin 6, record (k.castAdd 28) = scheduledHeaderPorts fields h k)
    (off : ∀ k, k ≠ 3 → k ≠ 4 → fields k ≠ h 3 ∧ fields k ≠ h 4)
    (headerOff : ∀ k, headers k ≠ h 3 ∧ headers k ≠ h 4)
    (widthOff : width ≠ h 3 ∧ width ≠ h 4)
    (src tmp count saved : Fin T) (apart : [count,splitter 0,src,saved,tmp].Nodup)
    (rawOff : ∀ k, splitter k ≠ src ∧ splitter k ≠ tmp ∧ splitter k ≠ count ∧ splitter k ≠ saved)
    (hOff : ∀ k a, splitter k ≠ h a) (fieldsOff : ∀ k a, splitter k ≠ fields a)
    (dimsOff : ∀ k a, splitter k ≠ headers a) (clockOff : ∀ k, splitter k ≠ width)
    (cutOff : ∀ k, splitter k ≠ record 6)
    (workOff : ∀ k a, a ∈ idleRecordWork → splitter k ≠ record a) :
    let bounds := idleBounds i idleCopies[j.val].2
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let embed := caller.trans (intervalExtend T N)
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (((intervalOwners 142080).trans splitter).trans caller) (small 24)
    let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
      (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
    ∀ work : List (Fin (intervalHostSize T N)), work.Nodup → embed (splitter 0) ∈ work → embed src ∉ work →
    ∃ code, ∀ (p c : CutoffNodeInput) rate budget,
      c.node = scheduledChild prime p.node (idleDirectoryIndex (i,j)) →
      DirectoryIntervalRun (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2)
        ((intervalOwners 142080).trans splitter) headers width record dst bank outer worker p.w p.idleWidth c rate budget →
      let e := idleInterval i idleCopies[j.val].2
      let lane := phaseIntervalChild (e.1+1) (e.2+1) (p.w+1) p.idleWidth 64
      let V := volume prime lane
      let wide := {lane with afterD := lane.afterD*142080}
      ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
        RecordPayload (embed src) (fun _ => blank) 0 word S →
        S.R (embed count) = [] → S.R (embed saved) = [] →
        S.L (embed tmp) = [] → S.R (embed tmp) = [] →
        (∀ k, S.L (embed (splitter k)) = [] ∧ S.R (embed (splitter k)) = []) →
        (S.R (embed (h 0))).length = p.w →
        S.R (embed (h 1)) = binSyms (prime^(p.w+1)).size (prime^(p.w+1)) →
        S.R (embed (h 2)) = (Routines.hdr p.node 4).map bitSymbol →
        (∀ k : Fin 12, 3 ≤ k.val → S.R (embed (h k)) = []) →
        (∀ k, k ≠ 3 → k ≠ 4 → S.R (embed (fields k)) = (Routines.hdr (role p.node 142080) k).map bitSymbol) →
        IntervalHeaderInputs (headers.trans embed) (embed width) p.w p.idleWidth S →
        (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
        S.R (embed (record 6)) = binSyms c.root.width.size c.cutoff →
        (∀ k ∈ idleRecordWork, S.L (embed (record k)) = [] ∧ S.R (embed (record k)) = []) →
        (∀ k : Fin 142082, let t := intervalExtend T N ((k.castAdd T).castAdd N); S.L t = [] ∧ S.R t = []) →
        (∀ k : Fin N, let t := intervalExtend T N (k.natAdd (142082+T)); S.L t = [] ∧ S.R t = []) →
        let localCost := 512008*p.cells+(rate*intervalLayoutCost U (e.1+1) (e.2+1) p.w p.idleWidth 64+budget)+113+
          13*(149*(V*142080)*(intervalSplitTapes+5)+6)
        let splitGrowth := 2*(V*142080)+6*(Fast.Main.mnProgPush split*((149*(intervalSplitTapes+5)+5)*(V*142080)+24))
        ∃ z F n, Exec outer code (mk u S) n (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F n ((149*(intervalSplitTapes+5)+13)*(V*142080)+34+splitGrowth+localCost+tapeCharge cleanupWeight work S+(18*volume prime wide+23)) ∧
          RecordPayload (embed src) (fun _ => blank) 0
            (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word) F ∧
          (∀ k ∈ work, F.L k = [] ∧ F.R k = []) ∧
          ∀ t, t ≠ src → embed t ∉ work → (∀ k, splitter k ≠ t) → F.L (embed t) = S.L (embed t) ∧ F.R (embed t) = S.R (embed t) := by
  intro bounds caller embed small ports split work unique inside away
  let initial := splitter.trans embed
  obtain ⟨merge,returned,target,run⟩ := mergedDirectoryInterval i j splitter capacity headers width record dst bank
    bankFrame (fun r k hk => workOff _ k ((List.mem_filter.mpr ⟨List.mem_finRange _,by simp [hk]⟩) : k ∈ idleRecordWork))
    outer worker fields h layout off (fun r => ⟨hOff _ 3,hOff _ 4⟩) headerOff widthOff
  have returnPorts : [embed count,initial 0,embed src,embed saved,embed tmp].Nodup := apart.map embed.injective
  have distinct : [embed src,embed tmp,initial 0].Nodup := by
    have srcTmp : src ≠ tmp := by
      regs_ne apart
      assumption
    simp [initial,embed.injective.eq_iff,srcTmp,(rawOff 0).1.symm,(rawOff 0).2.1.symm]
  let write : Pr A (intervalHostSize T N) Q prime U := (loadCompactWord (initial 0) (embed tmp) (embed count)).seq
    (((Node.usub (embed count) (embed src) (embed tmp)).seq (Mult.PhaseCellToeplitz.movePrefix (embed count) (initial 0) (embed src) (embed saved) (embed tmp))).seq (bclear (embed count)))
  refine ⟨(((loadCompactWord (embed src) (embed tmp) (initial 0)).seq (embProg initial Empty.elim split)).seq merge).seq (write.seq (clearWorkTapes work)),?_⟩
  intro p c rate budget scheduled child e lane V wide word u S payload hc hs tl tr fresh clock radix middle empty inherited dims scratch cut free bridge vacant localCost splitGrowth
  have vol : 0 < V := by
    change 0 < volume prime (phaseIntervalChild _ _ _ _ _)
    rw [intervalChild_volume (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2)]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) p.idlePositive
  let preserved t := ∃ a, t = embed a ∧ ∀ k, splitter k ≠ a
  obtain ⟨z,F,n,exec,paid,user,read,frame⟩ := workerRecordTranspose outer initial returned merge (embed src) (embed tmp)
    distinct capacity lane word u S (fun js => tapeCharge cleanupWeight js S+splitGrowth+localCost)
      (tapeCharge cleanupWeight) preserved vol payload tl tr fresh (by
      intro v D rep keep stock
      have kept t (away : ∀ k, splitter k ≠ t) := keep (embed t) (fun k => embed.injective.ne (away k))
      obtain ⟨q,G,m,ran,same,bill,result,frame⟩ := run p c rate budget scheduled child _ _ v D
        ((congrArg List.length (kept _ (fun k => hOff k 0)).2).trans clock)
        ((kept _ (fun k => hOff k 1)).2.trans radix) ((kept _ (fun k => hOff k 2)).2.trans middle)
        (fun a ha => (kept _ (fun k => hOff k a)).2.trans (empty a ha))
        (fun a b d => (kept _ (fun k => fieldsOff k a)).2.trans (inherited a b d))
        (by
          refine ⟨?_,(kept _ clockOff).2.trans dims.2⟩
          intro a z
          have eq := kept _ (fun k => dimsOff k (copyRecordSources a))
          change readAt blank (D.L (embed (headers (copyRecordSources a)))) (D.R (embed (headers (copyRecordSources a)))) _ = _
          rw [eq.1,eq.2]
          exact dims.1 a z) rep
        (fun r a ne => by
          have eq := keep (ports r a) (fun k => intervalWorkOutside _ _ r a ne (caller (splitter k)))
          exact ⟨eq.1.trans (scratch r a ne).1,eq.2.trans (scratch r a ne).2⟩)
        ((kept _ cutOff).2.trans cut)
        (fun a ha => by
          have eq := kept _ (fun k => workOff k a ha)
          exact ⟨eq.1.trans (free a ha).1,eq.2.trans (free a ha).2⟩)
        (fun a => by
          have eq := keep _ (fun k => (intervalExtend T N).injective.ne ((Fin.castAddEmb N).injective.ne (suffixApart (splitter k) a)))
          exact ⟨eq.1.trans (bridge a).1,eq.2.trans (bridge a).2⟩)
        (fun a => by
          have eq := keep _ (fun k => (intervalExtend T N).injective.ne (suffixApart a ((splitter k).natAdd 142082)).symm)
          exact ⟨eq.1.trans (vacant a).1,eq.2.trans (vacant a).2⟩)
      refine ⟨q,G,m,ran,?_,same,result,?_⟩
      · intro js nd
        have bound := bill js nd
        change m+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js D+localCost at bound
        have growth := stock js nd
        rw [Nat.add_assoc] at growth
        change tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+splitGrowth at growth
        change m+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js S+splitGrowth+localCost
        exact bound.trans (Nat.add_le_add_right growth localCost)
      · rintro _ ⟨t,rfl,away⟩
        exact ⟨(frame t away).1.trans (kept t away).1,(frame t away).2.trans (kept t away).2⟩)
  have core : CleanupBound S F n ((149*(intervalSplitTapes+5)+13)*(V*142080)+34+splitGrowth+localCost) :=
    fun js nd => splitCharge (paid js nd)
  have original := frame _ ⟨src,rfl,fun k => (rawOff k).1⟩
  have source : RecordPayload (embed src) (fun _ => blank) 0 word F := by
    intro k
    simpa only [original.1,original.2] using payload k
  have temp := frame _ ⟨tmp,rfl,fun k => (rawOff k).2.1⟩
  obtain ⟨v,G,m,finish,cost,same,result,stock,clean,keep⟩ := returnIdleBankWithStock_exec outer returnPorts work unique
    inside away word _ z F source (target ▸ read)
    ((frame _ ⟨count,rfl,fun k => (rawOff k).2.2.1⟩).2.trans hc)
    ((frame _ ⟨saved,rfl,fun k => (rawOff k).2.2.2⟩).2.trans hs) (temp.1.trans tl) (temp.2.trans tr)
  have total := cleanupBound_clearBank work unique core (cost.trans (Nat.add_comm ..).le) clean stock
  refine ⟨v,G,_,exec.seq finish,same.trans user,total,result,clean,?_⟩
  intro t ne outside notSplit
  have h := keep _ (embed.injective.ne ne) outside
  have f := frame _ ⟨t,rfl,notSplit⟩
  exact ⟨h.1.trans f.1,h.2.trans f.2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
