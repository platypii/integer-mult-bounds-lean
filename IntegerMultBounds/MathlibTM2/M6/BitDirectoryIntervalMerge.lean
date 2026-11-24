module

public import IntegerMultBounds.MathlibTM2.M6.BitDirectoryIntervalHeaders
public import IntegerMultBounds.MathlibTM2.M6.BitIntervalChildMerge

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout IntervalDescriptor

/-- Run the prepared child on the cyclic split and merge the transposed owner
streams into the splitter's original target tape. -/
theorem mergedDirectoryInterval {A U : Type} {N T Q : ℕ}
    (i : Fin 9) (j : Fin idleCopies.length)
    (splitter : Fin intervalSplitTapes ↪ Fin T)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (record : Fin 34 ↪ Fin T) (dst : Fin (142081+2) ↪ Fin N)
    (bank : Fin N ↪ Fin (142082+T+N)) (bankFrame : ChildBankFrame ((intervalOwners 142080).trans splitter) bank)
    (scratchOff : ∀ r k, 8 ≤ k.val → ((intervalOwners 142080).trans splitter) r ≠ record k)
    (outer : A → Pr A (intervalHostSize T N) Q prime U) (worker : Pr A (intervalHostSize T N) Q prime U)
    (fields : Fin 6 → Fin T) (h : Fin 12 ↪ Fin T)
    (layout : ∀ k : Fin 6, record (k.castAdd 28) = scheduledHeaderPorts fields h k)
    (off : ∀ k, k ≠ 3 → k ≠ 4 → fields k ≠ h 3 ∧ fields k ≠ h 4)
    (privateOutputs : ∀ k, ((intervalOwners 142080).trans splitter) k ≠ h 3 ∧ ((intervalOwners 142080).trans splitter) k ≠ h 4)
    (headerOff : ∀ k, headers k ≠ h 3 ∧ headers k ≠ h 4)
    (widthOff : width ≠ h 3 ∧ width ≠ h 4) :
    let bounds := idleBounds i idleCopies[j.val].2
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let embed := caller.trans (intervalExtend T N)
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (((intervalOwners 142080).trans splitter).trans caller) (small 24)
    ∃ (code : Pr A (intervalHostSize T N) Q prime U) (merged : Fin intervalSplitTapes ↪ Fin (intervalHostSize T N)), merged 0 = embed (splitter 0) ∧ ∀ (p c : CutoffNodeInput) rate budget,
      c.node = scheduledChild prime p.node (idleDirectoryIndex (i,j)) →
      DirectoryIntervalRun (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2)
        ((intervalOwners 142080).trans splitter) headers width record dst bank outer worker p.w p.idleWidth c rate budget →
      let e := idleInterval i idleCopies[j.val].2
      let lane := phaseIntervalChild (e.1+1) (e.2+1) (p.w+1) p.idleWidth 64
      ∀ target (input : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
        (S.R (embed (h 0))).length = p.w →
        S.R (embed (h 1)) = binSyms (prime^(p.w+1)).size (prime^(p.w+1)) →
        S.R (embed (h 2)) = (Routines.hdr p.node 4).map bitSymbol →
        (∀ k : Fin 12, 3 ≤ k.val → S.R (embed (h k)) = []) →
        (∀ k, k ≠ 3 → k ≠ 4 → S.R (embed (fields k)) = (Routines.hdr (role p.node 142080) k).map bitSymbol) →
        IntervalHeaderInputs (headers.trans embed) (embed width) p.w p.idleWidth S →
        RepT (intervalOwnerBank target input) (embStk (splitter.trans embed) S).L (embStk (splitter.trans embed) S).R →
        (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
        S.R (embed (record 6)) = binSyms c.root.width.size c.cutoff →
        (∀ k ∈ idleRecordWork, S.L (embed (record k)) = [] ∧ S.R (embed (record k)) = []) →
        (∀ k : Fin 142082, let t := intervalExtend T N ((k.castAdd T).castAdd N); S.L t = [] ∧ S.R t = []) →
        (∀ k : Fin N, let t := intervalExtend T N (k.natAdd (142082+T)); S.L t = [] ∧ S.R t = []) →
        let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (input r)
        let word := fun k : Fin (volume prime lane*142080) =>
          let b := finProdFinEquiv.symm k
          SparseRoleCircuit.encode (a := prime) (output b.2 b.1)
        ∃ z F n, Exec outer code (mk u S) n (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F n (512008*p.cells+(rate*intervalLayoutCost U (e.1+1) (e.2+1) p.w p.idleWidth 64+budget)+113+13*(149*(volume prime lane*142080)*(intervalSplitTapes+5)+6)) ∧
          RepT (intervalOwnerBank (putWord target 0 (List.ofFn word)) output)
            (embStk merged F).L (embStk merged F).R ∧
          ∀ t, (∀ k, splitter k ≠ t) → F.L (embed t) = S.L (embed t) ∧ F.R (embed t) = S.R (embed t) := by
  intro bounds caller embed small ports
  let live := (intervalOwners 142080).trans splitter
  let initial := splitter.trans embed
  let saved := (mergeSaved 142080).trans initial
  let returned := ((childReturnFan dst).trans bank).trans (intervalExtend T N)
  have outside i k : live k ≠ splitter (mergeSaved 142080 i) :=
    splitter.injective.ne (mergeSaved_outsideFan _ i k)
  have apart i k : saved i ≠ returned k := (intervalExtend T N).injective.ne
    (bankFrame _ (fun a => outside i _) (childReturnFan dst k)).symm
  let merged := returnedMergeBank saved returned apart
  obtain ⟨call,run⟩ := preparedDirectoryInterval i j live headers width record dst bank bankFrame scratchOff
    outer worker fields h layout off privateOutputs headerOff widthOff
  refine ⟨call.seq (embProg merged Empty.elim (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity))),
    merged,returnedMergeBank_target _ _ _,?_⟩
  intro p c rate budget scheduled child e lane target input u S clock radix middle empty inherited dims split scratch cut free bridge vacant output word
  have size := intervalChild_volume (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2) (p.w+1) p.idleWidth
  have pos : 0 < volume prime lane := size ▸ Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) p.idlePositive
  have fan : HelperFan (live.trans embed) input S :=
    placedOwners (c := 142080) splitter caller (intervalExtend T N) target input S split
  obtain ⟨v,D,n,exec,user,paid,owners,frame⟩ := run p c rate budget scheduled child input u S
    clock radix middle empty inherited dims ((castFan size _ input S).2 fan) scratch cut free bridge vacant
  obtain ⟨z,F,m,finish,time,same,result,_,keep,growth⟩ :=
    placedMergeReturnedOwners_exec outer merged capacity pos target input output (embStk initial S) v D split
      (by rw [returnedMergeBank_owners]; exact (castFan size _ output D).1 owners)
      (by rw [returnedMergeBank_target]; exact frame _ (outside 0))
      (fun k => by dsimp only; rw [returnedMergeBank_inner]; exact frame _ (outside k.succ))
  refine ⟨z,F,_,exec.seq finish,same.trans user,?_,result,?_⟩
  · apply paid.seq
    intro js nd
    have stock := growth js nd
    change tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+12*m at stock
    change m+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+13*(149*(volume prime lane*142080)*(intervalSplitTapes+5)+6)
    omega
  · intro t away
    have prior := frame t (fun k => away _)
    have separate := outsideReturnedMergeBank saved returned apart (j := embed t)
      (fun k => embed.injective.ne (away _))
      (fun k => (intervalExtend T N).injective.ne (bankFrame t (fun a => away _) _))
    exact ⟨(keep _ separate).1.trans prior.1,(keep _ separate).2.trans prior.2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
