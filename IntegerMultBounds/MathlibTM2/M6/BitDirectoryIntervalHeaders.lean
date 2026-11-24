module

public import IntegerMultBounds.MathlibTM2.M6.BitDirectoryIntervalCall
public import IntegerMultBounds.MathlibTM2.M6.BitScheduledChildHeaders

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout IntervalDescriptor

def idleRecordWork := (List.finRange 34).filter fun k => k = 3 ∨ k = 4 ∨ 8 ≤ k.val

private theorem memIdleRecordWork (k : Fin 34) :
    k ∈ idleRecordWork ↔ k = 3 ∨ k = 4 ∨ 8 ≤ k.val := by simp [idleRecordWork]

/-- Prepare the scheduled fields before the two layout passes and the recursive
call. Only four inherited role headers enter the caller, together with the
parent middle, atom clock, and radix. -/
theorem preparedDirectoryInterval {A U : Type} {N T Q : ℕ}
    (i : Fin 9) (j : Fin idleCopies.length)
    (live : Fin (142080+2) ↪ Fin T) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (record : Fin 34 ↪ Fin T) (dst : Fin (142081+2) ↪ Fin N)
    (bank : Fin N ↪ Fin (142082+T+N)) (bankFrame : ChildBankFrame live bank)
    (scratchOff : ∀ r k, 8 ≤ k.val → live r ≠ record k)
    (outer : A → Pr A (intervalHostSize T N) Q prime U) (worker : Pr A (intervalHostSize T N) Q prime U)
    (fields : Fin 6 → Fin T) (h : Fin 12 ↪ Fin T)
    (layout : ∀ k : Fin 6, record (k.castAdd 28) = scheduledHeaderPorts fields h k)
    (off : ∀ k, k ≠ 3 → k ≠ 4 → fields k ≠ h 3 ∧ fields k ≠ h 4)
    (privateOutputs : ∀ k, live k ≠ h 3 ∧ live k ≠ h 4)
    (headerOff : ∀ k, headers k ≠ h 3 ∧ headers k ≠ h 4)
    (widthOff : width ≠ h 3 ∧ width ≠ h 4) :
    let bounds := idleBounds i idleCopies[j.val].2
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let embed := caller.trans (intervalExtend T N)
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    ∃ code, ∀ (p c : CutoffNodeInput) rate budget,
      c.node = scheduledChild prime p.node (idleDirectoryIndex (i,j)) →
      DirectoryIntervalRun (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2)
        live headers width record dst bank outer worker p.w p.idleWidth c rate budget →
      let e := idleInterval i idleCopies[j.val].2
      let lane := phaseIntervalChild (e.1+1) (e.2+1) (p.w+1) p.idleWidth 64
      let size := intervalChild_volume (Nat.succ_le_succ bounds.1) (Nat.succ_le_succ bounds.2) (p.w+1) p.idleWidth
      ∀ (input : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
        (S.R (embed (h 0))).length = p.w →
        S.R (embed (h 1)) = binSyms (prime^(p.w+1)).size (prime^(p.w+1)) →
        S.R (embed (h 2)) = (Routines.hdr p.node 4).map bitSymbol →
        (∀ k : Fin 12, 3 ≤ k.val → S.R (embed (h k)) = []) →
        (∀ k, k ≠ 3 → k ≠ 4 → S.R (embed (fields k)) = (Routines.hdr (role p.node 142080) k).map bitSymbol) →
        IntervalHeaderInputs (headers.trans embed) (embed width) p.w p.idleWidth S →
        HelperFan (live.trans embed) (fun r k => input r (k.cast size.symm)) S →
        (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
        S.R (embed (record 6)) = binSyms c.root.width.size c.cutoff →
        (∀ k ∈ idleRecordWork, S.L (embed (record k)) = [] ∧ S.R (embed (record k)) = []) →
        (∀ k : Fin 142082, let t := intervalExtend T N ((k.castAdd T).castAdd N); S.L t = [] ∧ S.R t = []) →
        (∀ k : Fin N, let t := intervalExtend T N (k.natAdd (142082+T)); S.L t = [] ∧ S.R t = []) →
        ∃ z F n, Exec outer code (mk u S) n (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F n (512008*p.cells+(rate*intervalLayoutCost U (e.1+1) (e.2+1) p.w p.idleWidth 64+budget)+113) ∧
          HelperFan (((childReturnFan dst).trans bank).trans (intervalExtend T N))
            (fun r k => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (input r) (k.cast size.symm)) F ∧
          ∀ t, (∀ k, live k ≠ t) → F.L (embed t) = S.L (embed t) ∧ F.R (embed t) = S.R (embed t) := by
  intro bounds caller embed small ports
  let regs := h.trans embed
  obtain ⟨setup,prepare⟩ := prepareScheduledHeaders outer regs (embed ∘ fields) (idleDirectoryIndex (i,j))
    (fun k a b => ⟨embed.injective.ne (off k a b).1,embed.injective.ne (off k a b).2⟩)
  let placement := record.trans embed
  let work := idleRecordWork.map placement
  have distinct : work.Nodup := (by decide : idleRecordWork.Nodup).map placement.injective
  refine ⟨(setup.seq worker).seq (clearWorkTapes work),?_⟩
  intro p c rate budget scheduled run e lane size input u S clock radix middle empty inherited dims fan scratch cut free bridge vacant
  obtain ⟨v,D,n,start,same,paid,ready,keep⟩ := prepare p u S clock radix middle empty inherited
  have kept t (a : t ≠ h 3) (b : t ≠ h 4) := keep (embed t) (embed.injective.ne a) (embed.injective.ne b)
  have field (k : Fin 6) : embed (record (k.castAdd 28)) = scheduledHeaderPorts (embed ∘ fields) regs k := by
    rw [layout]
    fin_cases k <;> rfl
  have slot {k : Fin 34} (a : k ≠ 3) (b : k ≠ 4) : record k ≠ h 3 ∧ record k ≠ h 4 := by
    have x := layout 3
    have y := layout 4
    change record 3 = _ at x
    change record 4 = _ at y
    simp [scheduledHeaderPorts] at x y
    exact ⟨x ▸ record.injective.ne a,y ▸ record.injective.ne b⟩
  obtain ⟨z,F,m,finish,user,bill,output,frame⟩ := run input v D (by
    refine ⟨?_,(kept _ widthOff.1 widthOff.2).2.trans dims.2⟩
    intro k z
    have eq := kept _ (headerOff (copyRecordSources k)).1 (headerOff _).2
    change readAt blank (D.L (embed (headers (copyRecordSources k)))) (D.R (embed (headers (copyRecordSources k)))) _ = _
    rw [eq.1,eq.2]
    exact dims.1 k z)
    (helperFan_of_agree fan (fun k => kept _ (privateOutputs k).1 (privateOutputs k).2))
    (by
      intro r k ne
      have eq := keep (ports r k) (intervalWorkOutside _ _ r k ne (caller (h 3))).symm (intervalWorkOutside _ _ r k ne (caller (h 4))).symm
      exact ⟨eq.1.trans (scratch r k ne).1,eq.2.trans (scratch r k ne).2⟩)
    (fun k => by rw [← scheduled] at ready; exact field k ▸ ready k)
    ((kept _ (slot (by decide) (by decide)).1 (slot (by decide) (by decide)).2).2.trans cut)
    (fun k hk => (kept _ (slot (by omega) (by omega)).1 (slot (by omega) (by omega)).2).2.trans (free k ((memIdleRecordWork k).2 (.inr (.inr hk)))).2)
    (by
      intro k
      have eq := keep (intervalExtend T N ((k.castAdd T).castAdd N)) ((intervalExtend T N).injective.ne ((Fin.castAddEmb N).injective.ne (suffixApart (h 3) k).symm))
        ((intervalExtend T N).injective.ne ((Fin.castAddEmb N).injective.ne (suffixApart (h 4) k).symm))
      exact ⟨eq.1.trans (bridge k).1,eq.2.trans (bridge k).2⟩)
    (by
      intro k
      have eq := keep (intervalExtend T N (k.natAdd (142082+T))) ((intervalExtend T N).injective.ne (suffixApart k ((h 3).natAdd 142082)))
        ((intervalExtend T N).injective.ne (suffixApart k ((h 4).natAdd 142082)))
      exact ⟨eq.1.trans (vacant k).1,eq.2.trans (vacant k).2⟩)
  obtain ⟨q,last,clear⟩ := clearWorkTapes_exec outer work distinct z F
  let G := {F with L := fun k => if k ∈ work then [] else F.L k,
                   R := fun k => if k ∈ work then [] else F.R k}
  have initial k (member : k ∈ work) : S.L k = [] ∧ S.R k = [] := by
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp member
    exact free j hj
  have clean k (member : k ∈ work) : G.L k = [] ∧ G.R k = [] := by simp [G,member]
  have bill' := cleanupBound_clearBank work distinct (paid.seq bill)
    (Nat.le_refl (tapeCharge cleanupWeight work F+1)) clean
    (fun k => by by_cases member : k ∈ work <;> simp [G,member])
  have initialCost : tapeCharge cleanupWeight work S = 112 := by
    unfold tapeCharge
    rw [List.map_congr_left (g := fun _ => 4) (fun k hk => by
      simp [cleanupWeight,(initial k hk).1,(initial k hk).2])]
    simp only [List.map_const',List.sum_replicate_nat,work,List.length_map]
    decide
  rw [initialCost,Nat.add_assoc] at bill'
  have atWidth : record 3 = h 3 := by simpa [scheduledHeaderPorts] using layout 3
  have atMiddle : record 4 = h 4 := by simpa [scheduledHeaderPorts] using layout 4
  refine ⟨q,G,_,(start.seq finish).seq clear,last.trans (user.trans same),?_,?_,?_⟩
  · simpa only [e,tapeCharge,cleanupWeight,Nat.add_assoc,Nat.reduceAdd,Nat.succ_eq_add_one] using bill'
  · apply helperFan_of_agree output
    intro r
    have outside : intervalExtend T N (bank (childReturnFan dst r)) ∉ work := by
      intro member
      obtain ⟨k,hk,eq⟩ := List.mem_map.mp member
      apply bankFrame (record k) _ (childReturnFan dst r) ((intervalExtend T N).injective eq.symm)
      intro a
      rcases (memIdleRecordWork k).1 hk with rfl | rfl | h8
      · exact atWidth ▸ (privateOutputs _).1
      · exact atMiddle ▸ (privateOutputs _).2
      · exact scratchOff _ _ h8
    exact ⟨ite_eq_right outside,ite_eq_right outside⟩
  · intro t offLive
    by_cases member : embed t ∈ work
    · exact ⟨(clean _ member).1.trans (initial _ member).1.symm,(clean _ member).2.trans (initial _ member).2.symm⟩
    have apart k (hk : k ∈ idleRecordWork) : record k ≠ t := by
      intro eq
      exact member (List.mem_map.mpr ⟨k,hk,congrArg embed eq⟩)
    have a := (atWidth ▸ apart 3 (by decide)).symm
    have b := (atMiddle ▸ apart 4 (by decide)).symm
    have f := frame t offLive (fun k h8 => apart k ((memIdleRecordWork k).2 (.inr (.inr h8))))
    exact ⟨(ite_eq_right member).trans (f.1.trans (kept t a b).1),(ite_eq_right member).trans (f.2.trans (kept t a b).2)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
