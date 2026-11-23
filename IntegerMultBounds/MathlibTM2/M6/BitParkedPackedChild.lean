module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatNodeHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitDescriptorRecurrence

/-! Prepare exact words for a packed recursive entry and read its returned fan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)
open M8.RevMachine

theorem packedRowEntry {T N Q : ℕ} {P A U : Type} (body : P → Pr P N Q prime U)
    (host : A → Pr A T Q prime U) (place : Fin N ↪ Fin T) (label : P → A)
    (installed : ∀ p, host (label p) = embProg place label (body p))
    (live : Fin (142080+2) ↪ Fin T) (src dst : Fin (142081+2) ↪ Fin N) (tmp : Fin T)
    (apart : ∀ (r : Fin 142080) (i : Fin 142081), live (r.castAdd 2) ≠ place (src (i.castAdd 2)))
    (srcTmp : ∀ r : Fin 142080, live (r.castAdd 2) ≠ tmp)
    (dstTmp : ∀ i : Fin 142081, place (src (i.castAdd 2)) ≠ tmp)
    (controls : ∀ j : Fin 2, place (src (j.natAdd 142081)) = live (j.natAdd 142080))
    (entry : P) :
    let privatePorts := (List.finRange N).filter (fun j => ∀ i, childReturnFan dst i ≠ j)
    let scratch := privatePorts.map place
    ∃ code : Pr A T Q prime U, ∀ (lane : Descriptor) (seed : Stacks N prime) price,
      let V := volume prime lane
      PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ r : Fin 142080,
        y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
        body (body entry) src dst seed price →
      ∀ (data : Fin 142080 → Fin V → ZMod 2) u S, HelperFan live data S →
      S.L tmp = [] → S.R tmp = [] →
      (∀ i : Fin 142081, S.L (place (src (i.castAdd 2))) = [] ∧ S.R (place (src (i.castAdd 2))) = []) →
      (∀ j, (∀ i, src i ≠ j) → S.L (place j) = seed.L j ∧ S.R (place j) = seed.R j) →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧ t ≤ tapeCharge cleanupWeight scratch S + 142081*(8*V+10+2*V)+1+price+3 ∧
        z.user = u.user ∧ HelperFan ((childReturnFan dst).trans place) (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)) F ∧
        (∀ j, (∀ i, childReturnFan dst i ≠ j) → F.L (place j) = [] ∧ F.R (place j) = []) ∧
        ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro privatePorts scratch
  have distinct : scratch.Nodup := ((List.nodup_finRange N).filter _).map place.injective
  have mem (j : Fin N) : place j ∈ scratch ↔ ∀ i, childReturnFan dst i ≠ j := by
    simp [scratch,privatePorts,place.injective.eq_iff]
  have retain (i) : place (childReturnFan dst i) ∉ scratch := fun h => (mem _).mp h i rfl
  obtain ⟨prep,prepare⟩ := prepareChildOwners_exec host live (src.trans place) tmp apart srcTmp dstTmp
  refine ⟨(prep.seq (.call (label entry))).seq (clearWorkTapes scratch),?_⟩
  intro lane seed price V child data u S represented left right empty privateTapes
  obtain ⟨v,R,a,setup,paid,user,words,keep,prepBill⟩ := prepare data u S represented controls left right empty
  let D := {S with R := R}
  have physical := words.next place src (fun _ => rfl) (fun _ => rfl)
  obtain ⟨z,F,b,y,run,cost,final,out,effect⟩ := child _ (embDn place v) (embStk place D) physical (by
    intro j off
    exact ⟨(privateTapes j off).1,(keep (place j) (fun i => place.injective.ne (off (i.castAdd 2)))).trans (privateTapes j off).2⟩)
  obtain ⟨q,G,lifted,_,same,view,frame⟩ := exec_emb place.injective installed run v rfl D rfl
  have called := Exec.call (installed entry ▸ lifted : Exec host (host (label entry)) (mk v D) b (mk q G))
  obtain ⟨last,lastUser,erase⟩ := clearWorkTapes_exec host scratch distinct q G
  have childBill := placedCleanup_cost_le place D G cleanupWeight b price frame
    (view ▸ cost) scratch distinct
  have before := prepBill cleanupWeight (2*V) (by
    intro word length
    simp [cleanupWeight,length,Nat.add_comm]) scratch distinct
  refine ⟨last,_,_,(setup.seq called).seq erase,?_,lastUser.trans (same.trans (final.trans user)),?_,?_,?_⟩
  · change a+(b+2)+(tapeCharge cleanupWeight scratch G+1) ≤ _
    change a+tapeCharge cleanupWeight scratch D ≤ _ at before
    omega
  · rw [← view] at out
    have rows : (fun r : Fin 142080 => y r.castSucc) = fun r =>
        Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r) := by
      funext r
      simpa only [Function.comp_apply,Fin.lastCases_castSucc,id_eq] using effect r
    rw [← rows]
    have rep := ParentStageWords.returnFan (bank := place) (F := G) out
    intro i z
    simpa only [embStk,Function.comp_apply,Function.Embedding.trans_apply,ite_eq_right (retain i)] using rep i z
  · intro j away
    simp only [ite_eq_left ((mem j).mpr away),and_self]
  · intro j off
    have away : j ∉ scratch := fun h => by
      obtain ⟨i,_,eq⟩ := List.mem_map.mp h
      exact off i eq
    simpa only [ite_eq_right away] using
      And.intro (frame j off).1 ((frame j off).2.trans (keep j (fun i => off (src (i.castAdd 2)))))

/-- Reload private right-stack words from persistent caller tapes. A source
may supply several seed ports, and both copy temporaries are reusable. -/
theorem reloadChildSeed {k T Q : ℕ} {A U : Type} (host : A → Pr A T Q prime U)
    (target : Fin k ↪ Fin T) (source : Fin k → Fin T) (tmp saved : Fin T)
    (apart : ∀ i j, target i ≠ source j)
    (regs : ∀ i, [source i,target i,tmp,saved].Nodup) :
    ∃ code : Pr A T Q prime U, ∀ (seed : Fin k → List (Fin (prime+4))) u S,
      (∀ i, S.R (source i) = seed i) → (∀ i, S.R (target i) = []) →
      S.R tmp = [] → S.R saved = [] →
      ∃ z R t, Exec host code (mk u S) t (mk z {S with R := R}) ∧
        t ≤ ((List.finRange k).map fun i => 6*(seed i).length+6).sum+1 ∧
        z.user = u.user ∧ (∀ i, R (target i) = seed i) ∧
        ∀ j, (∀ i, target i ≠ j) → R j = S.R j := by
  let copy : Fin k → Pr A T Q prime U := fun i => bcopy (source i) (target i) tmp saved
  refine ⟨Cover.LabelTraversal.sequence copy (List.finRange k),?_⟩
  intro seed u S words empty tl tr
  obtain ⟨z,R,t,user,paid,exec,loaded,keep⟩ := distinctTapeSequence host target copy
    (List.finRange k) (List.nodup_finRange k) (fun _ => []) seed (fun i => 6*(seed i).length+6)
    u S empty (by
      intro i v D _ vacant off
      have tmpOff (j) : target j ≠ tmp := by
        have h := regs j
        simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
        tauto
      have savedOff (j) : target j ≠ saved := by
        have h := regs j
        simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
        tauto
      obtain ⟨q,same,run⟩ := bcopy_exec host (regs i) v D ((off _ tmpOff).trans tl) ((off _ savedOff).trans tr)
      have word := (off _ (fun j => apart j i)).trans (words i)
      rw [word,vacant,List.append_nil] at run
      exact ⟨q,_,same,le_rfl,run⟩)
  exact ⟨z,R,t,exec,paid,user,fun i => loaded i (List.mem_finRange i),fun j h => keep j (fun i _ => h i)⟩

private theorem loadedSeedCharge {k T : ℕ} (target : Fin k ↪ Fin T)
    (S : Stacks T prime) (R : Fin T → List (Fin (prime+4)))
    (words : Fin k → List (Fin (prime+4))) (loaded : ∀ i, R (target i) = words i)
    (off : ∀ j, (∀ i, target i ≠ j) → R j = S.R j)
    (js : List (Fin T)) (distinct : js.Nodup) :
    tapeCharge cleanupWeight js {S with R := R} ≤ tapeCharge cleanupWeight js S +
      ∑ i, 2*(words i).length := by
  rw [← Nat.zero_add (tapeCharge cleanupWeight js {S with R := R})]
  apply placedCleanup_cost_le target S {S with R := R} cleanupWeight 0 _ (fun j h => ⟨rfl,off j h⟩) _ js distinct
  intro is unique
  simp only [Nat.zero_add,tapeCharge,embStk,Function.comp_apply,loaded]
  rw [← List.sum_toFinset _ unique,← List.sum_toFinset _ unique]
  calc
    _ ≤ ∑ i ∈ is.toFinset, (cleanupWeight (S.L (target i)) (S.R (target i)) + 2*(words i).length) := by
      apply Finset.sum_le_sum
      intro i _
      unfold cleanupWeight
      omega
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) _

def seedLoadBill {k : ℕ} (words : Fin k → List (Fin (prime+4))) : ℕ :=
  (∑ i, (8*(words i).length+6))+1

theorem descriptorSeedBill (v : Descriptor) (positive : 0 < volume prime v) :
    seedLoadBill (fun i => (Routines.hdr v i).map bitSymbol) ≤ 133*volume prime v := by
  let V := volume prime v
  have each (i : Fin 6) : 8*((Routines.hdr v i).map (bitSymbol (a := prime))).length+6 ≤ 16*V+6 := by
    have bound := RecursiveRowsNode.header_length v (M8.RevMachine.LeafCore.positive_of_volume positive)
      _ (Routines.hdr_headers v) i
    simp only [List.length_map]
    dsimp only [V]
    omega
  have total := Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at total
  simp only [seedLoadBill]
  dsimp only [V] at total
  omega

/-- Charge the six physical descriptor words once for each scheduled occurrence,
using the actual volume of the child even when its spectator coordinates differ. -/
theorem scheduledSeedBill (parent : Descriptor) (width : 64 ∣ parent.width)
    (rows : 142080 ∣ parent.rows) (positive : 0 < volume prime parent)
    (lanes : Fin nodeChildren5.length → Descriptor)
    (size : ∀ i, volume prime (lanes i) = volume prime (scheduledChild prime parent i)) :
    (∑ i, seedLoadBill (fun j => (Routines.hdr (lanes i) j).map bitSymbol))*142080 ≤
      nodeChildren5.length*133*volume prime parent := by
  have piece (i) : volume prime (lanes i)*142080 = volume prime parent := by
    rw [size]
    exact (scheduledChild_measures prime parent width rows i).2
  have each (i) := Nat.mul_le_mul_right 142080
    (descriptorSeedBill (lanes i) (Nat.pos_of_mul_pos_right ((piece i).symm ▸ positive)))
  rw [Finset.sum_mul]
  simpa only [Nat.mul_assoc,piece,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    using Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i)

open scoped Classical in
theorem seededPackedRowEntry {k T N Q : ℕ} {P A U : Type} (body : P → Pr P N Q prime U)
    (host : A → Pr A T Q prime U) (place : Fin N ↪ Fin T) (label : P → A)
    (installed : ∀ p, host (label p) = embProg place label (body p))
    (live : Fin (142080+2) ↪ Fin T) (src dst : Fin (142081+2) ↪ Fin N) (tmp : Fin T)
    (apart : ∀ (r : Fin 142080) (i : Fin 142081), live (r.castAdd 2) ≠ place (src (i.castAdd 2)))
    (srcTmp : ∀ r : Fin 142080, live (r.castAdd 2) ≠ tmp)
    (dstTmp : ∀ i : Fin 142081, place (src (i.castAdd 2)) ≠ tmp)
    (controls : ∀ j : Fin 2, place (src (j.natAdd 142081)) = live (j.natAdd 142080))
    (slots : Fin k ↪ Fin N) (master : Fin k → Fin T) (aux : Fin T)
    (privateSlots : ∀ i j, slots i ≠ src j)
    (ownerOff : ∀ i j, place (slots i) ≠ live j)
    (masterOff : ∀ i j, place (slots i) ≠ master j)
    (regs : ∀ i, [master i,place (slots i),tmp,aux].Nodup) (entry : P) :
    let privatePorts := (List.finRange N).filter (fun j => ∀ i, childReturnFan dst i ≠ j)
    let scratch := privatePorts.map place
    ∃ code : Pr A T Q prime U, ∀ (lane : Descriptor) (seed : Stacks N prime) price,
      let V := volume prime lane
      PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ r : Fin 142080,
        y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
        body (body entry) src dst seed price →
      ∀ (data : Fin 142080 → Fin V → ZMod 2) u S, HelperFan live data S →
      S.L tmp = [] → S.R tmp = [] →
      (∀ i : Fin 142081, S.L (place (src (i.castAdd 2))) = [] ∧ S.R (place (src (i.castAdd 2))) = []) →
      S.R aux = [] → (∀ i, S.R (master i) = seed.R (slots i)) →
      (∀ i, S.R (place (slots i)) = []) →
      (∀ j, (∀ i, src i ≠ j) → S.L (place j) = seed.L j ∧
        ((∀ i, slots i ≠ j) → S.R (place j) = seed.R j)) →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧ t ≤ tapeCharge cleanupWeight scratch S +
          seedLoadBill (fun i => seed.R (slots i)) + 142081*(8*V+10+2*V)+1+price+3 ∧
        z.user = u.user ∧ HelperFan ((childReturnFan dst).trans place) (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)) F ∧
        (∀ j, (∀ i, childReturnFan dst i ≠ j) → F.L (place j) = [] ∧ F.R (place j) = []) ∧
        ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  classical
  intro privatePorts scratch
  obtain ⟨load,loadRun⟩ := reloadChildSeed host (slots.trans place) master tmp aux masterOff regs
  obtain ⟨call,callRun⟩ := packedRowEntry body host place label installed live src dst tmp apart srcTmp dstTmp controls entry
  refine ⟨load.seq call,?_⟩
  intro lane seed price V child data u S liveRows tl tr empty auxFree masters vacant prepared
  obtain ⟨v,R,a,setup,paid,user,loaded,off⟩ := loadRun (fun i => seed.R (slots i)) u S masters vacant tr auxFree
  let D := {S with R := R}
  have rows : HelperFan live data D := by
    intro i z
    simpa only [D,embStk,Function.comp_apply,off _ (fun j => ownerOff j i)] using liveRows i z
  have temp (i) : place (slots i) ≠ tmp := by
    have h := regs i
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    tauto
  obtain ⟨z,F,b,run,cost,final,result,clean,frame⟩ := callRun lane seed price child data v D rows tl
    ((off _ temp).trans tr)
    (fun i => ⟨(empty i).1,(off _ (fun j => place.injective.ne (privateSlots j _))).trans (empty i).2⟩)
    (by
      intro j outside
      refine ⟨(prepared j outside).1,?_⟩
      by_cases h : ∃ i, slots i = j
      · obtain ⟨i,rfl⟩ := h
        exact loaded i
      · have away := fun i eq => h ⟨i,eq⟩
        exact (off _ (fun i => place.injective.ne (away i))).trans ((prepared j outside).2 away))
  refine ⟨z,F,_,setup.seq run,?_,final.trans user,result,clean,?_⟩
  · have distinct : scratch.Nodup := ((List.nodup_finRange N).filter _).map place.injective
    have growth := loadedSeedCharge (slots.trans place) S R _ loaded off scratch distinct
    change tapeCharge cleanupWeight scratch D ≤ tapeCharge cleanupWeight scratch S +
      ∑ i, 2*(seed.R (slots i)).length at growth
    change b ≤ tapeCharge cleanupWeight scratch D + 142081*(8*V+10+2*V)+1+price+3 at cost
    rw [← List.sum_toFinset _ (List.nodup_finRange k)] at paid
    have allSlots : (List.finRange k).toFinset = Finset.univ := by ext; simp
    rw [allSlots] at paid
    have combined : (∑ i, (6*(seed.R (slots i)).length+6)) + (∑ i, 2*(seed.R (slots i)).length) =
        ∑ i, (8*(seed.R (slots i)).length+6) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      omega
    simp only [seedLoadBill]
    omega
  · intro j outside
    exact ⟨(frame j outside).1,(frame j outside).2.trans (off j (fun i => outside (slots i)))⟩

theorem descriptorPackedRowEntry {T N Q : ℕ} {P A U : Type} (body : P → Pr P N Q prime U)
    (host : A → Pr A T Q prime U) (place : Fin N ↪ Fin T) (label : P → A)
    (installed : ∀ p, host (label p) = embProg place label (body p))
    (live : Fin (142080+2) ↪ Fin T) (src dst : Fin (142081+2) ↪ Fin N) (tmp : Fin T)
    (apart : ∀ (r : Fin 142080) (i : Fin 142081), live (r.castAdd 2) ≠ place (src (i.castAdd 2)))
    (srcTmp : ∀ r : Fin 142080, live (r.castAdd 2) ≠ tmp)
    (dstTmp : ∀ i : Fin 142081, place (src (i.castAdd 2)) ≠ tmp)
    (controls : ∀ j : Fin 2, place (src (j.natAdd 142081)) = live (j.natAdd 142080))
    (sameControls : ∀ j : Fin 2, dst (j.natAdd 142081) = src (j.natAdd 142081))
    (slots : Fin 6 ↪ Fin N) (master : Fin 6 → Fin T) (aux : Fin T)
    (privateSlots : ∀ i j, slots i ≠ src j)
    (ownerOff : ∀ i j, place (slots i) ≠ live j)
    (masterOff : ∀ i j, place (slots i) ≠ master j)
    (regs : ∀ i, [master i,place (slots i),tmp,aux].Nodup) (entry : P) :
    ∃ code : Pr A T Q prime U, ∀ (lane : Descriptor) (seed : Stacks N prime) price,
      let V := volume prime lane
      0 < V → (∀ i, seed.R (slots i) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j, (∀ i, src i ≠ j) → seed.L j = [] ∧ ((∀ i, slots i ≠ j) → seed.R j = [])) →
      PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ r : Fin 142080,
        y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
        body (body entry) src dst seed price →
      ∀ (data : Fin 142080 → Fin V → ZMod 2) u S, HelperFan live data S →
      S.L tmp = [] → S.R tmp = [] →
      S.R aux = [] → (∀ i, S.R (master i) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j, (∀ i : Fin 2, src (i.natAdd 142081) ≠ j) → S.L (place j) = [] ∧ S.R (place j) = []) →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧
        t ≤ price+(4*N+133+142081*20+4)*V ∧
        z.user = u.user ∧ HelperFan ((childReturnFan dst).trans place) (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)) F ∧
        (∀ j, (∀ i, childReturnFan dst i ≠ j) → F.L (place j) = [] ∧ F.R (place j) = []) ∧
        ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  classical
  obtain ⟨code,run⟩ := seededPackedRowEntry body host place label installed live src dst tmp apart
    srcTmp dstTmp controls slots master aux privateSlots ownerOff masterOff regs entry
  refine ⟨code,?_⟩
  intro lane seed price V pos headers seedBlank child data u S represented tl tr auxFree words free
  have rowsFree (r : Fin 142081) := free (src (r.castAdd 2)) (fun i => src.injective.ne (by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_natAdd,Fin.val_castAdd] at h
    omega))
  obtain ⟨z,F,t,exec,cost,user,out,clean,frame⟩ := run lane seed price child data u S represented tl tr
    rowsFree auxFree (fun i => (words i).trans (headers i).symm)
    (fun i => (free _ (fun j => (privateSlots i _).symm)).2) (by
      intro j off
      have blank := free j (fun i => off _)
      have h := seedBlank j off
      exact ⟨blank.1.trans h.1.symm,fun away => blank.2.trans (h.2 away).symm⟩)
  refine ⟨z,F,t,exec,?_,user,out,clean,frame⟩
  let ps := (List.finRange N).filter (fun j => ∀ i, childReturnFan dst i ≠ j)
  have charge : tapeCharge cleanupWeight (ps.map place) S = ps.length*4 := by
    unfold tapeCharge
    rw [List.map_map]
    have each (j : Fin N) (mem : j ∈ ps) :
        cleanupWeight (S.L (place j)) (S.R (place j)) = 4 := by
      have off := of_decide_eq_true (List.mem_filter.mp mem).2
      have blank := free j (fun i => by
        have eq := childReturnFan_control dst i
        rw [sameControls] at eq
        exact eq ▸ off (i.natAdd 142080))
      simp [cleanupWeight,blank]
    simp only [Function.comp_def]
    rw [List.map_congr_left (fun j hj => each j hj)]
    simp
  change t ≤ tapeCharge cleanupWeight (ps.map place) S + seedLoadBill _ +
    142081*(8*V+10+2*V)+1+price+3 at cost
  rw [charge,show (fun i => seed.R (slots i)) = _ from funext headers] at cost
  have hdr := descriptorSeedBill lane pos
  have count : ps.length ≤ N := (List.length_filter_le ..).trans_eq List.length_finRange
  have room : 4*N ≤ 4*N*V := Nat.le_mul_of_pos_right _ pos
  change 0 < V at pos
  change seedLoadBill _ ≤ 133*V at hdr
  rw [Nat.add_mul,Nat.add_mul,Nat.add_mul]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
