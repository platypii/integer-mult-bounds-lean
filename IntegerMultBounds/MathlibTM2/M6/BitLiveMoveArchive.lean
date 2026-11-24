module

public import IntegerMultBounds.MathlibTM2.M6.BitSelectedBandMoves

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Run a two-field worker from a cutoff-only record. The extra tape holds
the computed count during packing and is blank again when the call returns. -/
theorem liveMoveArchive {P U : Type} {T Q N : ℕ} (body : P → Pr P T Q prime U)
    (worker : Pr P T Q prime U) (ports : Fin (N+35) ↪ Fin T) (tmp : Fin T)
    (apart : ∀ i, ports i ≠ tmp) (rank : ℕ) (fits : rank ≤ 8) :
    let bank := scheduledRecordPorts ports
    ∃ code, ∀ (child : Descriptor) (w W L cutoff price : ℕ), 0 < W → child.width = (w+1)*rank →
      let V := (prime^(w+1))^16*W
      volume prime child = V →
      let n := CopyChildLayout.spectators child
      let head := binSyms (A := prime) L cutoff
      let count := binSyms (A := prime) n.size n
      let archive := count ++ separator :: head
      let stored := fun record => RecordReady (b := prime) (w := w) (W := W) (d := 16) bank
        (prime^(w+1)).size W.size record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
      ∀ x u (S : Stacks T prime) (effect : (Fin V → ZMod 2) → Prop), stored head x S → S.R tmp = [] →
      (∀ q A, stored archive x A → (∀ j, A.L j = S.L j) → (∀ j, j ≠ bank 34 → A.R j = S.R j) →
        ∃ z B t y, Exec body worker (mk q A) t (mk z B) ∧ CleanupBound A B t price ∧ z.user = q.user ∧
          stored archive y B ∧ B.R tmp = [] ∧ effect y ∧
          (∀ j, (∀ i, ports i ≠ j) → B.L j = A.L j ∧ B.R j = A.R j) ∧
          (∀ i, 35 ≤ i.val → B.L (ports i) = [] ∧ B.R (ports i) = [])) →
      ∃ z F t y, Exec body code (mk u S) t (mk z F) ∧ CleanupBound S F t (price+30100*V) ∧
        z.user = u.user ∧ stored head y F ∧ effect y ∧
        (∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        (∀ i, 35 ≤ i.val → F.L (ports i) = [] ∧ F.R (ports i) = []) := by
  intro bank
  have away (i : Fin 35) : bank i ≠ tmp := apart _
  obtain ⟨make,compute⟩ := packedSpectatorWord body bank tmp away rank fits
  let put : Pr P T Q prime U := (Prog.act (DFT.pushSep (bank 34))).seq ((moveR tmp (bank 0) id).seq (moveR (bank 0) (bank 34) id))
  refine ⟨make.seq (put.seq (worker.seq ((DFT.takeField (bank 34) tmp (bank 0)).seq (bclear tmp)))),?_⟩
  intro child w W L cutoff price rows width V mass n head count archive stored x u S effect ready empty call
  let D := {S with R := Function.update S.R tmp count}
  obtain ⟨a,k,start,user,setup⟩ := compute child w W rows width mass u S x head ready empty
  have same (i : Fin 35) : D.R (bank i) = S.R (bank i) := Function.update_of_ne (away i) ..
  have readyD := ready.returnPayload (F := D) (outBank := bank) (output := x) (fun i _ => ⟨rfl,same i⟩)
    (fun j => by simpa only [same] using (ready.src j).symm)
  obtain ⟨b,pack,bu,packed⟩ := restoreMoveArchive body bank tmp away w W L cutoff n x a D readyD (Function.update_self ..)
  let A := {D with R := Function.update (Function.update D.R (bank 34) archive) tmp []}
  have keep j (hj : j ≠ bank 34) : A.R j = S.R j := by
    by_cases eq : j = tmp <;> simp [A,D,eq,hj,empty]
  obtain ⟨z,B,m,y,run,paid,zu,out,vacant,action,frame,clear⟩ := call b A packed (fun _ => rfl) keep
  obtain ⟨v,unpack,vu,opened,saved⟩ := unpackMoveArchive body bank tmp away w W L cutoff n y z B out vacant
  let E := {B with R := Function.update (Function.update B.R (bank 34) head) tmp count}
  obtain ⟨f,fu,_,erase⟩ := bclear_exec body tmp v E
  let F := {E with R := Function.update E.R tmp []}
  have len : (E.R tmp).length = n.size := by simp [E,count]
  rw [len] at erase
  have off j (hj : j ≠ bank 34) : F.R j = B.R j := by
    by_cases eq : j = tmp <;> simp [F,E,eq,hj,vacant]
  have unchanged (i : Fin 35) : F.R (bank i) = E.R (bank i) := Function.update_of_ne (away i) ..
  refine ⟨f,F,_,y,start.seq (pack.seq (run.seq (unpack.seq erase))),?_,fu.trans (vu.trans (zu.trans (bu.trans user))),?_,action,?_,?_⟩
  · have bill := workerCost.updateRight (charged := true) paid (bank 34) head (packed.archive.trans out.archive.symm)
    have reset : ({A with R := Function.update A.R (bank 34) head} : Stacks T prime) = S := by
      refine Stacks.ext ?_ ?_ ?_ ?_ <;> try rfl
      funext j
      by_cases eq : j = bank 34
      · subst j; simpa using ready.archive.symm
      · exact (Function.update_of_ne eq ..).trans (keep j eq)
    have final : ({B with R := Function.update B.R (bank 34) head} : Stacks T prime) = F := by
      refine Stacks.ext ?_ ?_ ?_ ?_ <;> try rfl
      funext j
      by_cases eq : j = bank 34
      · subst j; simp [F,E,away]
      · exact (Function.update_of_ne eq ..).trans (off j eq).symm
    rw [reset,final] at bill
    have elapsed : k ≤ 30000*V := by simpa [tapeCharge] using setup [] (by simp)
    have sn : n ≤ V := by
      rw [← mass]
      have eq : volume prime child = (prime^child.width*prime^child.width)*n := by dsimp [volume,n,CopyChildLayout.spectators]; ring
      rw [eq]; exact Nat.le_mul_of_pos_left _ (by have := Shared50ModularControl.prime_prime.pos; positivity)
    have digits : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    have pos : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) rows
    intro js nd
    have cost := bill js nd
    change m+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+price at cost
    change k+(4*n.size+5+(m+(4*n.size+5+(2*n.size+2))))+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+_
    omega
  · exact opened.returnPayload (fun i _ => ⟨rfl,unchanged i⟩) (fun j => by simpa only [unchanged] using (opened.src j).symm)
  · intro j outside
    have ne := (outside _ : bank 34 ≠ j).symm
    exact ⟨(frame j outside).1,(off j ne).trans ((frame j outside).2.trans (keep j ne))⟩
  · intro i hi
    have ne : ports i ≠ bank 34 := ports.injective.ne (fun eq => by have h := congrArg Fin.val eq; change i.val = 34 at h; exact (Nat.not_lt_of_ge hi) (h ▸ (by decide : (34 : ℕ) < 35)))
    exact ⟨(clear i hi).1,(off _ ne).trans (clear i hi).2⟩


open Certificates.PR589 Certificates.PR589.Nine

/-- Selected MOVE calls on the phase's cutoff-only record. The temporary
register is supplied by the caller and restored by the frame guarantee. -/
theorem selectedLiveBandMoves {U : Type} (stage : Fin 9) (run : StageRun) (afterCopy : Bool) :
    let _ := BinaryRadixEqualShared.supplierNet
    let J := Fin (selectedPhaseSchedule afterCopy).1.length
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ N : ℕ, ∀ {H : ℕ} (port : J → Fin (N+35) ↪ Fin H) (tmp : Fin H),
      (∀ j i, port j i ≠ tmp) →
      ∃ (P : J → Type) (tables : ∀ j, P j → Pr (P j) H Q prime U) (codes : ∀ j, Pr (P j) H Q prime U) (rate : ℕ),
      ∀ (p : CutoffNodeInput) (blocks : ℕ) (j : J),
        let i := phaseChildPositions.choose (stage,run,selectedPhaseIndex afterCopy j)
        let ports := port j
        let table := tables j
        let code := codes j
        let child := scheduledChild prime p.node i
        let V := (prime^(p.w+1))^16*p.stageWidth
        let archive := binSyms p.root.width.size p.cutoff
        p.root.Positive → 142080^(p.depth+1) ∣ p.root.rows →
        p.root.beforeH = blocks*prime^(64*p.root.width) →
        49*(p.w+1) ≤ 64*p.cutoff →
        ∃ position : Fin (volume prime child) ≃ Fin V,
          (∀ j, (position j).val = (CopyChildLayout.packActive child j).val) ∧
          let price := cutoffTreeBudget D leafRate p.cutoff (p.depth-(p.path.length+1)) child
          let bank := scheduledRecordPorts ports
          let stored := RecordReady (b := prime) (w := p.w) (W := p.stageWidth) (d := 16) bank
            (prime^(p.w+1)).size p.stageWidth.size archive SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
          let clean := fun S : Stacks H prime => ∀ j : Fin (N+35), 35 ≤ j.val → S.L (ports j) = [] ∧ S.R (ports j) = []
          ∀ u S word, stored word S → clean S → S.R tmp = [] →
            ∃ z F t y, Exec table code (mk u S) t (mk z F) ∧
              CleanupBound S F t (price+rate*p.cells) ∧
              z.user = u.user ∧ stored y F ∧ clean F ∧
              (∀ j, (∀ k, ports k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
              ∀ h, y (position h) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h := by
  intro inst J
  classical
  obtain ⟨states,compile⟩ := selectedBandMoves (U := U) stage run afterCopy
  refine ⟨states,?_⟩
  intro Q enough
  obtain ⟨minimum,leaf,build⟩ := compile enough
  refine ⟨minimum,leaf,?_⟩
  intro D large
  obtain ⟨N,place⟩ := build D large
  refine ⟨N,?_⟩
  intro H port tmp apart
  obtain ⟨P,tables,codes,rate,call⟩ := place port
  let rank (j : J) := nodeChildren5[(phaseChildPositions.choose (stage,run,selectedPhaseIndex afterCopy j)).val]
  have fits (j : J) : rank j ≤ 8 := (phaseChildRank_le stage run (selectedPhaseIndex afterCopy j)).trans (by decide)
  choose wrapped dispatch using fun j => liveMoveArchive (tables j) (codes j) (port j) tmp (apart j) (rank j) (fits j)
  refine ⟨P,tables,wrapped,rate+30100,?_⟩
  intro p blocks j i ports table code child V archive root rows label band
  obtain ⟨position,packed,runWorker⟩ := call p blocks j root rows label band
  refine ⟨position,packed,?_⟩
  intro price bank stored clean u S word ready free empty
  have mass : volume prime child = V := (scheduledChildVolume p i).trans p.stageCells.symm
  have width : child.width = (p.w+1)*rank j := by
    change nodeChildren5[i.val]*(p.node.width/64) = _
    rw [p.width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
  have positive : 0 < p.stageWidth := by
    have cells : 0 < p.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
      (Nat.mul_pos p.idlePositive (by decide))
    exact Nat.pos_of_mul_pos_left (p.stageCells ▸ cells)
  obtain ⟨z,F,t,y,exec,paid,user,out,action,frame,fresh⟩ :=
    dispatch j child p.w p.stageWidth p.root.width.size p.cutoff (price+rate*p.cells)
      positive width mass word u S (fun y => ∀ h, y (position h) =
        Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) h) ready empty (by
          intro q A prepared left right
          have clear : clean A := by
            intro k hk
            have ne : ports k ≠ bank 34 := ports.injective.ne (fun eq => by
              have h := congrArg Fin.val eq
              change k.val = 34 at h
              exact (Nat.not_lt_of_ge hk) (h ▸ (by decide : (34 : ℕ) < 35)))
            exact ⟨(left _).trans (free k hk).1,(right _ ne).trans (free k hk).2⟩
          obtain ⟨z,B,t,y,exec,paid,user,out,fresh,frame,action⟩ := runWorker q A word prepared clear
          have ne : tmp ≠ bank 34 := (apart j _).symm
          exact ⟨z,B,t,y,exec,paid,user,out,(frame tmp (apart j)).2.trans ((right tmp ne).trans empty),
            action,frame,fresh⟩)
  refine ⟨z,F,t,y,exec,?_,user,out,fresh,frame,action⟩
  simpa only [V,p.stageCells,Nat.add_mul,Nat.add_assoc] using paid

end IntegerMultBounds.MathlibTM2.M6.BitNode
