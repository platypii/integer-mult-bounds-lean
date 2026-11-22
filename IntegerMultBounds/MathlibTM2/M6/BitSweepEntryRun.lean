module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepEntryPlacement
public import IntegerMultBounds.MathlibTM2.M6.BitSweepExitReturn

/-! Execute the node-to-sweep conversion directly on the entry chart's payload slots. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover
open Shared50ModularControl (prime)

theorem forwardChartOwners_exec {U : Type} {Q : ℕ} (n : Fin 9) :
    ∃ C : ℕ, ∀ {T : ℕ} {P : Type} (body : P → Pr P T Q prime U) (sw : Fin tapes ↪ Fin T), ∃ code, ∀ w H B W (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ i, IsUnit (parent i)),
      let M := prime^(w+1)
      let N := prime^(64*((w+1)*64))
      M^128 < 2^H → H ≤ M^128+1 → 0 < B → 0 < W → ∀ (x : OwnerArray (w+1) B W) u S,
      ReturnHeaders w H parent W B (embStk sw S).R →
      (∀ r, S.R (sw (owners (sweepRoleTape r))) =
        List.ofFn fun i => SparseRoleCircuit.encode (x (sweepRoleTape r) i)) →
      ∃ z F l, Exec body code (mk u S) l (mk z F) ∧ l ≤ 142080*(C*(M^16*(B*N*(M^112*W)))+8)+1 ∧
        z.user = u.user ∧ F.L = S.L ∧
        (∀ r, F.R (sw (owners (sweepRoleTape r))) = List.ofFn fun i =>
          SparseRoleCircuit.encode (sweepArray parent units n x (sweepRoleTape r) i)) ∧
        ∀ j, (∀ r, sw (owners (sweepRoleTape r)) ≠ j) → F.R j = S.R j := by
  obtain ⟨forward,C,run⟩ := sweepAllocatedOwners_exec (P := Empty) (Q := Q) (U := U) Empty.elim n
  refine ⟨C,?_⟩
  intro T P body sw
  refine ⟨embProg sw Empty.elim forward,?_⟩
  intro w H B W parent units M N hw bound hb width x u S headers input
  obtain ⟨tail,archive⟩ := headers.archive
  obtain ⟨record,row,len,rowLen,prepared⟩ := headers.transpose
  obtain ⟨v,R,l,user,paid,exec,output,frame⟩ := run w H W B parent units tail hw bound width hb x
    (embDn sw u) (embStk sw S) headers.exponent headers.bits headers.unit headers.archiveSize archive headers.blank
    headers.matrixFree headers.rankFree headers.coordFree headers.maskFree headers.recordWidth headers.empty
    headers.gatherFree headers.scanFree record row len rowLen (by
      intro r
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i = 6
      · subst i; exact input r
      exact (prepared r i hi).trans (by fin_cases i <;> first | contradiction | rfl))
  obtain ⟨z,F,placed,_,same,view,off⟩ := exec_emb (ι := (Empty.elim : Empty → P)) (body' := body)
    sw.injective (fun e => nomatch e) exec u rfl S rfl
  have right j := congrArg (fun D : Stacks tapes prime => D.R j) view
  refine ⟨z,F,l,placed,paid,same.trans user,?_,fun r => (right _).trans (output r),?_⟩
  · funext j
    by_cases inside : ∃ i, sw i = j
    · obtain ⟨i,rfl⟩ := inside; exact congrArg (fun D : Stacks tapes prime => D.L i) view
    · exact (off j (not_exists.mp inside)).1
  · intro j hj
    by_cases inside : ∃ i, sw i = j
    · obtain ⟨i,rfl⟩ := inside
      exact (right i).trans (frame i (fun r h => hj r (congrArg sw h)))
    · exact (off j (not_exists.mp inside)).2

/-- Convert the flat owner words, materialize them in the allocated sweep
registers and execute the forward chart route on those very stacks. -/
theorem flatForwardOwners_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (n : Fin 9) (sw : Fin tapes ↪ Fin T)
    (pack : Fin ((Fallback.rowSwapBlock.tapes+35)+142081) ↪ Fin T)
    (capacity : Fallback.rowSwapBlock.states ≤ Q) (tmp : Fin T)
    (separate : ∀ i j, pack i ≠ sw j) (scratch : ∀ i, pack i ≠ tmp)
    (fresh : ∀ i, sw (owners i) ≠ tmp) :
    let src := (Fin.natAddEmb (Fallback.rowSwapBlock.tapes+35) (m := 142081)).trans pack
    ∃ code, ∃ (C : ℝ) (D : ℕ), ∀ w H W, let M := prime^(w+1)
      let V := M^128*W
      M^128 < 2^H → H ≤ M^128+1 → 0 < W →
      ∀ (data : Fin 142081 → Fin V → ZMod 2) u S,
      embStk pack S = helperPackInput w W (embStk src S) →
      RepT (phaseOwners data) (embStk src S).L (embStk src S).R →
      ReturnHeaders w H (fun _ => 1) W 1 (embStk sw S).R →
      S.L tmp = [] → S.R tmp = [] → (∀ i, S.R (sw (owners i)) = []) →
      ∃ z F, ∃ time : ℕ, ∃ y : OwnerArray (w+1) 1 W,
        Exec body code (mk u S) time (mk z F) ∧ z.user = u.user ∧
        (time : ℝ) ≤ C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau +
          ((142080*(D*(M^16*(1*prime^(64*((w+1)*64))*(M^112*W)))+8)+1 : ℕ) : ℝ) ∧
        (∀ r, F.R (sw (owners (sweepRoleTape r))) = List.ofFn fun j =>
          SparseRoleCircuit.encode (y (sweepRoleTape r) j)) ∧
        ∀ r a, y (sweepRoleTape r) (flatToSweep (w+1) W n r a) = data (sweepRoleTape r) a := by
  intro src
  let dest := owners.trans sw
  obtain ⟨prepare,C,load⟩ := flatFrameWords_exec body (List.finRange 142081) (List.nodup_finRange _)
    pack capacity dest tmp (fun i j => separate i _) scratch fresh
  obtain ⟨D,build⟩ := forwardChartOwners_exec (U := U) (Q := Q) n
  obtain ⟨forward,route⟩ := build body sw
  refine ⟨prepare.seq forward,C,D,?_⟩
  intro w H W M V fits width hW data u S init rep headers left right empty
  obtain ⟨v,A,m,out,placed,user,paid,words,off,_,_,frame⟩ := load w W hW data u S init rep left right empty
  let framed : OwnerArray (w+1) 1 W := fun i j => M8.RevMachine.ext (out i) j.val
  have size : M^16*(1*(M^112*W)) = V := by simp only [V,one_mul,← Nat.mul_assoc,← pow_add]
  have ready : ReturnHeaders w H (fun _ => 1) W 1 (embStk sw A).R := headers.of_off (by
    intro j away
    exact (off _ (fun i => separate i j) (fun i h => away i (sw.injective h))).2)
  obtain ⟨z,F,l,exec,bill,same,_,done,_⟩ := route w H 1 W (fun _ => 1) (fun _ => isUnit_one)
    fits width (by decide) hW framed v A ready (fun r => (words _).trans (encodedFrameWord size _).symm)
  refine ⟨z,F,m+l,_,Exec.seq placed exec,same.trans user,?_,done,?_⟩
  · rw [Nat.cast_add]
    exact add_le_add paid (by exact_mod_cast bill)
  · exact sweepArray_flat n data out (fun r a => (frame _ (List.mem_finRange _) a).1)

/-- The complete physical entry from node-order words to the recursive input fan. -/
theorem stageEntry_exec {P U : Type} {Q : ℕ} (n : Fin 9) (fits : 215 ≤ Q) :
    ∃ C : ℕ, ∀ {t : ℕ} (fan : Fin (142081+2) ↪ Fin t), ∀ w H B W (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ i, IsUnit (parent i)),
    let M := prime^(w+1)
    let K := M^112*W
    let A := M^16
    let N := prime^(64*((w+1)*64))
    M^128 < 2^H → H ≤ M^128+1 → 0 < B → 0 < W →
    ∀ (enter : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := A*(B*K)))),
    enter.states ≤ Q → ∀ body : P → Pr P (size t enter.tapes) Q prime U,
    let dst := fan.trans (recursive t enter.tapes)
    let src := (⟨enter.slots,enter.slots_injective⟩ : Fin 142081 ↪ Fin enter.tapes).trans (chart t enter.tapes)
    let pad := padPort fan enter.slots
    let sw := forwardBank (t := t) (⟨enter.slots,enter.slots_injective⟩ : Fin 142081 ↪ Fin enter.tapes)
    ∃ code, ∀ (x : OwnerArray (w+1) B W) u S, ChartPrivateReady enter (embStk (chart t enter.tapes) S) →
      ReturnHeaders w H parent W B (embStk sw S).R →
      (∀ r, S.L (src (sweepRoleTape r)) = []) →
      (∀ r, S.R (src (sweepRoleTape r)) = List.ofFn fun i =>
        SparseRoleCircuit.encode (x (sweepRoleTape r) i)) →
      WordAtZero (x (Fin.last 142080)) (S.L (src (Fin.last 142080))) (S.R (src (Fin.last 142080))) →
      StageControls dst (A*(B*N*K)) S → CropCounters (pad 0) (A*B) N K S →
      (∀ (i : Fin 142081) z, readAt blank (S.L (dst (i.castAdd 2))) (S.R (dst (i.castAdd 2))) z = blank) →
      ∃ z F l, Exec body code (mk u S) l (mk z F) ∧
        l ≤ 142080*(C*(A*(B*N*K))+8)+1 + (enter.cost*(enter.tapes+5)+6 + (142081*(7021*(A*B)*(N*K)+6)+1)) ∧
        z.user = u.user ∧ HelperFan dst (singleLabelBank (B := B) (K := K) (firstRowLabel (w+1)) (enter.transform (sweepArray parent units n x))) F ∧
        ∀ j, (∀ i : Fin 142081, fan (i.castAdd 2) ≠ j) →
          F.L (recursive t enter.tapes j) = S.L (recursive t enter.tapes j) ∧
          F.R (recursive t enter.tapes j) = S.R (recursive t enter.tapes j) := by
  obtain ⟨C,build⟩ := forwardChartOwners_exec (Q := Q) (U := U) n
  refine ⟨C,?_⟩
  intro t fan w H B W parent units M K A N hw bound hb width enter room body dst src pad sw
  let slots := (⟨enter.slots,enter.slots_injective⟩ : Fin 142081 ↪ Fin enter.tapes)
  obtain ⟨forward,convert⟩ := build body sw
  obtain ⟨prepare,pack⟩ := placedEntryCorrection_exec n parent units fan hb width fits enter room body
  refine ⟨forward.seq prepare,?_⟩
  intro x u S ready headers left words extra controls counters empty
  have addr i : sw (owners i) = src i := forwardBank_owner slots i
  obtain ⟨v,D,k,run,paid,user,ls,output,frame⟩ := convert w H B W parent units hw bound hb width x u S headers
    (fun r => (congrArg S.R (addr _)).trans (words r))
  let e := Fintype.equivFin (Register t enter.tapes)
  have recOff j := frame (recursive t enter.tapes j) (fun r => by
    rw [addr]; exact e.injective.ne (show Register.chart _ ≠ .recursive j by intro h; cases h))
  obtain ⟨z,F,l,exec,bill,same,live,off⟩ := pack x v D (by
    intro j hj h
    have eqn := frame (chart t enter.tapes j) (fun r => by
      rw [addr]; exact (chart t enter.tapes).injective.ne (hj _))
    change _ = readAt blank (D.L _) (D.R _) _
    rw [ls,eqn]; exact ready j hj h) (fun r => ls ▸ left r)
    (fun r => (congrArg D.R (addr _)).symm.trans (output r)) (by
      have eqn := frame (src (Fin.last 142080)) (fun r => by
        rw [addr]; apply src.injective.ne; exact Fin.castSucc_ne_last _)
      rw [ls,eqn]; exact extra) (by
      intro j h
      change _ = readAt blank (D.L _) (D.R (recursive t enter.tapes _)) _
      rw [ls,recOff]; exact controls j h) (by
      intro j h d z
      have cell : pad 0 j = e (.crop j) := by
        change e (padReg _ _ _ _) = _; simp [padReg,h,d]
      have eqn := frame (pad 0 j) (fun r => by
        rw [addr,cell]; exact e.injective.ne (show Register.chart _ ≠ .crop j by intro eqn; cases eqn))
      change _ = readAt blank (D.L _) (D.R (pad 0 j)) _
      rw [ls,eqn]; exact counters j h d z) (by
      intro i z
      change readAt blank (D.L _) (D.R (recursive t enter.tapes _)) _ = _
      rw [ls,recOff]; exact empty i z)
  exact ⟨z,F,k+l,Exec.seq run exec,Nat.add_le_add paid bill,same.trans user,live,
    fun j hj => ⟨((off j hj).1).trans (congrFun ls _),((off j hj).2).trans (recOff j)⟩⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
