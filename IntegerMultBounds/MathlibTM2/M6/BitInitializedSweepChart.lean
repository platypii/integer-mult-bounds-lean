module

public import IntegerMultBounds.MathlibTM2.M6.BitChartInitialization

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open M8.RevMachine Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Execute every role's chart on its scheduled row. Workspaces may overlap
because each single-row program restores every tape except its live owner. -/
theorem initializedSweepChartList [M8.Machine.Net] (n : Fin 9) (backward : Bool) :
    ∃ machine : Role → SharedBankSkeleton.Skeleton 1 prime,
    ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
      (chart : ∀ r, Fin ((machine r).tapes+35) ↪ Fin T)
      (ports : Role → Fin (rowSwapBlock.tapes+35) ↪ Fin T) (precision : Fin T),
      let regs := fun r => scheduledRecordPorts (ports r)
      let owner := fun r => regs r 24
      (∀ r, (machine r).states ≤ Q) → (∀ r i j, chart r i ≠ ports r j) →
      (∀ r i, chart r i ≠ precision) → (∀ r, owner r ≠ precision) →
      (∀ r s i, chart r i ≠ owner s) →
      (∀ r s, r ≠ s → ∀ i, regs r i ≠ owner s) →
      ∀ jobs : List Role, jobs.Nodup →
      ∃ (C : ℝ) (code : Pr P T Q prime U), ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
        let M := prime^(w+1)
        let V := M^128*W
        ∀ (record : Role → List (Fin (prime+4))) (x : Role → Fin V → ZMod 2),
        let ready := fun r y D => RecordReady (b := prime) (w := w) (d := 128) (W := W) (regs r)
          M.size W.size (record r) SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 y D
        (∀ r, ready r (x r) S) → S.R precision = binSyms (w+1).size (w+1) →
        (∀ r ∈ jobs, ∀ i, S.L (chart r i) = [] ∧ S.R (chart r i) = []) →
        ∃ z F t, ∃ y : Role → Fin V → ZMod 2, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
          (∀ js : List (Fin T), js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤
            tapeCharge cleanupWeight js S+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
          (∀ r, ready r (y r) F) ∧
          (∀ r ∈ jobs, ∀ i, routedCell backward (x r) (y r) i
            ((flatToSweep (w+1) W n r i).cast (by simpa only [Nat.one_mul] using ordinaryCompact_width M W))) ∧
          (∀ r ∉ jobs, y r = x r) ∧
          ∀ j, (∀ r ∈ jobs, owner r ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  classical
  choose machine c k build using fun r => initializedSweepChart n r backward
  refine ⟨machine,?_⟩
  intro P U T Q body chart ports precision regs owner capacity apart external clock safe separate jobs unique
  choose rate code run using fun r => build r body (capacity r) (chart r) (ports r) precision (apart r) (external r)
  choose coeff bound using fun r => recordChartCost_bound (rate r) (c r) (k r) (machine r).tapes
  induction jobs with
  | nil =>
    refine ⟨1,.act .done,?_⟩
    intro w W pos u S M V record x ready stored prec free
    refine ⟨u,S,1,x,Exec.act .done _,rfl,?_,stored,by simp,by simp,fun _ _ => ⟨rfl,rfl⟩⟩
    intro js nd
    have vol : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos
    have power : 1 ≤ ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau := Real.one_le_rpow
      (by exact_mod_cast Nat.le_add_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le
    have paid := one_le_mul_of_one_le_of_one_le (show (1 : ℝ) ≤ V by exact_mod_cast vol) power
    simpa only [Nat.cast_one,one_mul,add_comm] using add_le_add_left paid (tapeCharge cleanupWeight js S : ℝ)
  | cons r jobs ih =>
    obtain ⟨C,rest,exec⟩ := ih unique.tail
    refine ⟨coeff r+C,(code r).seq rest,?_⟩
    intro w W pos u S M V record x ready stored prec free
    obtain ⟨v,D,t,startWord,start,user,paid,out,action,off⟩ := run r w W pos u S (record r) (x r)
      (stored r) prec (free r List.mem_cons_self)
    let next := Function.update x r startWord
    have current s : ready s (next s) D := by
      by_cases eq : s = r
      · subst s; simpa [next] using out
      · rw [show next s = x s from Function.update_of_ne eq ..]
        have frame i := off (regs s i) (separate s r eq i)
        apply (stored s).returnPayload (fun i _ => frame i)
        intro h
        rw [(frame 24).1,(frame 24).2]
        exact ((stored s).src h).symm
    obtain ⟨z,F,m,y,finish,last,charge,done,move,unchanged,frame⟩ :=
      exec w W pos v D record next current ((off precision (clock r).symm).2.trans prec) (by
        intro s hs i
        have e := off (chart s i) (safe s r i)
        have blank := free s (List.mem_cons_of_mem _ hs) i
        exact ⟨e.1.trans blank.1,e.2.trans blank.2⟩)
    refine ⟨z,F,t+m,y,start.seq finish,last.trans user,?_,done,?_,?_,?_⟩
    · intro js nd
      have time := Nat.cast_le (α := ℝ).mpr (paid js nd)
      have vol : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) pos
      have cost := bound r (w+1) V (by omega) vol
      change ((t+tapeCharge cleanupWeight js D : ℕ) : ℝ) ≤
        ((tapeCharge cleanupWeight js S+recordChartCost (rate r) (c r) (k r) (machine r).tapes (w+1) V : ℕ) : ℝ) at time
      rw [Nat.cast_add,Nat.cast_add] at time
      rw [Nat.cast_add t m]
      have tailCost := charge js nd
      change (m : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+
        C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau at tailCost
      linarith only [time,cost,tailCost]
    · intro s hs
      rcases List.mem_cons.mp hs with eq|mem
      · subst s
        rw [unchanged r unique.notMem,show next r = startWord from Function.update_self ..]
        exact action
      · have ne : s ≠ r := fun eq => unique.notMem (eq ▸ mem)
        simpa only [next,Function.update_of_ne ne] using move s mem
    · intro s hs
      have ne : s ≠ r := fun eq => hs (eq ▸ List.mem_cons_self)
      exact (unchanged s (fun h => hs (List.mem_cons_of_mem _ h))).trans (Function.update_of_ne ne ..)
    · intro j outside
      have a := off j (outside r List.mem_cons_self).symm
      have b := frame j (fun s h => outside s (List.mem_cons_of_mem _ h))
      exact ⟨b.1.trans a.1,b.2.trans a.2⟩

/-- The complete finite role bank, with one coefficient for the whole sweep chart. -/
theorem initializedSweepChartBank [M8.Machine.Net] (n : Fin 9) (backward : Bool) :
    ∃ machine : Role → SharedBankSkeleton.Skeleton 1 prime,
    ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
      (chart : ∀ r, Fin ((machine r).tapes+35) ↪ Fin T)
      (ports : Role → Fin (rowSwapBlock.tapes+35) ↪ Fin T) (precision : Fin T),
      let regs := fun r => scheduledRecordPorts (ports r)
      let owner := fun r => regs r 24
      (∀ r, (machine r).states ≤ Q) → (∀ r i j, chart r i ≠ ports r j) →
      (∀ r i, chart r i ≠ precision) → (∀ r, owner r ≠ precision) →
      (∀ r s i, chart r i ≠ owner s) →
      (∀ r s, r ≠ s → ∀ i, regs r i ≠ owner s) →
      ∃ (C : ℝ) (code : Pr P T Q prime U), ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
        let M := prime^(w+1)
        let V := M^128*W
        ∀ (record : Role → List (Fin (prime+4))) (x : Role → Fin V → ZMod 2),
        let ready := fun r y D => RecordReady (b := prime) (w := w) (d := 128) (W := W) (regs r)
          M.size W.size (record r) SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 y D
        (∀ r, ready r (x r) S) → S.R precision = binSyms (w+1).size (w+1) →
        (∀ r i, S.L (chart r i) = [] ∧ S.R (chart r i) = []) →
        ∃ z F t, ∃ y : Role → Fin V → ZMod 2, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
          (∀ js : List (Fin T), js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤
            tapeCharge cleanupWeight js S+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
          (∀ r, ready r (y r) F) ∧
          (∀ r i, routedCell backward (x r) (y r) i
            ((flatToSweep (w+1) W n r i).cast (by simpa only [Nat.one_mul] using ordinaryCompact_width M W))) ∧
          ∀ j, (∀ r, owner r ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  classical
  let e := Fintype.equivFin Role
  let jobs := (List.finRange (Fintype.card Role)).map e.symm
  have mem r : r ∈ jobs := List.mem_map.mpr ⟨e r,List.mem_finRange _,e.symm_apply_apply _⟩
  obtain ⟨machine,build⟩ := initializedSweepChartList n backward
  refine ⟨machine,?_⟩
  intro P U T Q body chart ports precision regs owner capacity apart external clock safe separate
  obtain ⟨C,code,run⟩ := build body chart ports precision capacity apart external clock safe separate jobs
    ((List.nodup_finRange _).map e.symm.injective)
  refine ⟨C,code,?_⟩
  intro w W pos u S M V record x ready stored prec free
  obtain ⟨z,F,t,y,exec,user,paid,out,action,_,off⟩ := run w W pos u S record x stored prec (fun r _ => free r)
  exact ⟨z,F,t,y,exec,user,paid,out,fun r => action r (mem r),fun j away => off j (fun r _ => away r)⟩

/-- Every role borrows the same record headers and the same chart workspace.
Only slot 24 follows the selected owner. -/
theorem sharedRecordSweepChart [M8.Machine.Net] (n : Fin 9) (backward : Bool) :
    ∃ space states : ℕ, ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
      (work : Fin space ↪ Fin T) (recordBank : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
      (owners : Role ↪ Fin T) (precision : Fin T),
      states ≤ Q → (∀ i j, work i ≠ recordBank j) → (∀ i r, work i ≠ owners r) →
      (∀ j r, recordBank j ≠ owners r) → (∀ i, work i ≠ precision) → (∀ r, owners r ≠ precision) →
      ∃ (C : ℝ) (code : Pr P T Q prime U), ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
        let M := prime^(w+1)
        let V := M^128*W
        ∀ (x : Role → Fin V → ZMod 2),
        (∀ i, i.val ≠ 24 → let seed := moveRecordSeed w W [] [] []
          S.L (recordBank i) = seed.L i ∧ S.R (recordBank i) = seed.R i) →
        (∀ r, RecordPayload (owners r) (fun _ => blank) 0 (x r) S) →
        S.R precision = binSyms (w+1).size (w+1) → (∀ i, S.L (work i) = [] ∧ S.R (work i) = []) →
        ∃ z F t, ∃ y : Role → Fin V → ZMod 2, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
          (∀ js : List (Fin T), js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤
            tapeCharge cleanupWeight js S+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
          (∀ r, RecordPayload (owners r) (fun _ => blank) 0 (y r) F) ∧
          (∀ r i, routedCell backward (x r) (y r) i
            ((flatToSweep (w+1) W n r i).cast (by simpa only [Nat.one_mul] using ordinaryCompact_width M W))) ∧
          ∀ j, (∀ r, owners r ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  classical
  obtain ⟨machine,build⟩ := initializedSweepChartBank n backward
  obtain ⟨space,fits⟩ := Finite.exists_le fun r => (machine r).tapes+35
  obtain ⟨states,qs⟩ := Finite.exists_le fun r => (machine r).states
  refine ⟨space,states,?_⟩
  intro P U T Q body work recordBank owners precision capacity apart safe outside ext clock
  let charts r := (Fin.castLEEmb (fits r)).trans work
  let idx := Fin.castLEEmb (Nat.le_add_left 35 rowSwapBlock.tapes)
  let ports r := chartLivePorts recordBank (idx 24) (owners r) (fun i => outside i r)
  have owner r : scheduledRecordPorts (ports r) 24 = owners r := by
    simp [scheduledRecordPorts,ports,chartLivePorts,idx]
  have other r i (ne : i ≠ 24) : scheduledRecordPorts (ports r) i = scheduledRecordPorts recordBank i := by
    change (if idx i = idx 24 then owners r else recordBank (idx i)) = _
    rw [ite_eq_right (idx.injective.ne ne)]
    rfl
  obtain ⟨C,code,run⟩ := build body charts ports precision (fun r => (qs r).trans capacity) (by
    intro r i j
    change work _ ≠ (if j = idx 24 then owners r else recordBank j)
    split
    · exact safe _ _
    · exact apart _ _) (fun r i => ext _) (fun r => by change scheduledRecordPorts (ports r) 24 ≠ precision; rw [owner]; exact clock r) (fun r s i => by change charts r i ≠ scheduledRecordPorts (ports s) 24; rw [owner]; exact safe _ _) (by
      intro r s ne i
      change scheduledRecordPorts (ports r) i ≠ scheduledRecordPorts (ports s) 24
      rw [owner s]
      by_cases eq : i = 24
      · subst i; rw [owner]; exact owners.injective.ne ne
      · rw [other r i eq]; exact outside _ _)
  refine ⟨C,code,?_⟩
  intro w W pos u S M V x stock payload prec free
  obtain ⟨z,F,t,y,exec,user,paid,out,action,frame⟩ := run w W pos u S (fun _ => []) x (by
    intro r
    have stored (i : Fin 35) (ne : i ≠ 24) := stock (idx i) (by
      change i.val ≠ 24
      exact fun eq => ne (Fin.ext eq))
    have cell i (ne : i ≠ 24) :
        S.L (scheduledRecordPorts (ports r) i) = (moveRecordSeed w W [] [] []).L (idx i) ∧
        S.R (scheduledRecordPorts (ports r) i) = (moveRecordSeed w W [] [] []).R (idx i) := by
      rw [other r i ne]
      exact stored i ne
    refine ⟨(cell 2 (by decide)).2,(cell 27 (by decide)).2,(cell 28 (by decide)).2,
      (cell 32 (by decide)).2,?_,(cell 34 (by decide)).2,?_,?_,?_⟩
    · rw [(cell 33 (by decide)).2]; exact List.length_replicate ..
    · intro i hi
      have clean := (by decide : ∀ j ∈ shearWork, j.val ≠ 2 ∧ j.val ≠ 24 ∧ j.val ≠ 25 ∧
        j.val ≠ 27 ∧ j.val ≠ 28 ∧ j.val ≠ 32 ∧ j.val ≠ 33 ∧ j.val ≠ 34) i hi
      obtain ⟨a,b,c,d,e,f,g,h⟩ := clean
      simpa [idx,moveRecordSeed,a,b,c,d,e,f,g,h] using cell i (fun eq => b (congrArg Fin.val eq))
    · intro h
      rw [owner]
      simpa only [List.map_ofFn] using payload r h
    · intro h
      rw [(cell 25 (by decide)).1,(cell 25 (by decide)).2]
      change readAt blank [] [] _ = _
      simp [readAt]
      rfl) prec (fun r i => free _)
  refine ⟨z,F,t,y,exec,user,paid,?_,action,?_⟩
  · intro r h
    rw [← owner r]
    simpa only [List.map_ofFn] using (out r).src h
  · intro j away
    exact frame j (fun r => by change scheduledRecordPorts (ports r) 24 ≠ j; rw [owner]; exact away r)

/-- Apply the sweep chart to the permanent owner fan, preserving the last
row and both controls. The represented output can enter the next fan worker. -/
theorem initializedSweepFan [M8.Machine.Net] (n : Fin 9) (backward : Bool) :
    ∃ space states : ℕ, ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
      (work : Fin space ↪ Fin T) (recordBank : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
      (fan : Fin (142081+2) ↪ Fin T) (precision : Fin T),
      let owners := sweepRoleTape.trans ((Fin.castAddEmb 2).trans fan)
      states ≤ Q → (∀ i j, work i ≠ recordBank j) → (∀ i r, work i ≠ owners r) →
      (∀ j r, recordBank j ≠ owners r) → (∀ i, work i ≠ precision) → (∀ r, owners r ≠ precision) →
      ∃ (C : ℝ) (code : Pr P T Q prime U), ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
        let M := prime^(w+1)
        let V := M^128*W
        ∀ (x : Fin 142081 → Fin V → ZMod 2),
        (∀ i, i.val ≠ 24 → let seed := moveRecordSeed w W [] [] []
          S.L (recordBank i) = seed.L i ∧ S.R (recordBank i) = seed.R i) →
        HelperFan fan x S →
        S.R precision = binSyms (w+1).size (w+1) → (∀ i, S.L (work i) = [] ∧ S.R (work i) = []) →
        ∃ z F t, ∃ y : Fin 142081 → Fin V → ZMod 2, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
          (∀ js : List (Fin T), js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤
            tapeCharge cleanupWeight js S+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
          HelperFan fan y F ∧
          (∀ r i, routedCell backward (x (sweepRoleTape r)) (y (sweepRoleTape r)) i
            ((flatToSweep (w+1) W n r i).cast (by simpa only [Nat.one_mul] using ordinaryCompact_width M W))) ∧
          y (Fin.last 142080) = x (Fin.last 142080) ∧
          ∀ j, (∀ r, owners r ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  classical
  obtain ⟨space,states,build⟩ := sharedRecordSweepChart n backward
  refine ⟨space,states,?_⟩
  intro P U T Q body work recordBank fan precision owners capacity apart safe outside ext clock
  obtain ⟨C,code,run⟩ := build body work recordBank owners precision capacity apart safe outside ext clock
  refine ⟨C,code,?_⟩
  intro w W pos u S M V x stored live prec free
  obtain ⟨z,F,t,rows,exec,user,paid,payload,action,keep⟩ := run w W pos u S
    (x ∘ sweepRoleTape) stored (fun r => fanPayload live _) prec free
  let y := Function.extend sweepRoleTape rows x
  have atRole r : y (sweepRoleTape r) = rows r := sweepRoleTape.injective.extend_apply _ _ _
  have elsewhere j (off : ∀ r, sweepRoleTape r ≠ j) : y j = x j := by
    simp [y,show ¬ ∃ r, sweepRoleTape r = j from fun ⟨r,h⟩ => off r h]
  refine ⟨z,F,t,y,exec,user,paid,?_,fun r i => (atRole r).symm ▸ action r i,
    elsewhere _ (fun r => Fin.castSucc_ne_last _),keep⟩
  have encoded (a : Fin 142081 → Fin V → ZMod 2) j : SparseRoleCircuit.encoded (a := prime) a j = fun k => SparseRoleCircuit.encode (a j k) := rfl
  intro i
  refine Fin.addCases (fun j h => ?_) (fun j h => ?_) i
  · by_cases hit : ∃ r, sweepRoleTape r = j
    · obtain ⟨r,rfl⟩ := hit
      have cell := payload r h
      rw [encodedOwnerCell] at cell
      simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,
        encoded,atRole,owners,Function.Embedding.trans_apply,Fin.castAddEmb_apply] using cell.symm
    · have off r : sweepRoleTape r ≠ j := fun eq => hit ⟨r,eq⟩
      have eq := keep (fan (j.castAdd 2)) (fun r => fan.injective.ne ((Fin.castAddEmb 2).injective.ne (off r)))
      simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,
        encoded,elsewhere j off,eq.1,eq.2] using live (j.castAdd 2) h
  · have disjoint {m n : ℕ} (a : Fin m) (b : Fin n) : a.castAdd n ≠ b.natAdd m := by
      intro eq
      have val := congrArg Fin.val eq
      change a.val = m+b.val at val
      omega
    have eq := keep (fan (j.natAdd 142081)) (fun r => fan.injective.ne (disjoint (sweepRoleTape r) j))
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,eq.1,eq.2]
      using live (j.natAdd 142081) h

/-- Build the single shared record from the caller's modulus, spectator
count, unit and precision before running the full fan chart. -/
theorem prepareSweepFan [M8.Machine.Net] (n : Fin 9) (backward : Bool) :
    ∃ space states : ℕ, ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
      (workspace : Fin (rowSwapBlock.tapes+35+space) ↪ Fin T) (caller : Fin 6 ↪ Fin T)
      (fan : Fin (142081+2) ↪ Fin T),
      let owners := sweepRoleTape.trans ((Fin.castAddEmb 2).trans fan)
      states ≤ Q → (∀ i j, workspace i ≠ fan j) → (∀ i j, workspace i ≠ caller j) →
      (∀ r, owners r ≠ caller 3) →
      ∃ (C : ℝ) (code : Pr P T Q prime U), ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
        let M := prime^(w+1)
        let V := M^128*W
        ∀ x : Fin 142081 → Fin V → ZMod 2, HelperFan fan x S →
        S.R (caller 0) = binSyms M.size M → S.R (caller 1) = binSyms W.size W →
        S.R (caller 2) = binSyms 1 1 → S.R (caller 3) = binSyms (w+1).size (w+1) →
        S.R (caller 4) = [] → S.R (caller 5) = [] →
        (∀ i, S.L (workspace i) = [] ∧ S.R (workspace i) = []) →
        ∃ z F t, ∃ y : Fin 142081 → Fin V → ZMod 2, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
          (∀ js : List (Fin T), js.Nodup → (t : ℝ)+tapeCharge cleanupWeight js F ≤
            tapeCharge cleanupWeight js S+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
          HelperFan fan y F ∧
          (∀ r i, routedCell backward (x (sweepRoleTape r)) (y (sweepRoleTape r)) i
            ((flatToSweep (w+1) W n r i).cast (by simpa only [Nat.one_mul] using ordinaryCompact_width M W))) ∧
          y (Fin.last 142080) = x (Fin.last 142080) ∧
          (∀ i : Fin (rowSwapBlock.tapes+35), i.val ≠ 24 → let seed := moveRecordSeed w W [] [] []
            F.L (workspace (i.castAdd space)) = seed.L i ∧ F.R (workspace (i.castAdd space)) = seed.R i) ∧
          (∀ i : Fin space, let j := workspace (i.natAdd (rowSwapBlock.tapes+35))
            F.L j = [] ∧ F.R j = []) ∧
          ∀ j, (∀ r, owners r ≠ j) → (∀ i, workspace i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨space,states,build⟩ := initializedSweepFan n backward
  refine ⟨space,states,?_⟩
  intro P U T Q body workspace caller fan owners capacity fanOff callerOff clock
  let recBank := (Fin.castAddEmb space).trans workspace
  let work := (Fin.natAddEmb (rowSwapBlock.tapes+35)).trans workspace
  have apart i j : work i ≠ recBank j := workspace.injective.ne (by
    intro eq
    have val := congrArg Fin.val eq
    change rowSwapBlock.tapes+35+i.val = j.val at val
    omega)
  let src := fun i : Fin 3 => caller (i.castAdd 3)
  obtain ⟨setup,init⟩ := loadWorkerRecordSeed body recBank src (caller 3) (caller 4) (caller 5)
    (fun i => (callerOff _ _).symm) (fun i j => callerOff _ _) (by
      intro i
      have distinct (s : Fin 6) (a : s ≠ 4) (b : s ≠ 5) (j) :
          [caller s,workspace j,caller 4,caller 5].Nodup := by
        simp [List.nodup_cons,caller.injective.eq_iff,(callerOff j s).symm,callerOff j,a,b]
      exact distinct _ (by fin_cases i <;> decide) (by fin_cases i <;> decide) _)
  obtain ⟨C,code,run⟩ := build body work recBank fan (caller 3) capacity apart (fun _ _ => fanOff _ _)
    (fun _ _ => fanOff _ _) (fun _ => callerOff _ _) clock
  refine ⟨98+C,setup.seq code,?_⟩
  intro w W pos u S M V x live modulus spectators unit prec tmp saved vacant
  obtain ⟨v,D,t,start,user,paid,seed,off⟩ := init w W u S modulus spectators unit prec
    (fun _ _ => vacant _) tmp saved
  have kept j := off (fan j) (fun _ _ => fanOff _ _)
  have liveD : HelperFan fan x D := by
    intro i h
    simpa only [embStk,Function.comp_apply,(kept i).1,(kept i).2] using live i h
  obtain ⟨z,F,m,y,finish,last,bill,out,act,reserved,frame⟩ := run w W pos v D x seed liveD
    ((off _ (fun _ _ => callerOff _ _)).2.trans prec) (by
      intro j
      have eq := off (work j) (fun i _ => (apart j i).symm)
      exact ⟨eq.1.trans (vacant _).1,eq.2.trans (vacant _).2⟩)
  refine ⟨z,F,t+m,y,start.seq finish,last.trans user,?_,out,act,reserved,?_,?_,?_⟩
  · intro js nd
    have mass : M ≤ V := (Nat.le_self_pow (by decide : 128 ≠ 0) M).trans (Nat.le_mul_of_pos_right _ pos)
    have width : w+1 ≤ V := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans mass
    have count : W ≤ V := Nat.le_mul_of_pos_left _ (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
    have size (k : ℕ) : k.size ≤ k := Nat.size_le.mpr Nat.lt_two_pow_self
    have setupBound : 18*M.size+8*W.size+8*(w+1)+11*(w+1).size+53 ≤ 98*V := by
      have := size M
      have := size W
      have := size (w+1)
      omega
    have initial := (paid js nd).trans (Nat.add_le_add_left setupBound _)
    have charge : (t : ℝ)+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+98*V := by
      exact_mod_cast initial
    have power : 1 ≤ ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau :=
      Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le
    have scale := le_mul_of_one_le_right (Nat.cast_nonneg V (α := ℝ)) power
    have done := bill js nd
    change (m : ℝ)+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+C*V*_ at done
    rw [Nat.cast_add t m]
    linarith only [charge,scale,done]
  · intro i ne
    have eq := frame (recBank i) (fun r => (fanOff _ _).symm)
    exact ⟨eq.1.trans (seed i ne).1,eq.2.trans (seed i ne).2⟩
  · intro i
    have unchanged := frame (work i) (fun r => (fanOff _ _).symm)
    have before := off (work i) (fun j _ => (apart i j).symm)
    exact ⟨unchanged.1.trans (before.1.trans (vacant _).1),unchanged.2.trans (before.2.trans (vacant _).2)⟩
  · intro j away outside
    have f := frame j away
    have e := off j (fun _ _ => outside _)
    exact ⟨f.1.trans e.1,f.2.trans e.2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
