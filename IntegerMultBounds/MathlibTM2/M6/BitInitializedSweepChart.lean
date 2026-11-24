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

end IntegerMultBounds.MathlibTM2.M6.BitNode
