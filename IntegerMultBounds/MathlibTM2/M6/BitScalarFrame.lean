module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead
public import IntegerMultBounds.MathlibTM2.M6.BitScalarMoveSequence
public import IntegerMultBounds.MathlibTM2.M6.BitSeededSuspendedMove

/-! Account for the suspended parent bank across scalar blocks in the PR589 schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback Certificates.PR589
open Shared50ModularControl (prime)

/-- The same potential covers the stack lengths billed by MOVE and telescopes across gates. -/
theorem frameCharge_bounds {T : ℕ} (js : List (Fin T)) (S : Stacks T prime) :
    let size := (js.map fun j => (S.L j).length+(S.R j).length+2).sum
    let charge := tapeCharge (fun l r => 4*l.length+2*r.length+4) js S
    2*size ≤ charge ∧ charge ≤ 4*size := by
  induction js with
  | nil => simp [tapeCharge]
  | cons j js ih =>
    simp only [tapeCharge,List.map_cons,List.sum_cons] at *
    omega

/-- A placed scalar block increases the saved-bank potential by at most its linear
bill, including when some of the scalar owners belong to the suspended bank. -/
theorem scalarBlockFrame {k T b : ℕ} {P U : Type} (layout : Fin 661 ↪ Fin k)
    (owner : Fin (k+2+1) ↪ Fin T) (bank : Fin b ↪ Fin T) :
    ∃ states, ∀ {Q : ℕ} (body : P → Pr P T Q prime U),
    states ≤ Q → ∀ gs : List RawGate, (∀ g ∈ gs, g ∈ program) →
    ∃ (code : Pr P T Q prime U) (rate : ℕ), ∀ {V : ℕ}, 0 < V →
    ∀ (x : Fin k → Fin V → ZMod 2) word u S,
      HelperFan (Fin.castAddEmb 1) x (embStk owner S) ∧ S.R (owner (Fin.last (k+2))) = word →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ CleanupBound S F n (rate*V) ∧
        z.user = u.user ∧
        HelperFan (Fin.castAddEmb 1) (gs.foldl (scalarOwnerEffect layout) x) (embStk owner F) ∧
        F.R (owner (Fin.last (k+2))) = word ∧
        tapeCharge cleanupWeight (frameSlots bank) F ≤ tapeCharge cleanupWeight (frameSlots bank) S+rate*V ∧
        ∀ j, (∀ i, owner i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨states,compile⟩ := scalarCutoffBlock layout
  refine ⟨states,?_⟩
  intro Q body capacity gs allowed
  obtain ⟨code,rate,run⟩ := compile (U := U) capacity gs allowed
  refine ⟨embProg owner Empty.elim code,rate,?_⟩
  intro V pos x word u S live
  obtain ⟨v,D,n,exec,paid,user,out,kept⟩ := run pos x word (embDn owner u) (embStk owner S) live
  obtain ⟨z,F,placed,_,same,view,frame⟩ := exec_emb (body' := body) (ι := Empty.elim) owner.injective
    (fun f => nomatch f) exec u rfl S rfl
  rw [← view] at paid out kept
  have cost := CleanupBound.place owner frame paid
  have distinct : (frameSlots bank).Nodup := by
    simpa [frameSlots] using (List.nodup_finRange _).map bank.injective
  exact ⟨z,F,n,placed,cost,same.trans user,out,kept,
    (Nat.le_add_left _ n).trans (cost _ distinct),frame⟩

open M8.RevMachine RecursiveInterchangeLayout

/-- A scheduled COPY may borrow clean scratch from the saved bank. Only its
record ports need to be disjoint to keep the parent's potential exactly. -/
theorem scheduledCopyFrame [M8.Machine.Net] {P U : Type} {T Q : ℕ} (node desc : Descriptor) (w W : ℕ)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (record : List (Fin (prime+4)))
    (position : Fin (volume prime desc) ≃ Fin ((prime^(w+1))^16*W))
    (body : P → Pr P T Q prime U) (f : P) (budget : ℕ) (charged : Bool)
    (saved : Fin b ↪ Fin T) (apart : ∀ j i, saved j ≠ scheduledRecordPorts ports i)
    (worker : ScheduledChildExec node desc w W ports record position body f budget charged) :
  let bank := scheduledRecordPorts ports
  let M := prime^(w+1)
  let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank M.size W.size record
    SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
  let clean := fun (D : Stacks T prime) => ∀ l : Fin (rowSwapBlock.tapes+35), 35 ≤ l.val →
    D.L (ports l) = [] ∧ D.R (ports l) = []
  desc.width < node.width → ∀ u D word, stored word D → clean D →
    ∃ z F t changed, Exec body (body f) (mk u D) t (mk z F) ∧ workerCost charged D F t budget ∧ z.user = u.user ∧
      stored changed F ∧ clean F ∧ (∀ j, (∀ l, ports l ≠ j) → F.L j = D.L j ∧ F.R j = D.R j) ∧
      tapeCharge cleanupWeight (frameSlots saved) F = tapeCharge cleanupWeight (frameSlots saved) D ∧
      ∀ h, changed (position h) = Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) (word ∘ position) h := by
  intro bank M stored clean smaller u D word ready empty
  obtain ⟨z,F,t,changed,exec,paid,user,out,cleared,frame,action⟩ := worker smaller u D word ready empty
  refine ⟨z,F,t,changed,exec,paid,user,out,cleared,frame,?_,action⟩
  unfold tapeCharge
  congr 1
  apply List.map_congr_left
  intro j hj
  obtain ⟨k,rfl⟩ := (mem_frameSlots saved j).mp hj
  by_cases hit : ∃ i, ports i = saved k
  · obtain ⟨i,eq⟩ := hit
    have high : 35 ≤ i.val := by
      by_contra! low
      exact apart k ⟨i.val,low⟩ (eq.symm.trans (congrArg ports (Fin.ext rfl)))
    simp only [← eq,(empty i high).1,(empty i high).2,(cleared i high).1,(cleared i high).2]
  · have off i eq := hit ⟨i,eq⟩
    simp only [(frame _ off).1,(frame _ off).2]

end IntegerMultBounds.MathlibTM2.M6.BitNode
