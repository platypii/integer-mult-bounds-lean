module

public import IntegerMultBounds.MathlibTM2.M6.BitInPlaceOwnerWords
public import IntegerMultBounds.MathlibTM2.M6.BitScalarFrame

/-! Compact the shared COPY payload before returning to the parent owners. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

private theorem compactCharge {T : ℕ} (j : Fin T) (S D : Stacks T prime)
    (xs : List (Fin (prime+4))) {n price : ℕ} (paid : CleanupBound S D n price) :
    let G := {D with L := Function.update D.L j [], R := Function.update D.R j xs}
    CleanupBound S G (n+(12*xs.length+19+4*(D.L j).length+2*(D.R j).length))
      (price+cleanupWeight (S.L j) (S.R j)+14*xs.length+19) := by
  intro G
  let E := {D with L := Function.update D.L j [], R := Function.update D.R j []}
  have empty : ∀ i ∈ [j], E.L i = [] ∧ E.R i = [] := by simp [E]
  have bounded i : (E.L i).length ≤ (D.L i).length ∧ (E.R i).length ≤ (D.R i).length := by
    by_cases h : i = j <;> simp [E,h]
  have bill := cleanupBound_clearBank [j] (by simp) paid (localCost := 12*xs.length+19)
    (m := 12*xs.length+19+4*(D.L j).length+2*(D.R j).length)
    (by simp [tapeCharge,cleanupWeight]; omega) empty bounded
  intro js distinct
  have diff (is : List (Fin T)) (nd : is.Nodup) :
      tapeCharge cleanupWeight is G = tapeCharge cleanupWeight is E + (if j ∈ is then 2*xs.length else 0) := by
    induction is with
    | nil => simp [tapeCharge]
    | cons i is ih =>
      have tail := ih nd.of_cons
      by_cases h : i = j
      · subst i
        simp [G,E,tapeCharge,cleanupWeight,nd.notMem] at tail ⊢
        omega
      · simp [G,E,tapeCharge,cleanupWeight,h,Ne.symm h] at tail ⊢
        omega
  have bound := bill js distinct
  change _+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js S+_
  rw [diff js distinct]
  change _+tapeCharge cleanupWeight js E ≤ tapeCharge cleanupWeight js S+_ at bound
  simp only [tapeCharge,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at bound ⊢
  split <;> omega

/-- The concrete COPY layout shares only its payload with the owners. Compacting
that tape makes the returned owner size independent of the recursive bill. -/
theorem compactScheduledCopy [M8.Machine.Net] {P U : Type} {T k Q : ℕ}
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (layout : WorkerBasisLayout ports)
    (fan : Fin k ↪ Fin T) (owners : layout.OwnerTapes fan)
    (body : P → Pr P T Q prime U) (f : P) :
    let bank := scheduledRecordPorts ports
    ∃ code : Pr P T Q prime U, ∀ (node child : Descriptor) (w W : ℕ) record position price,
      ScheduledChildExec node child w W ports record position body f price true → child.width < node.width →
      let V := (prime^(w+1))^16*W
      let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size
        record SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
      let clean := fun S : Stacks T prime => ∀ i : Fin (rowSwapBlock.tapes+35), 35 ≤ i.val →
        S.L (ports i) = [] ∧ S.R (ports i) = []
      ∀ u S x, stored x S → clean S →
      ∃ z F n y, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (price+cleanupWeight (S.L (bank 24)) (S.R (bank 24))+14*V+19) ∧
        stored y F ∧ clean F ∧ F.L (bank 24) = [] ∧ F.R (bank 24) = List.ofFn (fun i => SparseRoleCircuit.encode (y i)) ∧
        (∀ j, j ≠ bank 24 → (∀ i, ports i ≠ j) ∨ (∃ h, fan h = j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        tapeCharge cleanupWeight (frameSlots fan) F ≤ tapeCharge cleanupWeight (frameSlots fan) S+2*V+4 ∧
        ∀ i, y (position i) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) i := by
  intro bank
  obtain ⟨pack,compact⟩ := materializeOwnerInPlace body (bank 24) (bank 0) (bank 1)
    (by simp [List.nodup_cons,bank.injective.eq_iff])
  refine ⟨(body f).seq pack,?_⟩
  intro node child w W record position price run smaller V stored clean u S x ready free
  obtain ⟨v,D,t,y,exec,paid,user,out,cleared,frame,action⟩ := run smaller u S x ready free
  have word : WordAtZero y (D.L (bank 24)) (D.R (bank 24)) := by
    intro j
    rw [← encodedOwnerCell]
    simpa only [sub_zero,List.map_ofFn] using out.src j
  obtain ⟨z,last,finish⟩ := compact y v D word (out.scratch 0 (by decide)).1 (out.scratch 0 (by decide)).2
    (out.scratch 1 (by decide)).2
  let xs := List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (y i)
  let F := {D with L := Function.update D.L (bank 24) [], R := Function.update D.R (bank 24) xs}
  have kept j (away : j ≠ bank 24) : F.L j = D.L j ∧ F.R j = D.R j := by simp [F,away]
  have zl : F.L (bank 24) = [] := Function.update_self ..
  have zr : F.R (bank 24) = xs := Function.update_self ..
  have restored : ∀ j, j ≠ bank 24 → (∀ i, ports i ≠ j) ∨ (∃ h, fan h = j) → F.L j = S.L j ∧ F.R j = S.R j := by
    intro j ne hj
    have off : ∀ i, ports i ≠ j := by
      rcases hj with outside | ⟨h,rfl⟩
      · exact outside
      intro i eq
      by_cases same : i.val = 24
      · exact ne (eq.symm.trans (congrArg ports (Fin.ext same)))
      · exact owners.recordPrivate i same h eq.symm
    exact ⟨(kept _ ne).1.trans (frame j off).1,(kept _ ne).2.trans (frame j off).2⟩
  refine ⟨z,F,_,y,exec.seq finish,last.trans user,?_,?_,?_,zl,zr,restored,?_,action⟩
  · simpa only [xs,List.length_ofFn] using compactCharge (bank 24) S D xs paid
  · apply out.returnPayload (outBank := bank) (fun i hi => kept _ (bank.injective.ne hi))
    intro j
    rw [zl,zr,sub_zero,← List.map_ofFn,encodedOwnerCell,readAt_nil_left,putWord_blank_zero]
  · intro i hi
    have ne : ports i ≠ bank 24 := ports.injective.ne (fun eq => by
      have h := congrArg Fin.val eq
      change i.val = 24 at h
      omega)
    exact ⟨(kept _ ne).1.trans (cleared i hi).1,(kept _ ne).2.trans (cleared i hi).2⟩
  · have bound (js : List (Fin T)) (nd : js.Nodup) (inside : ∀ j ∈ js, ∃ i, fan i = j) :
        tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(if bank 24 ∈ js then 2*V+4 else 0) := by
      induction js with
      | nil => simp [tapeCharge]
      | cons j js ih =>
        have tail := ih nd.of_cons (fun a ha => inside a (List.mem_cons_of_mem _ ha))
        by_cases eq : j = bank 24
        · subst j
          simp [tapeCharge,cleanupWeight,nd.notMem,zl,zr,xs] at tail ⊢
          dsimp only [V]
          omega
        · obtain ⟨l,r⟩ := restored j eq (.inr (inside j List.mem_cons_self))
          simp [tapeCharge,cleanupWeight,l,r,Ne.symm eq] at tail ⊢
          omega
    have total := bound (frameSlots fan) (by simpa [frameSlots] using (List.nodup_finRange _).map fan.injective)
      (fun j => (mem_frameSlots fan j).mp)
    split at total <;> omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
