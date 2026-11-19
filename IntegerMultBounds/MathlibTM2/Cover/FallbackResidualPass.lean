module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackScan

/-! Restore forward output order on the signed input queue after the residual scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {T r d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def residualPass (ports : Fin (N+2) ↪ Fin T) (ext : Fin 6 ↪ Fin T) (d : ℕ) :
    Pr P T columnCapacity prime U :=
  .seq (residualScan ports (ext 0) (ext 1) (ext 2) (ext 3) (ext 4) (ext 5) d) (moveR (ext 5) (ext 2) id)

/-- Return a completed scan's accumulator to its input tape in forward order. -/
theorem finishScan_exec {Q : ℕ} (a : ScanData r d w W) (ports : Fin (N+2) ↪ Fin T) (ext : Fin 6 ↪ Fin T)
    (off : ∀ i k, ports i ≠ ext k) (body : P → Pr P T Q prime U)
    (u : HS T Q prime U) (D : Stacks T prime) (ready : ScanReady a ports ext a.records D)
    (fresh : a.outputTail = []) (len : a.signed.length = a.records) (empty : D.R (ext 0) = []) :
    let output := (List.range a.records).flatMap (outputRecord (LabelStock.live r (w+1) 1) a.matrix a.input)
    ∃ z F, z.user = u.user ∧ F.R (ext 2) = output ++ a.inputTail ∧ F.R (ext 5) = [] ∧
      F.R (ext 0) = [] ∧ F.R (ports (Fin.last N).castSucc) = a.pivotTail ∧
      F.R (ports (archivePorts 0 (columnBank 34))) = a.matrixTail ∧
      F.L = D.L ∧
      (∀ h, h ≠ ext 2 → h ≠ ext 5 → F.L h = D.L h ∧ F.R h = D.R h) ∧
      Exec body (moveR (ext 5) (ext 2) id) (mk u D) (2*(a.records*(M^(d+1)*W))+2) (mk z F) := by
  intro output
  have acc : D.R (ext 5) = output.reverse := by simpa [outputPrefix,fresh] using ready.acc
  have queue : D.R (ext 2) = a.inputTail := by simpa [← len] using ready.queue
  have volume (is : List ℕ) : (is.flatMap (outputRecord (LabelStock.live r (w+1) 1) a.matrix a.input)).length =
      is.length*(M^(d+1)*W) := by
    induction is with
    | nil => simp
    | cons i is ih => simp [ih,outputRecord,payloadWord,Nat.succ_mul,Nat.add_comm]
  have width : (D.R (ext 5)).length = a.records*(M^(d+1)*W) := by simp [acc,output,volume]
  obtain ⟨z,hz,move⟩ := moveR_exec body (ext 5) (ext 2) (ext.injective.ne (by decide)) id u D
  have finish : (List.range a.records).drop a.records = [] := List.drop_eq_nil_of_le (by simp)
  rw [width] at move
  refine ⟨z,_,hz,?_,?_,?_,?_,?_,?_,?_,move⟩
  · simp [movedR,acc,queue]
  · simp [movedR,ext.injective.eq_iff]
  · simp [movedR,ext.injective.eq_iff,empty]
  · simpa [movedR,off,finish] using ready.pivots
  · simpa [movedR,off,ScanData.matrices,finish] using ready.archive
  · rfl
  · intro h hs ha
    simp [movedR,hs,ha]

theorem residualPass_exec (a : ScanData r d w W) (ports : Fin (N+2) ↪ Fin T) (ext : Fin 6 ↪ Fin T)
    (off : ∀ i k, ports i ≠ ext k) (inputs : ℕ → Record.Array d 1 (w+1) W)
    (encoded : ∀ j < a.records, Record.scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j)
    (signed : (Record.signedInputs a.table (w+1) a.records inputs).Forall₂ Record.Correct a.signed)
    (liveSpec : ∀ j < a.records, LabelStock.live r (w+1) 1 j = true →
      ((a.matrix j).det = 1 ∨ (a.matrix j).det = -1) ∧
      (LabelRing.res prime (w+1) (by omega)).mapMatrix (a.matrix j) = a.table (LabelStock.residue r (w+1) 1 j))
    (padding : ∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
      ∃ symbol, Record.scalarArray (inputs j) = fun _ => symbol)
    (hm : M < 2^a.H) (hw : W < 2^a.J) (hW : 0 < W)
    (body : P → Pr P T columnCapacity prime U) (v : HS T columnCapacity prime U) (S : Stacks T prime)
    (fresh : a.outputTail = []) (start : ScanReady a ports ext 0 S)
    (mask : S.R (ext 0) = (LabelMask.selectors r (w+1) a.records).map bitSymbol) :
    let output := (List.range a.records).flatMap (outputRecord (LabelStock.live r (w+1) 1) a.matrix a.input)
    ∃ z F n, z.user = v.user ∧ F.R (ext 2) = output ++ a.inputTail ∧ F.R (ext 5) = [] ∧
      F.R (ext 0) = [] ∧ F.R (ports (Fin.last N).castSucc) = a.pivotTail ∧
      F.R (ports (archivePorts 0 (columnBank 34))) = a.matrixTail ∧
      F.L (ext 2) = S.L (ext 2) ∧
      n ≤ ((List.range a.records).map fun j => a.recordTime U j + 4).sum + 2 + (2*(a.records*(M^(d+1)*W))+2) ∧
      Exec body (residualPass ports ext d) (mk v S) n (mk z F) := by
  intro output
  obtain ⟨u,D,l,hu,⟨ready,left⟩,empty,hl,scan⟩ := residualScan_exec a ports ext off inputs encoded signed liveSpec padding
    hm hw hW body v S start mask
  obtain ⟨z,F,hz,queue,acc,maskEnd,pivots,archive,finishLeft,_,move⟩ := finishScan_exec a ports ext off body u D ready
    fresh (by simpa [Record.signedInputs] using signed.length_eq.symm) empty
  exact ⟨z,F,_,hz.trans hu,queue,acc,maskEnd,pivots,archive,(congrFun finishLeft _).trans left,Nat.add_le_add_right hl _,.seq scan move⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
