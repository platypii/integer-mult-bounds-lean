import IntegerMultBounds.Machine.RecursiveRowsMove
import IntegerMultBounds.Machine.CleanExecution

/-! Clean destructive cyclic split/permuted merge from six original headers.
The same permanent payload bank is used at both boundaries; every generated
counter, arithmetic workspace, installed loop marker and tracker is erased.
Split clears the common source, and merge clears every physical role source. -/
namespace IntegerMultBounds.Machine.RecursiveRowsClean
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowsInstall (LocalTapes TotalTapes)
open RecursiveRowsMove (TapeCount)
variable {q c : ℕ} (hq : 2 ≤ q)
noncomputable section

def dimRight (i : Fin 38) : Bool := decide (3 ≤ i.val ∧ i.val < 9)
def localKeep : Fin (LocalTapes c) → Bool :=
  Fin.addCases (Fin.addCases (fun _ => true) (fun _ => false)) (fun _ => false)
def right : Fin (TapeCount c) → Bool :=
  Fin.addCases (Fin.addCases dimRight (fun _ => false)) (fun _ => false)
def keep : Fin (TapeCount c) → Bool :=
  Fin.addCases (Fin.addCases dimRight localKeep) (fun _ => false)

def bank (hs : Fin 6 → List Bool) (payload : Tapes (1+c) q) :=
  (RecursiveRowsMove.input hs payload).append (SharedBank.empty (TapeCount c) q)

def splitProgram := CleanExecution.program (RecursiveRowsMove.splitProgram hq (c := c)) right keep
def mergeProgram (rho : Equiv.Perm (Fin c)) :=
  CleanExecution.program (RecursiveRowsMove.mergeProgram hq rho) right keep

def bound (c V : ℕ) := (2+5*TapeCount c)*RecursiveRowsMove.bound c V+11*TapeCount c+4

private theorem input_head (hs : Fin 6 → List Bool) (payload : Tapes (1+c) q)
    (hp : payload.head = fun _ => 0) :
    (RecursiveRowsMove.input hs payload).head = TrackedInit.position right := by
  funext i
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      simp only [RecursiveRowsMove.input,RecursiveRowsConstruct.input,Tapes.append,right,TrackedInit.position,Fin.addCases_left]
      fin_cases i <;> rfl
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i => simpa only [RecursiveRowsMove.input,RecursiveRowsConstruct.input,RecursiveRowsInstall.blankLocal,
            Tapes.append,Fin.addCases_left,Fin.addCases_right,right,TrackedInit.position,Bool.false_eq_true,ite_false] using congrFun hp i
        | right i => simp [RecursiveRowsMove.input,RecursiveRowsConstruct.input,RecursiveRowsInstall.blankLocal,
            Tapes.append,SharedBank.empty,right,TrackedInit.position]
      | right i => simp [RecursiveRowsMove.input,RecursiveRowsConstruct.input,RecursiveRowsInstall.blankLocal,
          Tapes.append,SharedBank.empty,right,TrackedInit.position]
  | right i => simp [RecursiveRowsMove.input,Tapes.append,SharedBank.empty,right,TrackedInit.position]

private theorem input_private (hs : Fin 6 → List Bool) (payload : Tapes (1+c) q)
    (i : Fin (TapeCount c)) (hi : keep i = false) :
    (RecursiveRowsMove.input hs payload).head i = 0 ∧
    (RecursiveRowsMove.input hs payload).tape i = fun _ => blank := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      have hn : ¬ (3 ≤ i.val ∧ i.val < 9) := by simpa [keep,dimRight] using hi
      simpa only [RecursiveRowsMove.input,RecursiveRowsConstruct.input,Tapes.append,Fin.addCases_left] using
        RecursiveRowsDimensions.input_blank (q := q) hs i hn
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i => simp [keep,localKeep] at hi
        | right i => simp [RecursiveRowsMove.input,RecursiveRowsConstruct.input,RecursiveRowsInstall.blankLocal,
            Tapes.append,SharedBank.empty]
      | right i => simp [RecursiveRowsMove.input,RecursiveRowsConstruct.input,RecursiveRowsInstall.blankLocal,
          Tapes.append,SharedBank.empty]
  | right i => simp [RecursiveRowsMove.input,Tapes.append,SharedBank.empty]

private theorem retained_eq (target : RecursiveRowsResetCount.Target) (hs : Fin 6 → List Bool) (v : Descriptor)
    (rs : List Bool) (payload : Tapes (1+c) q) :
    TrackedCleanupList.retained keep (RecursiveRowsMove.output hq target hs v rs payload) =
      RecursiveRowsMove.input hs payload := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      simp only [TrackedCleanupList.retained,keep,RecursiveRowsMove.output,CountedBankReset.bank,
        CountedLoopReuseAlphabet.bank,RecursiveRowsMove.counted,RecursiveRowsMove.input,RecursiveRowsConstruct.input,
        Tapes.append,Fin.addCases_left]
      fin_cases i <;> first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left i => simp [TrackedCleanupList.retained,keep,localKeep,RecursiveRowsMove.output,RecursiveRowsMove.counted,
            RecursiveRowsMove.input,RecursiveRowsConstruct.input,RecursiveRowsInstall.blankLocal,RecursiveRowsInstall.prepared,
            CountedBankReset.bank,CountedLoopReuseAlphabet.bank,Tapes.append]
        | right i => simp [TrackedCleanupList.retained,keep,localKeep,RecursiveRowsMove.input,
            RecursiveRowsConstruct.input,RecursiveRowsInstall.blankLocal,Tapes.append,SharedBank.empty]
      | right i => simp [TrackedCleanupList.retained,keep,localKeep,RecursiveRowsMove.input,
          RecursiveRowsConstruct.input,RecursiveRowsInstall.blankLocal,Tapes.append,SharedBank.empty]
  | right i => simp [TrackedCleanupList.retained,keep,RecursiveRowsMove.input,Tapes.append,SharedBank.empty]

private theorem payload_head (f : ℤ → Fin (q+4)) (roles : Fin c → ℤ → Fin (q+4)) :
    (CyclicRowCopy.payload f roles 0 (fun _ => 0)).head = fun _ => 0 := by
  funext i
  induction i using Fin.addCases <;> simp [CyclicRowCopy.payload,Tapes.append]

/-- From one sole common array to its cyclic role streams, with the original
common tape blank again and every private tape blank/head zero. -/
theorem split_hoare (hc : 0 < c) (hs : Fin 6 → List Bool) (v : Descriptor)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4)) :
    HoareTime (splitProgram hq (c := c))
      (fun w => w = bank hs (RecursiveRowsConstruct.sourcePayload (c := c) x))
      (fun w => w = bank hs (RecursiveRowsMove.rolePayload hd x)) (bound c (volume q v)) := by
  obtain ⟨rs,hm⟩ := RecursiveRowsMove.split_hoare hq hc hs v hv hp hd x
  have h := CleanExecution.realizes (RecursiveRowsMove.splitProgram hq (c := c)) right keep
    (RecursiveRowsMove.input hs (RecursiveRowsConstruct.sourcePayload (c := c) x))
    (RecursiveRowsMove.output hq .common hs v rs (RecursiveRowsMove.rolePayload hd x)) _
    (input_head hs _ (payload_head _ _)) (fun i hi => (input_private hs _ i hi).2) hm
  rw [retained_eq] at h
  exact h

/-- From permuted physical role streams to the common cyclic array; every role
tape is physically erased/reset, so the next recursive transfer may reuse it. -/
theorem merge_hoare (rho : Equiv.Perm (Fin c)) (hc : 0 < c) (hs : Fin 6 → List Bool) (v : Descriptor)
    (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (hd : c ∣ v.rows)
    (x : Fin (volume q v) → Fin (q+4)) :
    HoareTime (mergeProgram hq rho)
      (fun w => w = bank hs (RecursiveRowsConstruct.mergePayload rho hd x (fun _ => blank)))
      (fun w => w = bank hs (RecursiveRowsConstruct.sourcePayload (c := c) x)) (bound c (volume q v)) := by
  obtain ⟨rs,hm⟩ := RecursiveRowsMove.merge_hoare hq rho hc hs v hv hp hd x
  have h := CleanExecution.realizes (RecursiveRowsMove.mergeProgram hq rho) right keep
    (RecursiveRowsMove.input hs (RecursiveRowsConstruct.mergePayload rho hd x (fun _ => blank)))
    (RecursiveRowsMove.output hq .roles hs v rs (RecursiveRowsConstruct.sourcePayload (c := c) x)) _
    (input_head hs _ (payload_head _ _)) (fun i hi => (input_private hs _ i hi).2) hm
  rw [retained_eq] at h
  exact h

theorem bound_linear (c V : ℕ) (hV : 0 < V) :
    bound c V ≤ ((2+5*TapeCount c)*(RecursiveRowsQuotient.constant c+1099)+11*TapeCount c+4)*V := by
  have hconst : 336 ≤ 336*V := Nat.le_mul_of_pos_right _ hV
  have hbase : RecursiveRowsMove.bound c V ≤ (RecursiveRowsQuotient.constant c+1099)*V := by
    unfold RecursiveRowsMove.bound RecursiveRowsConstruct.bound RecursiveRowsConstruct.setupBound RecursiveRowsDimensions.bound
    nlinarith
  have hmul := Nat.mul_le_mul_left (2+5*TapeCount c) hbase
  have hrest := Nat.le_mul_of_pos_right (11*TapeCount c+4) hV
  unfold bound
  nlinarith


def payloadSlot (i : Fin (1+c)) : Fin (TapeCount c+TapeCount c) :=
  Fin.castAdd (TapeCount c) (Fin.castAdd 2 (Fin.natAdd 38 (Fin.castAdd 2 (Fin.castAdd 2 i))))
def headerSlot (j : Fin 6) : Fin (TapeCount c+TapeCount c) :=
  Fin.castAdd (TapeCount c) (Fin.castAdd 2 (Fin.castAdd (LocalTapes c) (RecursiveRowsDimensions.headerSlot j)))

theorem payload (hs : Fin 6 → List Bool) (p : Tapes (1+c) q) (i : Fin (1+c)) :
    (bank hs p).head (payloadSlot i) = p.head i ∧ (bank hs p).tape (payloadSlot i) = p.tape i := by
  simp only [bank,payloadSlot,RecursiveRowsMove.input,RecursiveRowsConstruct.input,RecursiveRowsInstall.blankLocal,
    Tapes.append,Fin.addCases_left,Fin.addCases_right]
  trivial

theorem headers (hs : Fin 6 → List Bool) (p : Tapes (1+c) q) (j : Fin 6) :
    (bank hs p).head (headerSlot j) = 1 ∧
    (bank hs p).tape (headerSlot j) = RadixZeroFill.encodedBinary (hs j) := by
  simpa only [bank,headerSlot,RecursiveRowsMove.input,RecursiveRowsConstruct.input,
    Tapes.append,Fin.addCases_left] using RecursiveRowsDimensions.input_header (q := q) hs j

theorem private_blank (hs : Fin 6 → List Bool) (p : Tapes (1+c) q) (i : Fin (TapeCount c)) (hi : keep i = false) :
    (bank hs p).head (Fin.castAdd (TapeCount c) i) = 0 ∧
    (bank hs p).tape (Fin.castAdd (TapeCount c) i) = fun _ => blank := by
  simpa only [bank,Tapes.append,Fin.addCases_left] using input_private hs p i hi

theorem trackers_blank (hs : Fin 6 → List Bool) (p : Tapes (1+c) q) (i : Fin (TapeCount c)) :
    (bank hs p).head (Fin.natAdd (TapeCount c) i) = 0 ∧
    (bank hs p).tape (Fin.natAdd (TapeCount c) i) = fun _ => blank := by
  simp only [bank,Tapes.append,Fin.addCases_right,SharedBank.empty]
  trivial

theorem bank_head (hs : Fin 6 → List Bool) (p : Tapes (1+c) q) (hp : p.head = fun _ => 0) :
    (bank hs p).head = Fin.addCases (TrackedInit.position right) (fun _ => 0) := by
  unfold bank Tapes.append SharedBank.empty
  rw [input_head hs p hp]

end
end IntegerMultBounds.Machine.RecursiveRowsClean
