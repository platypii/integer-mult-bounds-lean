import IntegerMultBounds.Machine.DigitInterchangeCompile
import IntegerMultBounds.Machine.CleanExecution
import IntegerMultBounds.Machine.SharedPayload

/-! Reusable width-one interchange from four supplied canonical descriptors and
the sole array. Two loop sentinels are physically initialized; every generated
stream, marker and tracker is erased after the result overwrites its source.
Synthesis of the four dimension descriptors is explicitly outside this module. -/
namespace IntegerMultBounds.Machine.DigitInterchangeClean
open DigitInterchangeRows DigitInterchangeBank
noncomputable section
variable {O q C E a : ℕ}

def rawHead : Slot q → ℤ | .header _ => 1 | _ => 0

def rawWord (x : Array O q C E a) (bs gs es cs : List Bool) : Slot q → ℤ → Fin (a+4)
  | .source => putWord (fun _ => blank) 0 (CyclicRowSplit.sourceWord (outerRows x))
  | .header j => CountedLoopReuseAlphabet.binary (headerWord bs gs es cs j)
  | _ => fun _ => blank

def rawBank (x : Array O q C E a) (bs gs es cs : List Bool) : Tapes (TapeCount q) a :=
  ⟨fun i => rawHead (name i),fun i => rawWord x bs gs es cs (name i)⟩

def clock : Slot q → Bool | .rowClock | .groupClock => true | _ => false

def initProgram (q a : ℕ) : Program (TapeCount q) 2 a where
  tapes_pos := by have := tapeCount_ge (q := q); unfold LocalTapes at this; omega
  start := 0
  transition := fun st sy => if st = 0 then some (1,fun i =>
    (if clock (name i) then separator else sy i,if clock (name i) then .right else .stay)) else none

theorem initializes_hoare (x : Array O q C E a) (bs gs es cs : List Bool) :
    HoareTime (initProgram q a) (fun v => v = rawBank x bs gs es cs)
      (fun v => v = DigitInterchangeCompile.input x bs gs es cs) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(DigitInterchangeCompile.input x bs gs es cs).head,
    (DigitInterchangeCompile.input x bs gs es cs).tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,initProgram,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i
      cases hn : name i <;>
        simp [rawBank,rawHead,DigitInterchangeCompile.input,DigitInterchangeBank.bank,head,clock,hn,Move.offset]
    · funext i z
      cases hn : name i <;>
        simp [rawBank,rawHead,rawWord,DigitInterchangeCompile.input,DigitInterchangeBank.bank,
          word,clock,hn,CountedLoopReuseAlphabet.empty]
      all_goals intro hz; subst z; rfl
  · simp [step,initProgram]

def initializedProgram (q a : ℕ) := seq (initProgram q a) (DigitInterchangeCompile.program q a)

theorem initialized_hoare (x : Array O q C E a) (bs gs es cs : List Bool)
    (hq : 0 < q) (hO : 0 < O) (hC : 0 < C) (hE : 0 < E)
    (hb : Counter.value bs = C*(q*E)) (hg : Counter.value gs = O)
    (he : Counter.value es = E) (hc : Counter.value cs = O*C)
    (cb : GrowingCounterData.Canonical bs) (cg : GrowingCounterData.Canonical gs)
    (ce : GrowingCounterData.Canonical es) (cc : GrowingCounterData.Canonical cs) :
    HoareTime (initializedProgram q a) (fun v => v = rawBank x bs gs es cs)
      (fun v => v = DigitInterchangeCompile.output x bs gs es cs)
      ((597+2*q)*(O*(q*(C*(q*E))))+2) := by
  have hh := (initializes_hoare x bs gs es cs).seq
    (DigitInterchangeCompile.realizes_hoare x bs gs es cs hq hO hC hE hb hg he hc cb cg ce cc)
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

def rightName : Slot q → Bool | .header _ => true | _ => false
def keepName : Slot q → Bool | .source | .header _ => true | _ => false
def right (i : Fin (TapeCount q)) : Bool := rightName (name i)
def keep (i : Fin (TapeCount q)) : Bool := keepName (name i)

def bank (x : Array O q C E a) (bs gs es cs : List Bool) :=
  (rawBank x bs gs es cs).append (SharedBank.empty (TapeCount q) a)

def program (q a : ℕ) := CleanExecution.program (initializedProgram q a) right keep

def bound (q V : ℕ) := (2+5*TapeCount q)*((597+2*q)*V+2)+11*TapeCount q+4

private theorem raw_head (x : Array O q C E a) (bs gs es cs : List Bool) :
    (rawBank x bs gs es cs).head = TrackedInit.position right := by
  funext i
  cases hn : name i <;> simp [rawBank,rawHead,right,rightName,TrackedInit.position,hn]

private theorem raw_private (x : Array O q C E a) (bs gs es cs : List Bool)
    (i : Fin (TapeCount q)) (hi : keep i = false) :
    (rawBank x bs gs es cs).tape i = fun _ => blank := by
  cases hn : name i <;> simp [keep,keepName,hn] at hi <;> simp [rawBank,rawWord,hn]

private theorem retained_output (x : Array O q C E a) (bs gs es cs : List Bool) :
    TrackedCleanupList.retained keep (DigitInterchangeCompile.output x bs gs es cs) =
      rawBank (transpose x) bs gs es cs := by
  have hh : 1+q+q < 2*q+2 := by omega
  apply congrArg₂ Tapes.mk
  · funext i
    cases hn : name i <;> simp [TrackedCleanupList.retained,keep,keepName,rawBank,rawHead,
      DigitInterchangeCompile.output,DigitInterchangeBank.bank,head,hn]
  · funext i
    cases hn : name i <;> simp [TrackedCleanupList.retained,keep,keepName,rawBank,rawWord,
      DigitInterchangeCompile.output,DigitInterchangeBank.bank,word,hn,hh]

/-- Same sole-payload bank before and after, with exact transpose semantics and
all private workspace blank again. Descriptor construction remains a premise. -/
theorem realizes_hoare (x : Array O q C E a) (bs gs es cs : List Bool)
    (hq : 0 < q) (hO : 0 < O) (hC : 0 < C) (hE : 0 < E)
    (hb : Counter.value bs = C*(q*E)) (hg : Counter.value gs = O)
    (he : Counter.value es = E) (hc : Counter.value cs = O*C)
    (cb : GrowingCounterData.Canonical bs) (cg : GrowingCounterData.Canonical gs)
    (ce : GrowingCounterData.Canonical es) (cc : GrowingCounterData.Canonical cs) :
    HoareTime (program q a) (fun v => v = bank x bs gs es cs)
      (fun v => v = bank (transpose x) bs gs es cs) (bound q (O*(q*(C*(q*E))))) := by
  have hh := CleanExecution.realizes (initializedProgram q a) right keep
    (rawBank x bs gs es cs) (DigitInterchangeCompile.output x bs gs es cs) _
    (raw_head x bs gs es cs) (raw_private x bs gs es cs)
    (initialized_hoare x bs gs es cs hq hO hC hE hb hg he hc cb cg ce cc)
  rw [retained_output] at hh
  exact hh

theorem bound_linear (q V : ℕ) (hV : 0 < V) :
    bound q V ≤ ((2+5*TapeCount q)*(599+2*q)+11*TapeCount q+4)*V := by
  unfold bound
  nlinarith [Nat.mul_le_mul_left (2*(2+5*TapeCount q)+11*TapeCount q+4) hV]

theorem source (x : Array O q C E a) (bs gs es cs : List Bool) :
    (bank x bs gs es cs).head (Fin.castAdd (TapeCount q) (slot .source)) = 0 ∧
    (bank x bs gs es cs).tape (Fin.castAdd (TapeCount q) (slot .source)) =
      putWord (fun _ => blank) 0 (CyclicRowSplit.sourceWord (outerRows x)) := by
  simp [bank,rawBank,Tapes.append,rawHead,rawWord]

theorem headers (x : Array O q C E a) (bs gs es cs : List Bool) (j : Fin 4) :
    (bank x bs gs es cs).head (Fin.castAdd (TapeCount q) (slot (.header j))) = 1 ∧
    (bank x bs gs es cs).tape (Fin.castAdd (TapeCount q) (slot (.header j))) =
      CountedLoopReuseAlphabet.binary (headerWord bs gs es cs j) := by
  simp [bank,rawBank,Tapes.append,rawHead,rawWord]

theorem private_blank (x : Array O q C E a) (bs gs es cs : List Bool)
    (i : Fin (TapeCount q)) (hi : keep i = false) :
    (bank x bs gs es cs).head (Fin.castAdd (TapeCount q) i) = 0 ∧
    (bank x bs gs es cs).tape (Fin.castAdd (TapeCount q) i) = fun _ => blank := by
  simp only [bank,Tapes.append,Fin.addCases_left]
  constructor
  · cases hn : name i <;> simp [keep,keepName,hn] at hi <;> simp [rawBank,rawHead,hn]
  · exact raw_private x bs gs es cs i hi

theorem trackers_blank (x : Array O q C E a) (bs gs es cs : List Bool) (i : Fin (TapeCount q)) :
    (bank x bs gs es cs).head (Fin.natAdd (TapeCount q) i) = 0 ∧
    (bank x bs gs es cs).tape (Fin.natAdd (TapeCount q) i) = fun _ => blank := by
  simp only [bank,Tapes.append,Fin.addCases_right,SharedBank.empty]
  trivial


def pair (x : Array O q C E a) : Tapes 2 a :=
  ⟨fun _ => 0,![putWord (fun _ => blank) 0 (CyclicRowSplit.sourceWord (outerRows x)),fun _ => blank]⟩

theorem payload (x : Array O q C E a) (bs gs es cs : List Bool) :
    SharedPayload.payload (bank x bs gs es cs)
      (Fin.castAdd (TapeCount q) (slot .source)) (Fin.castAdd (TapeCount q) (slot .dest)) = pair x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [SharedPayload.payload,bank,rawBank,Tapes.append,rawHead,rawWord,pair]

theorem bank_head (x : Array O q C E a) (bs gs es cs : List Bool) :
    (bank x bs gs es cs).head = Fin.addCases (TrackedInit.position right) (fun _ => 0) := by
  unfold bank Tapes.append SharedBank.empty
  rw [raw_head]

theorem realizes_array (x : Array O q C E a) (bs gs es cs : List Bool)
    (hq : 0 < q) (hO : 0 < O) (hC : 0 < C) (hE : 0 < E)
    (hb : Counter.value bs = C*(q*E)) (hg : Counter.value gs = O)
    (he : Counter.value es = E) (hc : Counter.value cs = O*C)
    (cb : GrowingCounterData.Canonical bs) (cg : GrowingCounterData.Canonical gs)
    (ce : GrowingCounterData.Canonical es) (cc : GrowingCounterData.Canonical cs) :
    HoareTime (program q a) (fun v => v = bank x bs gs es cs)
      (fun v => v = bank (transpose x) bs gs es cs ∧
        SharedPayload.payload v (Fin.castAdd (TapeCount q) (slot .source))
          (Fin.castAdd (TapeCount q) (slot .dest)) = pair (transpose x) ∧
        ∀ o h c d e, transpose x o h c d e = x o d c h e)
      (bound q (O*(q*(C*(q*E))))) := by
  apply (realizes_hoare x bs gs es cs hq hO hC hE hb hg he hc cb cg ce cc).consequence
    (fun _ h => h) _ le_rfl
  rintro v rfl
  exact ⟨rfl,payload _ bs gs es cs,fun _ _ _ _ _ => rfl⟩

end
end IntegerMultBounds.Machine.DigitInterchangeClean
