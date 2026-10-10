import IntegerMultBounds.Machine.CompactComplexSourceReadyWorkspace
import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafDispatch
import IntegerMultBounds.Machine.CompactComplexScheduledPCDecode
import IntegerMultBounds.Machine.FiniteDispatch

/-! Recover actual child direction from the top saved return address. One
fixed pop-and-restore machine reads the code into finite control and restores
every stack cell and its head before selecting a directional continuation.
The temporary erasure needs no blank assumption on the older background. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyDirection
noncomputable section
namespace Peek
open FiniteReturnStack (Control Code encode cfg bank wordPart)
variable {a k : ℕ}
abbrev count (k : ℕ) := Fintype.card (Control k)

def scanState : Fin (count k) → Fin (count k+count k) := Fin.castAdd (count k)
def restoreState : Fin (count k) → Fin (count k+count k) := Fin.natAdd (count k)

/-- The right half uses the universal transition table of `push`; its start
state receives the code actually decoded by the left half. -/
def program (a k : ℕ) : Program 1 (count k+count k) a where
  tapes_pos := by decide
  start := scanState (FiniteReturnStack.pop a k).start
  transition := fun st sy => Fin.addCases
    (fun st => match (FiniteReturnStack.pop a k).transition st sy with
      | some (next,act) => some (scanState next,act)
      | none => some (restoreState st,fun i => (sy i,.stay)))
    (fun st => ((FiniteReturnStack.push a (fun _ : Fin k => false)).transition st sy).map
      (fun (next,act) => (restoreState next,act))) st

private theorem scan_step {x y : Config 1 (count k) a}
    (h : step (FiniteReturnStack.pop a k) x=some y) :
    step (program a k) (x.mapState scanState)=some (y.mapState scanState) := by
  unfold step at h ⊢
  simp only [program,Config.mapState,scanState,Fin.addCases_left]
  cases ht : (FiniteReturnStack.pop a k).transition x.state (fun i => x.tape i (x.head i)) with
  | none => simp only [ht] at h; contradiction
  | some z =>
    simp only [ht,Option.some.injEq] at h
    subst y
    cases z
    rfl

private theorem restore_step (code : Code k) (x : Config 1 (count k) a) :
    step (program a k) (x.mapState restoreState)=
      (step (FiniteReturnStack.push a code) x).map (Config.mapState restoreState) := by
  unfold step
  simp only [program,Config.mapState,restoreState,Fin.addCases_right]
  have ht : (FiniteReturnStack.push a (fun _ : Fin k => false)).transition=
      (FiniteReturnStack.push a code).transition := rfl
  rw [ht]
  cases hz : (FiniteReturnStack.push a code).transition x.state (fun i => x.tape i (x.head i)) with
  | none => rfl
  | some z => cases z; rfl

private theorem boundary (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ) :
    step (program a k) ((cfg (.inr (0,code)) f p).mapState scanState)=
      some ((cfg (.inr (0,code)) f p).mapState restoreState) := by
  simp only [step,program,Config.mapState,scanState,Fin.addCases_left,FiniteReturnStack.pop,cfg,
    Equiv.symm_apply_apply,Fin.val_zero,Nat.lt_irrefl,↓reduceDIte,restoreState,Move.offset,add_zero]
  congr 1
  congr 1
  funext i z
  by_cases hz : z=p <;> simp [hz]


def cleared (f : ℤ → Fin (a+4)) (p : ℤ) (k : ℕ) (z : ℤ) :=
  if p≤z ∧ z<p+k then blank else f z

private theorem cleared_free (f : ℤ → Fin (a+4)) (p : ℤ) (j : ℕ) (hj : j<k) :
    cleared f p k (p+j)=blank := by simp [cleared,show p≤p+(j:ℤ) ∧ p+(j:ℤ)<p+k by omega]

private theorem word_cleared (f : ℤ → Fin (a+4)) (p : ℤ) (code : Code k) :
    wordPart (cleared f p k) p code k le_rfl=wordPart f p code k le_rfl := by
  funext z
  simp only [wordPart,cleared]
  split_ifs <;> rfl

/-- The true saved binary frame is read and restored literally. Its decoded
code remains in the halt state, after exactly twice the fixed width plus two. -/
theorem exact_run (code : Code k) (f : ℤ → Fin (a+4)) (p : ℤ) :
    run (program a k) (2*k+2) ((bank (wordPart f p code k le_rfl) (p+k)).start (program a k))=
      some ((cfg (.inr (⟨k,by omega⟩,code)) (wordPart f p code k le_rfl) (p+k)).mapState restoreState) ∧
    step (program a k)
      ((cfg (.inr (⟨k,by omega⟩,code)) (wordPart f p code k le_rfl) (p+k)).mapState restoreState)=none := by
  let base := cleared f p k
  obtain ⟨hr,hh⟩ := FiniteReturnStack.pop_exact code base p (cleared_free f p)
  have hs := run_simulation _ (program a k) (Config.mapState scanState)
    (fun _ _ h => scan_step h) hr
  obtain ⟨hp,hph⟩ := FiniteReturnStack.push_exact code base p
  have ht := run_simulation _ (program a k) (Config.mapState restoreState)
    (fun x y h => by rw [restore_step code,h];rfl) hp
  constructor
  · have hb := boundary code base p
    have hout : run (program a k) ((k+1)+1+k)
        (((bank (wordPart base p code k le_rfl) (p+k)).start (FiniteReturnStack.pop a k)).mapState scanState)=
        some ((cfg (.inr (⟨k,by omega⟩,code)) (wordPart base p code k le_rfl) (p+k)).mapState restoreState) := by
      rw [run_add,run_add,hs]
      simp only [Option.bind_some,run_one,hb]
      exact ht
    simpa only [base,word_cleared,show (k+1)+1+k=2*k+2 by omega,Tapes.start,program,Config.mapState] using hout
  · have he := restore_step code (cfg (.inr (⟨k,by omega⟩,code))
      (wordPart base p code k le_rfl) (p+k))
    rw [hph] at he
    simpa only [Option.map_none,base,word_cleared] using he

end Peek
open Networks
open CompactComplexSourceReadyWorkspace (tapes)
open CompactComplexScheduledPCDecode (callAddress decodeCall)
open FiniteReturnStack (Control Code encode cfg bank wordPart)
variable {s c N k : ℕ}

def selectFor (hN : N≤2^k) (direction : Fin N → Option (Fin 2)) :
    Fin (Peek.count k+Peek.count k) → Option (Fin 2) :=
  Fin.addCases (fun _ => none) (fun st => match (encode k).symm st with
    | .inl _ => none
    | .inr (_,code) => (FiniteReturnDispatch.select hN (encode k (.inr (0,code)))).bind direction)

theorem selectFor_actual (hN : N≤2^k) (direction : Fin N → Option (Fin 2)) (address : Fin N)
    (n : Fin (k+1)) :
    selectFor hN direction (Peek.restoreState (encode k (.inr (n,FiniteReturnStack.address hN address))))=
      direction address := by
  simp only [selectFor,Peek.restoreState,Fin.addCases_right,Equiv.symm_apply_apply,
    FiniteReturnDispatch.select_return,Option.bind_some]

def terminalFor (hN : N≤2^k) (address : Fin N) : Fin (Peek.count k+Peek.count k) :=
  Peek.restoreState (k:=k) (encode k (.inr
    (⟨k,Nat.lt_succ_self k⟩,FiniteReturnStack.address hN address)))

theorem select_terminal (hN : N≤2^k) (direction : Fin N → Option (Fin 2)) (address : Fin N) :
    selectFor hN direction (terminalFor hN address)=direction address :=
  selectFor_actual hN direction address ⟨k,Nat.lt_succ_self k⟩

/-- Exact physical fixed-width decode, restore and classifier, packaged
without reducing a particular finite code into a gigantic enumeration. -/
theorem local_runsFor (a : ℕ) (hN : N≤2^k) (direction : Fin N → Option (Fin 2))
    (address : Fin N) (older : ℤ → Fin (a+4)) (p : ℤ) :
    let input := bank (wordPart older p (FiniteReturnStack.address hN address) k le_rfl) (p+k)
    ∃ out,run (Peek.program a k) (2*k+2) (input.start (Peek.program a k))=some out ∧
      step (Peek.program a k) out=none ∧ out.tapes=input ∧
      selectFor hN direction out.state=direction address := by
  obtain ⟨hr,hh⟩ := Peek.exact_run (FiniteReturnStack.address hN address) older p
  exact ⟨_,hr,hh,rfl,select_terminal hN direction address⟩

attribute [local irreducible] terminalFor FiniteReturnStack.encode
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites
  CompactComplexCallReturn.addressWidth

private def exactWidth (n : ℕ) : ℕ :=
  Classical.choose (show ∃ m : ℕ,m=n from ⟨n,rfl⟩)

private theorem exactWidth_eq (n : ℕ) : exactWidth n=n :=
  Classical.choose_spec (show ∃ m : ℕ,m=n from ⟨n,rfl⟩)

/-- Exact saved-address width, kept symbolic to avoid enumerating its finite
state space during kernel conversion. -/
def width := exactWidth (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))

theorem width_eq : width=CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3) :=
  exactWidth_eq _

theorem room : CompactComplexScheduledPCLayout.originalCount≤2^width := by
  rw [width_eq]
  exact CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)
def directionTag (call : ComplexRecursiveCallSchema.Call) : Fin 2 := if call.inverse then 1 else 0
def addressDirection (address : Fin CompactComplexScheduledPCLayout.originalCount) :=
  (decodeCall address).map directionTag

private theorem saved_bank_cast {k l N a : ℕ} (hkl : k=l) (hk : N≤2^k) (hl : N≤2^l)
    (address : Fin N) (older : ℤ → Fin (a+4)) (p : ℤ) :
    bank (wordPart older p (FiniteReturnStack.address hk address) k le_rfl) (p+k)=
      bank (wordPart older p (FiniteReturnStack.address hl address) l le_rfl) (p+l) := by
  subst l
  rfl

/-- The symbolic width encodes exactly the original physically saved frame. -/
theorem saved_bank_eq (call : ComplexRecursiveCallSchema.Call) (older : ℤ → Fin 6) (p : ℤ) :
    bank (wordPart older p (FiniteReturnStack.address room (callAddress call)) width le_rfl) (p+width)=
      bank (wordPart older p (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (p+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) := by
  rw [CompactComplexScheduledPCDecode.saved_code]
  exact saved_bank_cast width_eq room _ _ older p

def select := selectFor (k:=width) (N:=CompactComplexScheduledPCLayout.originalCount) room addressDirection

def leafPrograms : Fin 2 → Σ q,Program (tapes s c) q 2 :=
  ![⟨_,CompactComplexSourceReadyStoppedLeafDispatch.program .forward⟩,
    ⟨_,CompactComplexSourceReadyStoppedLeafDispatch.program .inverse⟩]
def leafStates := fun pc : Fin 2 => (leafPrograms (s:=s) (c:=c) pc).1
def leafFamily := fun pc : Fin 2 => (leafPrograms (s:=s) (c:=c) pc).2

def peekProgram (stack : Fin (tapes s c)) :=
  Placement.placed (Peek.program 2 width) (FiniteReturnStackAt.placement stack)
def program (stack : Fin (tapes s c)) :=
  FiniteDispatch.program (peekProgram stack) (leafStates (s:=s) (c:=c)) leafFamily select

/-- Actual saved-PC bytes alone select the true forward/inverse stopped leaf.
All tapes and the stack head are restored before entering that continuation. -/
theorem child_ready (stack : Fin (tapes s c)) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (older : ℤ → Fin 6) (p : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement stack) v=
      bank (wordPart older p (FiniteReturnStack.address room (callAddress call)) width le_rfl) (p+width)) :
    run (program stack) (2*width+3) (v.start (program stack))=
      some ((v.start (leafFamily (directionTag call))).mapState (FiniteDispatch.right leafStates (directionTag call))) := by
  obtain ⟨out,hr,hh,htapes,hselect⟩ := local_runsFor 2 room addressDirection (callAddress call) older p
  have hr' : run (Peek.program 2 width) (2*width+2)
      ((Placement.active (FiniteReturnStackAt.placement stack) v).start (Peek.program 2 width))=some out := by
    rw [hstack]
    exact hr
  have hwhole := Placement.placed_run _ (FiniteReturnStackAt.placement stack) v hr'
  have hhalt := Placement.placed_halt _ (FiniteReturnStackAt.placement stack) v hh
  have hout : (Placement.result (FiniteReturnStackAt.placement stack) v out).tapes=v := by
    rw [Placement.result_tapes,htapes,←hstack,Placement.replace_active]
  have hc : run (leafFamily (directionTag call)) 0
      ((Placement.result (FiniteReturnStackAt.placement stack) v out).tapes.start (leafFamily (directionTag call)))=
      some (v.start (leafFamily (directionTag call))) := by rw [hout];rfl
  have hs : select out.state=some (directionTag call) := hselect.trans
    (congrArg (Option.map directionTag) (CompactComplexScheduledPCDecode.decodeCall_actual call))
  exact FiniteDispatch.run_selected (peekProgram stack) leafStates leafFamily select v
    (Placement.result (FiniteReturnStackAt.placement stack) v out) (directionTag call)
    (v.start (leafFamily (directionTag call))) (2*width+2) 0 hwhole hhalt hs hc

/-- Direct bridge from the literal original saved code produced by child entry;
no converted frame or direction premise is supplied by the caller. -/
theorem child_ready_saved (stack : Fin (tapes s c)) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (tapes s c) 2) (older : ℤ → Fin 6) (p : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement stack) v=
      bank (wordPart older p (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (p+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))) :
    run (program stack) (2*width+3) (v.start (program stack))=
      some ((v.start (leafFamily (directionTag call))).mapState (FiniteDispatch.right leafStates (directionTag call))) :=
  child_ready stack call v older p (hstack.trans (saved_bank_eq call older p).symm)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyDirection
