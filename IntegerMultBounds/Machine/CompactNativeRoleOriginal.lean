import IntegerMultBounds.Machine.CompactNativeRoleHeaders
import IntegerMultBounds.Machine.CompactNativeRoleInstall

/-! Concrete original-header native role split/rejoin: all full-address row
lengths and role group counts are generated, every source reset is charged,
all installed descriptors are removed, and the original thirteen words plus
ell/p remain intact. The program depends only on the fixed role count. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleOriginal
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactNativeRoleGeometry (Array role)
open CompactNativeRoleInstall (rawCount tapes blankRaw readyRaw preparedRaw)
open CompactNativeRoleHeaders (prepared recordWidth)
open CompactSpectatorLeafSetup (raw)
open NativeZeroPaddingArray (word)
open RecursiveChildQuotientsConstant (bits)

def inner (s : Shape) (ell : ℕ) := 2^s.bits*2^ell
def symbols (s : Shape) (ell p : ℕ) := inner s ell*(2*(recordWidth s p+1))
def erased (merge : Bool) (n c : ℕ) (s : Shape) (ell p : ℕ) := (if merge then n else n*c)*symbols s ell p
def words (merge : Bool) (n c : ℕ) (s : Shape) (ell p : ℕ) : Fin 3 → List Bool :=
  ![bits (symbols s ell p),bits n,bits (erased merge n c s ell p)]
def sourcePayload {n c : ℕ} (s : Shape) (ell : ℕ) (f : Array n c (inner s ell)) :=
  CyclicRowCopy.payload (NativeZeroPadding.word (word f)) (fun _ : Fin c => fun _ => blank) 0 (fun _ => 0)
def rolePayload {n c : ℕ} (s : Shape) (ell : ℕ) (f : Array n c (inner s ell)) :=
  CyclicRowCopy.payload (fun _ => blank) (fun j => NativeZeroPadding.word (word (role f j))) 0 (fun _ => 0)
def bank (st : ActiveRepairRankHeadersCommands.State) (payload : Tapes (1+c) 2) :=
  (ActiveRepairRankHeadersCommands.bank st).append (blankRaw payload)
def headerProgram (c : ℕ) (ops : List ButterflyAxisHeadersArithmetic.Op) :=
  extend (ButterflyAxisHeadersArithmetic.compile (a:=2) ops).2 (rawCount c)
def cleanupProgram (c : ℕ) := Placement.placed (CompactNativeRoleInstall.cleanup c)
  (finAddFlip : Fin (rawCount c+43) ≃ Fin (43+rawCount c))
def assembly {k : ℕ} (c : ℕ) (merge : Bool) (M : Program (rawCount c) k 2) :=
  seq (seq (seq (seq (seq (headerProgram c (CompactNativeRoleHeaders.schedule c merge))
    (CompactNativeRoleInstall.program c)) (CompactNativeRoleInstall.initializes c))
    (Placement.placed M (finAddFlip : Fin (rawCount c+43) ≃ Fin (43+rawCount c))))
    (cleanupProgram c)) (headerProgram c CompactNativeRoleHeaders.cleanup)
def splitProgram (c : ℕ) := assembly c false (CompactNativeRoleDestructive.splitProgram c)
def mergeProgram (c : ℕ) := assembly c true (CompactNativeRoleDestructive.mergeProgram c)

def transferCost (merge : Bool) (n c : ℕ) (s : Shape) (ell p : ℕ) :=
  CyclicRowNormalized.cost c n (symbols s ell p) (bits (symbols s ell p)) (bits n)+
    30*erased merge n c s ell p+2*(bits (erased merge n c s ell p)).length+69

def cost (merge : Bool) (n c : ℕ) (s : Shape) (ell p rho left count slots right source target : ℕ) :=
  ButterflyAxisHeadersArithmetic.scheduleCost (CompactNativeRoleHeaders.schedule c merge)
    (raw s (n*c) ell p rho left count slots right source target)+
  BinaryDescriptorInstallMarkedList.cost (CompactNativeRoleInstall.instructions (c:=c))
    (CompactNativeRoleInstall.words (words merge n c s ell p))+
  transferCost merge n c s ell p+
  BinaryDescriptorCleanupList.cost (CompactNativeRoleInstall.cleanupSlots (c:=c))
    (CompactNativeRoleInstall.cleanupWords (words merge n c s ell p))+
  ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleHeaders.cleanup
    (prepared c merge s (n*c) ell p rho left count slots right source target)+6

theorem source_headers (merge : Bool) (n c : ℕ) (s : Shape) (ell p rho left count slots right source target : ℕ)
    (hc : 0<c) : ∀ j,
      (ActiveRepairRankHeadersCommands.bank (a:=2) (prepared c merge s (n*c) ell p rho left count slots right source target)).head
        (CompactNativeRoleInstall.source j)=1 ∧
      (ActiveRepairRankHeadersCommands.bank (a:=2) (prepared c merge s (n*c) ell p rho left count slots right source target)).tape
        (CompactNativeRoleInstall.source j)=RadixZeroFill.encodedBinary (words merge n c s ell p j) := by
  intro j
  have hd : n*c/c=n := Nat.mul_div_cancel n hc
  fin_cases j
  all_goals simp [ActiveRepairRankHeadersCommands.bank,ActiveRepairRankHeadersCommands.caller,CleanSubbank.bank,
    CompactNativeRoleInstall.source,prepared,words,symbols,inner,erased,Tapes.append,hd]
  all_goals constructor <;> rfl

private theorem assembled {k : ℕ} (c : ℕ) (merge : Bool) (M : Program (rawCount c) k 2)
    (n : ℕ) (s : Shape) (ell p rho left count slots right source target : ℕ)
    (hc : 0<c) (hn : 0<n) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (before after : Tapes (1+c) 2)
    (hm : HoareTime M
      (fun v => v=preparedRaw before (words merge n c s ell p))
      (fun v => v=preparedRaw after (words merge n c s ell p))
      (transferCost merge n c s ell p)) :
    HoareTime (assembly c merge M)
      (fun v => v=bank (raw s (n*c) ell p rho left count slots right source target) before)
      (fun v => v=bank (raw s (n*c) ell p rho left count slots right source target) after)
      (cost merge n c s ell p rho left count slots right source target) := by
  have hgroup : 0<n*c/c := by rw [Nat.mul_div_cancel n hc]; exact hn
  have h0 := hoare_extend_eq (CompactNativeRoleHeaders.runs c merge s (n*c) ell p rho left count slots right source target
    hc (Nat.mul_pos hn hc) hgroup hG hA hK) (blankRaw before)
  have h1 := CompactNativeRoleInstall.installs
    (ActiveRepairRankHeadersCommands.bank (a:=2) (prepared c merge s (n*c) ell p rho left count slots right source target))
    before (words merge n c s ell p) (source_headers merge n c s ell p rho left count slots right source target hc)
  have h2 := CompactNativeRoleInstall.initializes_runs
    (ActiveRepairRankHeadersCommands.bank (a:=2) (prepared c merge s (n*c) ell p rho left count slots right source target))
    before (words merge n c s ell p)
  have h3 := RecursiveRowsConstruct.left_frame hm
    (ActiveRepairRankHeadersCommands.bank (a:=2) (prepared c merge s (n*c) ell p rho left count slots right source target))
  have h4 := RecursiveRowsConstruct.left_frame (CompactNativeRoleInstall.cleanup_runs after (words merge n c s ell p))
    (ActiveRepairRankHeadersCommands.bank (a:=2) (prepared c merge s (n*c) ell p rho left count slots right source target))
  have h5 := hoare_extend_eq (CompactNativeRoleHeaders.cleanup_runs c merge s (n*c) ell p rho left count slots right source target)
    (blankRaw after)
  exact (((((h0.seq h1).seq h2).seq h3).seq h4).seq h5).consequence (fun _ h => h) (fun _ h => h)
    (by unfold cost; omega)

theorem splits (n c : ℕ) (s : Shape) (ell p rho left count slots right source target : ℕ)
    (hc : 0<c) (hn : 0<n) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (f : Array n c (inner s ell)) (hw : ∀ z,(f z).1.length=recordWidth s p ∧ (f z).2.length=recordWidth s p) :
    HoareTime (splitProgram c)
      (fun v => v=bank (raw s (n*c) ell p rho left count slots right source target) (sourcePayload s ell f))
      (fun v => v=bank (raw s (n*c) ell p rho left count slots right source target) (rolePayload s ell f))
      (cost false n c s ell p rho left count slots right source target) := by
  apply assembled c false _ n s ell p rho left count slots right source target hc hn hG hA hK
  simpa [sourcePayload,rolePayload,preparedRaw,words,transferCost,erased,symbols,inner,
    CompactNativeRoleDestructive.bank,CompactNativeRoleDestructive.withCount,CompactNativeRoleTransfer.input,
    CompactNativeRoleTransfer.roles,RecursiveRowsInstall.prepared,CyclicRowSplit.bank,CyclicRowCopy.bank,
    CountedLoopReuseAlphabet.bank,Nat.mul_assoc] using CompactNativeRoleDestructive.split_runs (recordWidth s p) f hw

theorem merges (n c : ℕ) (s : Shape) (ell p rho left count slots right source target : ℕ)
    (hc : 0<c) (hn : 0<n) (hG : 0<s.guard) (hA : 0<s.axes) (hK : 0<s.chunk)
    (f : Array n c (inner s ell)) (hw : ∀ z,(f z).1.length=recordWidth s p ∧ (f z).2.length=recordWidth s p) :
    HoareTime (mergeProgram c)
      (fun v => v=bank (raw s (n*c) ell p rho left count slots right source target) (rolePayload s ell f))
      (fun v => v=bank (raw s (n*c) ell p rho left count slots right source target) (sourcePayload s ell f))
      (cost true n c s ell p rho left count slots right source target) := by
  apply assembled c true _ n s ell p rho left count slots right source target hc hn hG hA hK
  simpa [sourcePayload,rolePayload,preparedRaw,words,transferCost,erased,symbols,inner,
    CompactNativeRoleDestructive.bank,CompactNativeRoleDestructive.withCount,CompactNativeRoleTransfer.input,
    CompactNativeRoleTransfer.roles,RecursiveRowsInstall.prepared,CyclicRowSplit.bank,CyclicRowCopy.bank,
    CountedLoopReuseAlphabet.bank,Nat.mul_assoc] using CompactNativeRoleDestructive.merge_runs (recordWidth s p) f hw

end
end IntegerMultBounds.Machine.CompactNativeRoleOriginal
