import IntegerMultBounds.Machine.CompactSpectatorLeafSetup
import IntegerMultBounds.Machine.CompactSpectatorLeafLoop
import IntegerMultBounds.Machine.BinaryDescriptorCopyPlaced

/-! A stopped-call leaf takes original thirteen native descriptors and immutable
ell/p words at retained ports. Every leaf-private descriptor is physically copied
or synthesized before the actual full-address native butterfly loop. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafOriginal
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactSpectatorVisitGeometry (Array)
open ActiveRepairRankHeadersCommands (State put)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)

abbrev localCount := 44+ButterflySpectatorPorts.count+2
abbrev tapes := localCount+15

def values (s : Shape) (rows ell p rho left count slots right source target : ℕ) : Fin 15 → ℕ :=
  ![s.chunk,s.axes,s.guard,s.active,rows,s.payload,slots,count,left,right,rho,source,target,ell,p]
def originals (vs : Fin 15 → ℕ) : Tapes 15 2 :=
  ⟨fun _ => 1,fun i => RadixZeroFill.encodedBinary (bits (vs i))⟩
def localBank (st : State) (f : ℤ → Fin 6) :=
  CountedLoopHeaderClean.bank (CompactSpectatorLeafAxis.bank st f)
def bank (st : State) (f : ℤ → Fin 6) (vs : Fin 15 → ℕ) :=
  (localBank st f).append (originals vs)
def destination : Fin 15 → Fin 28 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,17,18]
theorem destination_injective : Function.Injective destination := by decide

def target (j : Fin 15) : Fin tapes := Fin.castAdd 15 (Fin.castAdd 2
  (Fin.castAdd ButterflySpectatorPorts.count (Fin.castAdd 1 (Fin.castAdd 15 (destination j)))))
def focus (j : Fin 15) : Fin 2 → Fin tapes := ![Fin.natAdd localCount j,target j]
theorem focus_injective (j : Fin 15) : Function.Injective (focus j) := by
  intro i k h
  fin_cases i <;> fin_cases k
  · rfl
  · have hh := congrArg Fin.val h
    change localCount+j.val=(destination j).val at hh
    have hd := (destination j).isLt
    unfold localCount at hh
    omega
  · have hh := congrArg Fin.val h
    change (destination j).val=localCount+j.val at hh
    have hd := (destination j).isLt
    unfold localCount at hh
    omega
  · rfl

def copyProgram (j : Fin 15) := BinaryDescriptorCopyPlaced.program (a:=2) (focus j) (focus_injective j)

private theorem update_bank (st : State) (f : ℤ → Fin 6) (vs : Fin 15 → ℕ) (j : Fin 15) :
    setTape (bank st f vs) (target j) (RadixZeroFill.encodedBinary (bits (vs j))) 1=
      bank (put st (destination j) (vs j)) f vs := by
  unfold bank localBank CountedLoopHeaderClean.bank CompactSpectatorLeafAxis.bank CompactSpectatorLeafAxis.common target
  repeat rw [SharedPlacementAlphabet.setTape_append_left]
  unfold ActiveRepairRankHeadersCommands.bank CleanSubbank.bank
  rw [SharedPlacementAlphabet.setTape_append_left,← ActiveRepairRankHeadersCommands.put_caller]


private theorem copy_runs (st : State) (f : ℤ → Fin 6) (vs : Fin 15 → ℕ) (j : Fin 15)
    (hz : st (destination j)=none) :
    HoareTime (copyProgram j) (fun v => v=bank st f vs)
      (fun v => v=bank (put st (destination j) (vs j)) f vs) (2*(vs j)+7) := by
  have hh := BinaryDescriptorCopyPlaced.copies (bank st f vs) (focus j) (focus_injective j) (bits (vs j)) (by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [focus,target,bank,localBank,CountedLoopHeaderClean.bank,
      CompactSpectatorLeafAxis.bank,CompactSpectatorLeafAxis.common,ActiveRepairRankHeadersCommands.bank,
      CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller,originals,Tapes.append,Copy.cfg,hz])
  have hl := GrowingCounterData.canonical_width (bits (vs j)) (RecursiveChildQuotientsConstant.bits_canonical _)
  rw [RecursiveChildQuotientsConstant.bits_value] at hl
  have hlog := Nat.log2_le_self (vs j)
  exact hh.consequence (fun _ h => h) (fun v hv => hv.trans (update_bank st f vs j)) (by omega)

def copies : List (Fin 15) → Σ q,Program tapes q 2
  | [] => ⟨1,skip tapes 2 (by decide)⟩
  | j::js => ⟨_,seq (copyProgram j) (copies js).2⟩
def copied : List (Fin 15) → State → (Fin 15 → ℕ) → State
  | [],st,_ => st
  | j::js,st,vs => copied js (put st (destination j) (vs j)) vs
def copyCost (js : List (Fin 15)) (vs : Fin 15 → ℕ) := (js.map (fun j => 2*(vs j)+8)).sum

theorem copies_runs (js : List (Fin 15)) (hn : js.Nodup) (st : State) (f : ℤ → Fin 6) (vs : Fin 15 → ℕ)
    (hz : ∀ j∈js,st (destination j)=none) :
    HoareTime (copies js).2 (fun v => v=bank st f vs)
      (fun v => v=bank (copied js st vs) f vs) (copyCost js vs) := by
  induction js generalizing st with
  | nil => exact skip_hoare (by decide) (bank st f vs)
  | cons j js ih =>
    have hn' := List.nodup_cons.mp hn
    have hc := copy_runs st f vs j (hz j (by simp))
    have ht := ih hn'.2 (put st (destination j) (vs j)) (by
      intro k hk
      have hkj : destination k≠destination j := by
        intro he; have := destination_injective he; subst k; exact hn'.1 hk
      simpa [put,Function.update,hkj] using hz k (by simp [hk]))
    exact (hc.seq ht).consequence (fun _ h => h) (fun _ h => h) (by simp [copyCost])

def inputs : List (Fin 15) := List.finRange 15

theorem copied_inputs (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    copied inputs (fun _ => none) (values s rows ell p rho left count slots right source target)=
      CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right source target := by
  funext i
  fin_cases i <;> simp [copied,inputs,List.finRange,values,destination,put,Function.update,
    CompactSpectatorLeafSetup.raw]

def setup := extend (extend (extend (extend
  (ButterflyAxisHeadersArithmetic.compile (a:=2) CompactSpectatorLeafSetup.schedule).2 1)
  ButterflySpectatorPorts.count) 2) 15

def program := seq (seq (copies inputs).2 setup) (extend CompactSpectatorLeafLoop.program 15)


def cost (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ} (visit : Visit s.active left k)
    (slots right source target : ℕ) :=
  copyCost inputs (values s rows ell p rho.val left (arity^k) slots right source target)+
  ButterflyAxisHeadersArithmetic.scheduleCost CompactSpectatorLeafSetup.schedule
    (CompactSpectatorLeafSetup.raw s rows ell p rho.val left (arity^k) slots right source target)+
  CompactSpectatorLeafLoop.cost s rows ell p rho visit+2

private theorem assembled {u v z : ℕ} (A : Program tapes u 2) (B : Program tapes v 2) (C : Program tapes z 2)
    (input middle next output : Tapes tapes 2) (ca cb cc : ℕ)
    (ha : HoareTime A (fun x => x=input) (fun x => x=middle) ca)
    (hb : HoareTime B (fun x => x=middle) (fun x => x=next) cb)
    (hc : HoareTime C (fun x => x=next) (fun x => x=output) cc) :
    HoareTime (seq (seq A B) C) (fun x => x=input) (fun x => x=output) (ca+cb+cc+2) := by
  exact ((ha.seq hb).seq hc).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem runs (s : Shape) (rows ell p : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows) (f : Array s rows ell)
    (hw : ButterflySpectatorGeometry.Width rows s.bits (2^ell) p f) :
    HoareTime program
      (fun v => v=bank (fun _ => none) (CompactSpectatorLeafAxis.word f)
        (values s rows ell p rho.val left (arity^k) slots right source target))
      (fun v => v=(CompactSpectatorLeafLoop.output s rows ell p rho visit f).append
        (originals (values s rows ell p rho.val left (arity^k) slots right source target)))
      (cost s rows ell p rho visit slots right source target) := by
  let vs := values s rows ell p rho.val left (arity^k) slots right source target
  have hK : 0<s.chunk := by have := rho.isLt; omega
  have h0 := copies_runs inputs (List.nodup_finRange _) (fun _ => none) (CompactSpectatorLeafAxis.word f) vs
    (fun _ _ => rfl)
  dsimp [vs] at h0
  rw [copied_inputs] at h0
  have h1 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (CompactSpectatorLeafSetup.runs s rows ell p rho.val left (arity^k) slots right source target hG hA hK)
    (CountedLoopReuseAlphabet.one (CompactSpectatorLeafAxis.word f) 0))
    (SharedBank.empty ButterflySpectatorPorts.count 2)) (SharedBank.empty 2 2)) (originals vs)
  have h2 := hoare_extend_eq (CompactSpectatorLeafLoop.runs s rows ell p rho visit hr f hw) (originals vs)
  have hz : CompactSpectatorLeafLoop.bank s rows ell p rho visit 0 f=
      localBank (CompactSpectatorLeafHeaders.initial s rows ell p rho.val left (arity^k))
        (CompactSpectatorLeafAxis.word f) := by simp [CompactSpectatorLeafLoop.bank,
          CompactSpectatorLeafLoop.endpoint,CompactSpectatorLeafLoop.run,localBank]
  rw [hz] at h2
  exact assembled _ _ _ _ _ _ _ _ _ _ h0 h1 h2

end
end IntegerMultBounds.Machine.CompactSpectatorLeafOriginal
