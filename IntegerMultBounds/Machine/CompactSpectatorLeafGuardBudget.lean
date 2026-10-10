import IntegerMultBounds.Machine.CompactSpectatorLeafGuardPlacement
import IntegerMultBounds.Machine.CompactSpectatorLeafSetupBudget
import IntegerMultBounds.Machine.CompactSpectatorLeafLoopBudget

/-! The actual retained native payload and fixed recursive pair bounds charge
all original metadata to the complete native word. Paid guard synthesis and
both descriptor lifecycles preserve a uniform volume-times-visit-count bound. -/
namespace IntegerMultBounds.Machine.CompactSpectatorLeafGuardBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open ButterflyIndependentGuardHeaders (reservation)
open CompactSpectatorLeafOriginal
open ButterflyAxisHeadersArithmetic
open CompactSpectatorLeafGuardOriginal (Direction)

abbrev volume (s : Shape) (rows ell q : ℕ) := CompactSpectatorLeafAxisBudget.volume s rows ell (reservation s.bits q)

theorem scalar_le (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (hslots : slots≤arity) (hright : right≤s.active) (hsource : source≤arity) (htarget : target≤arity)
    (hpayload : s.payload=3*(2^ell*ButterflyAxisHeadersData.recordLength s.bits (reservation s.bits q))) :
    CompactSpectatorLeafSetupBudget.scalar s rows ell q rho.val left (arity^k) slots right source target≤
      (3*arity+20)*volume s rows ell q := by
  have hn : 0<arity^k := pow_pos (by decide) _
  have hf := visit.fits
  have ho : left<s.active := by omega
  obtain ⟨hH,hB,hactive,hchunk,hrho,hleft,_,_⟩ := CompactSpectatorLeafAxisBudget.descriptors s rho.val left rho.isLt ho
  obtain ⟨hbits,hp,hpoly,hell,hrows⟩ := CompactSpectatorLeafLoopBudget.volume_values s rows ell (reservation s.bits q) hr
  have haxes : s.axes≤s.H := Nat.le_mul_of_pos_right _ hG
  have hguard : s.guard≤s.H := by
    simpa only [Shape.H,CompactGadgetReservationCapacity.capacity,Nat.mul_comm] using Nat.le_mul_of_pos_right s.guard hA
  have hq : q≤reservation s.bits q := by unfold reservation; omega
  have hV := ButterflySpectatorBudget.positive rows s.bits (2^ell) (reservation s.bits q) hr (pow_pos (by decide) _)
  change 0<volume s rows ell q at hV
  have hrow : 1≤rows*2^s.bits := by
    simpa using Nat.mul_le_mul (show 1≤rows by omega) (Nat.one_le_two_pow (n:=s.bits))
  have hnative := Nat.mul_le_mul_right (2^ell*ButterflyAxisHeadersData.recordLength s.bits (reservation s.bits q)) hrow
  have heq : volume s rows ell q=(rows*2^s.bits)*(2^ell*ButterflyAxisHeadersData.recordLength s.bits (reservation s.bits q)) := by
    unfold volume CompactSpectatorLeafAxisBudget.volume ButterflySpectatorBudget.volume ButterflyAxisHeadersBudget.logicalVolume
    ring
  have hnative' : 2^ell*ButterflyAxisHeadersData.recordLength s.bits (reservation s.bits q)≤volume s rows ell q := by
    rw [heq]; simpa using hnative
  have hpay : s.payload≤3*volume s rows ell q := by rw [hpayload]; exact Nat.mul_le_mul_left 3 hnative'
  have hslotV := Nat.le_mul_of_pos_right arity hV
  unfold CompactSpectatorLeafSetupBudget.scalar
  nlinarith only [hn,hf,hH,hactive,hchunk,hrho,hleft,hbits,hp,hell,hrows,haxes,hguard,hq,hV,hpay,hslots,hright,hsource,htarget,hslotV]

private theorem copy_bound (js : List (Fin 15)) (vs : Fin 15 → ℕ) (S : ℕ) (hv : ∀ j,vs j≤S) :
    copyCost js vs≤js.length*(2*S+8) := by
  induction js with
  | nil => simp [copyCost]
  | cons j js ih =>
    have hj := hv j
    simp only [copyCost,List.map_cons,List.sum_cons,List.length_cons] at *
    rw [Nat.add_mul]
    omega

theorem copies_cost (s : Shape) (rows ell q rho left count slots right source target : ℕ) :
    copyCost inputs (values s rows ell q rho left count slots right source target)≤
      150*CompactSpectatorLeafSetupBudget.scalar s rows ell q rho left count slots right source target := by
  let S := CompactSpectatorLeafSetupBudget.scalar s rows ell q rho left count slots right source target
  have hp : 0<S := by unfold S CompactSpectatorLeafSetupBudget.scalar; omega
  have hv (j : Fin 15) : values s rows ell q rho left count slots right source target j≤S := by
    fin_cases j <;> simp [values,S,CompactSpectatorLeafSetupBudget.scalar] <;> omega
  have hh := copy_bound inputs (values s rows ell q rho left count slots right source target) S hv
  change copyCost inputs _≤15*(2*S+8) at hh
  change copyCost inputs _≤150*S
  omega

theorem reserve_cost (s : Shape) (rows ell q rho left count : ℕ) (hr : 0<rows) :
    scheduleCost CompactSpectatorLeafGuardHeaders.schedule (CompactSpectatorLeafHeaders.initial s rows ell q rho left count)≤
      1000*volume s rows ell q := by
  obtain ⟨hb,hp,_,_,_⟩ := CompactSpectatorLeafLoopBudget.volume_values s rows ell (reservation s.bits q) hr
  change s.bits≤volume s rows ell q at hb
  change reservation s.bits q≤volume s rows ell q at hp
  have hq : q≤reservation s.bits q := by unfold reservation; omega
  have hV := ButterflySpectatorBudget.positive rows s.bits (2^ell) (reservation s.bits q) hr (pow_pos (by decide) _)
  change 0<volume s rows ell q at hV
  simp [CompactSpectatorLeafGuardHeaders.schedule,scheduleCost,ButterflyAxisHeadersArithmetic.cost,ButterflyAxisHeadersData.cmd,eval,CompactChildHeadersArithmetic.cost,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    CompactSpectatorLeafHeaders.initial,Function.update]
  omega

def phaseConstant := 200150*(3*arity+20)+1000+CompactSpectatorLeafLoopBudget.constant+3

theorem phase_cost (dir : Direction) (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (hslots : slots≤arity) (hright : right≤s.active) (hsource : source≤arity) (htarget : target≤arity)
    (hpayload : s.payload=3*(2^ell*ButterflyAxisHeadersData.recordLength s.bits (reservation s.bits q))) :
    CompactSpectatorLeafGuardOriginal.phaseCost dir s rows ell q rho visit slots right source target≤
      phaseConstant*volume s rows ell q*(arity^k) := by
  have hK : 0<s.chunk := by have := rho.isLt; omega
  have hH : 0<s.H := Nat.mul_pos hA hG
  have hc := copies_cost s rows ell q rho.val left (arity^k) slots right source target
  have hs := CompactSpectatorLeafSetupBudget.cost_linear s rows ell q rho.val left (arity^k) slots right source target hH hK
  have hg := reserve_cost s rows ell q rho.val left (arity^k) hr
  have hv := scalar_le s rows ell q rho visit slots right source target hG hA hr hslots hright hsource htarget hpayload
  have hm : CompactSpectatorLeafGuardOriginal.loopCost dir s rows ell q rho visit≤
      CompactSpectatorLeafLoopBudget.constant*volume s rows ell q*(arity^k) := by
    cases dir
    · exact CompactSpectatorLeafLoopBudget.cost_linear s rows ell (reservation s.bits q) rho visit hr
    · exact CompactSpectatorLeafLoopBudget.inverse_cost_linear s rows ell (reservation s.bits q) rho visit hr
  have hV := ButterflySpectatorBudget.positive rows s.bits (2^ell) (reservation s.bits q) hr (pow_pos (by decide) _)
  change 0<volume s rows ell q at hV
  have hn : 0<arity^k := pow_pos (by decide) _
  have hcharge := Nat.mul_le_mul_left 200150 hv
  unfold CompactSpectatorLeafGuardOriginal.phaseCost phaseConstant
  nlinarith only [hc,hs,hg,hm,hV,hn,hcharge]

def constant := 2*phaseConstant+1

theorem cost_linear (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (hslots : slots≤arity) (hright : right≤s.active) (hsource : source≤arity) (htarget : target≤arity)
    (hpayload : s.payload=3*(2^ell*ButterflyAxisHeadersData.recordLength s.bits (reservation s.bits q))) :
    CompactSpectatorLeafGuardOriginal.cost s rows ell q rho visit slots right source target≤
      constant*volume s rows ell q*(arity^k) := by
  have hf := phase_cost .forward s rows ell q rho visit slots right source target hG hA hr hslots hright hsource htarget hpayload
  have hi := phase_cost .inverse s rows ell q rho visit slots right source target hG hA hr hslots hright hsource htarget hpayload
  have hV := ButterflySpectatorBudget.positive rows s.bits (2^ell) (reservation s.bits q) hr (pow_pos (by decide) _)
  change 0<volume s rows ell q at hV
  have hn : 0<arity^k := pow_pos (by decide) _
  unfold CompactSpectatorLeafGuardOriginal.cost constant
  nlinarith only [hf,hi,hV,hn]

theorem correct_uniform {w : ℕ} (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left k) (slots right sourceSlot targetSlot : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows) (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hslots : slots≤arity) (hright : right≤s.active) (hsource : sourceSlot≤arity) (htarget : targetSlot≤arity)
    (hpayload : s.payload=3*(2^ell*ButterflyAxisHeadersData.recordLength s.bits (reservation s.bits q)))
    (hfields : ∀ i,(f i).1.length=q+4*s.bits+4 ∧ (f i).2.length=q+4*s.bits+4)
    (hu : ∀ i,‖ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q 0 f i‖≤1)
    (caller : Tapes (CompactSpectatorLeafPlacement.callerCount w) 2)
    (hdata : SharedBank.payload caller CompactSpectatorLeafPlacement.common=CompactSpectatorLeafPlacement.payload (CompactSpectatorLeafAxis.word f)
      (values s rows ell q rho.val left (arity^k) slots right sourceSlot targetSlot)) :
    HoareTime (CompactSpectatorLeafGuardPlacement.program (w:=w))
      (fun v => v=CleanSubbank.bank (s:=CompactSpectatorLeafOriginal.tapes) caller)
      (fun v => v=CleanSubbank.bank (s:=CompactSpectatorLeafOriginal.tapes)
        (SharedPlacementAlphabet.setTape caller (CompactSpectatorLeafPlacement.common (Fin.castAdd 15 (0 : Fin 1)))
          (CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)) 0) ∧
        ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q (2*arity^k)
          (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)=
          ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q 0 f)
      (constant*volume s rows ell q*(arity^k)) := by
  have hh := CompactSpectatorLeafGuardPlacement.correct (w:=w) s rows ell q rho visit slots right sourceSlot targetSlot
    hG hA hr f hfields hu caller hdata
  exact hh.consequence (fun _ h => h) (fun _ h => h)
    (cost_linear s rows ell q rho visit slots right sourceSlot targetSlot hG hA hr hslots hright hsource htarget hpayload)

end
end IntegerMultBounds.Machine.CompactSpectatorLeafGuardBudget
