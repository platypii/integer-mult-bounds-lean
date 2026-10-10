import IntegerMultBounds.Machine.CompactSpectatorLeafCountBudget
import IntegerMultBounds.Machine.CompactSpectatorLeafGuardBudget
import IntegerMultBounds.Machine.CompactSpectatorLeafCutoffBudget

/-! The stopped-node leaf physically expands original header7 by original
slots6, executes the actual guarded butterfly pair at native65/global109,
then restores the original node headers. The scalar branch keeps count1.
An appended clean43-tape arithmetic workspace frames every original tape. -/
namespace IntegerMultBounds.Machine.CompactSpectatorStoppedLeafCaller
noncomputable section
open CompactSpectatorLeafOriginal
open CompactSpectatorLeafPlacement
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open ActiveRepairRankHeadersCommands (State put)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {w : ℕ}

def raw (vs : Fin 13 → ℕ) : State := fun i =>
  if h : i.val<13 then some (vs ⟨i.val,h⟩) else none
def arithPorts : Fin 13 → Fin 43 := Fin.castAdd 15 ∘ Fin.castAdd 15

theorem arithPorts_injective : Function.Injective arithPorts := by
  intro i j h
  exact Fin.castAdd_injective _ _ (Fin.castAdd_injective _ _ h)

def originals13 (vs : Fin 13 → ℕ) : Tapes 13 2 :=
  ⟨fun _ => 1,fun i => RadixZeroFill.encodedBinary (bits (vs i))⟩

private theorem arith_payload (vs : Fin 13 → ℕ) :
    SharedBank.payload (ActiveRepairRankHeadersCommands.bank (a:=2) (raw vs)) arithPorts=originals13 vs := by
  apply congrArg₂ Tapes.mk
  · funext i
    simp [arithPorts,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,raw,Tapes.append]
  · funext i
    simp [arithPorts,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,raw,Tapes.append]

private theorem arith_clean (vs : Fin 13 → ℕ) :
    SharedBank.strip (ActiveRepairRankHeadersCommands.bank (a:=2) (raw vs)) arithPorts=SharedBank.empty 43 2 := by
  have selected (i : Fin 43) : (∃ j,arithPorts j=i) ↔ i.val<13 := by
    constructor
    · rintro ⟨j,rfl⟩; exact j.isLt
    · intro h; exact ⟨⟨i.val,h⟩,Fin.ext rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i.val<13
  all_goals simp only [selected,hi,ite_true,ite_false]
  all_goals induction i using Fin.addCases with
  | left i =>
      have hi' : ¬i.val<13 := hi
      simp [ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller,
        raw,Tapes.append,SharedBank.empty,hi']
  | right i => simp [ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,SharedBank.empty]

abbrev outer := callerCount w+tapes
abbrev total := outer (w:=w)+43

def countCommon : Fin 13 → Fin (outer (w:=w)) := fun i =>
  Fin.castAdd tapes (descriptor (Fin.castAdd 2 i))
theorem countCommon_injective : Function.Injective (countCommon (w:=w)) := by
  intro i j h
  have he := Fin.castAdd_injective _ _ h
  have hv := congrArg Fin.val he
  simp only [descriptor,Fin.addCases_left,Fin.val_castAdd] at hv
  exact Fin.ext (by omega)

def countProgram (ops : List CompactChildHeadersArithmetic.Op) :=
  Placement.placed (CompactChildHeadersArithmetic.compile (a:=2) ops).2
    (CleanSubbank.placement arithPorts (countCommon (w:=w)) countCommon_injective)

private theorem count_lift (ops : List CompactChildHeadersArithmetic.Op) (vs vt : Fin 13 → ℕ)
    (c : ℕ) (caller after : Tapes (outer (w:=w)) 2)
    (hin : SharedBank.payload caller countCommon=originals13 vs)
    (hout : SharedBank.payload after countCommon=originals13 vt)
    (hframe : SharedBank.strip caller countCommon=SharedBank.strip after countCommon)
    (hrun : HoareTime (CompactChildHeadersArithmetic.compile (a:=2) ops).2
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw vs))
      (fun v => v=ActiveRepairRankHeadersCommands.bank (raw vt)) c) :
    HoareTime (countProgram (w:=w) ops)
      (fun v => v=CleanSubbank.bank (s:=43) caller)
      (fun v => v=CleanSubbank.bank (s:=43) after) c := by
  apply CleanSubbank.realizes _ arithPorts countCommon arithPorts_injective countCommon_injective
    caller after (ActiveRepairRankHeadersCommands.bank (raw vs))
    (ActiveRepairRankHeadersCommands.bank (raw vt)) _
    ?_ ?_ (arith_clean vs) (arith_clean vt) ?_ hrun
  · rw [arith_payload]; exact hin.symm
  · rw [arith_payload]; exact hout.symm
  · exact hframe

private theorem payload_update {n c : ℕ} (v : Tapes n 2) (ps : Fin c → Fin n)
    (hp : Function.Injective ps) (j : Fin c) (f : ℤ → Fin 6) (p : ℤ) :
    SharedBank.payload (setTape v (ps j) f p) ps=setTape (SharedBank.payload v ps) j f p := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i=j
  all_goals simp [SharedBank.payload,setTape,Function.update,hi,hp.eq_iff]

private theorem strip_update {n c : ℕ} (v : Tapes n 2) (ps : Fin c → Fin n)
    (j : Fin c) (f : ℤ → Fin 6) (p : ℤ) :
    SharedBank.strip (setTape v (ps j) f p) ps=SharedBank.strip v ps := by
  have hn (i : Fin n) (hi : ¬∃ k,ps k=i) : i≠ps j := fun h => hi ⟨j,h.symm⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : ∃ j,ps j=i
  all_goals simp only [hi,ite_true,ite_false]
  all_goals simp only [setTape,Function.update_of_ne (hn i hi)]

private theorem originals13_update (vs : Fin 13 → ℕ) (n : ℕ) :
    setTape (originals13 vs) 7 (RadixZeroFill.encodedBinary (bits n)) 1=
      originals13 (Function.update vs 7 n) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i=7
  all_goals simp [originals13,Function.update,hi]

private theorem raw_update (vs : Fin 13 → ℕ) (n : ℕ) :
    raw (Function.update vs 7 n)=put (raw vs) 7 n := by
  funext i
  by_cases hi : i=7
  · subst i; simp [raw,put,Function.update]
  · have hh : ∀ h : i.val<13,(⟨i.val,h⟩ : Fin 13)≠7 := by
      intro h he
      have hv : i.val=7 := congrArg (fun j : Fin 13 => j.val) he
      exact hi (Fin.ext hv)
    simp [raw,put,Function.update,hi,hh]

private theorem count_expand (vs : Fin 13 → ℕ) (caller : Tapes (outer (w:=w)) 2)
    (hin : SharedBank.payload caller countCommon=originals13 vs) (hc : 0<vs 7) :
    HoareTime (countProgram (w:=w) CompactSpectatorLeafCountBudget.expand)
      (fun v => v=CleanSubbank.bank (s:=43) caller)
      (fun v => v=CleanSubbank.bank (s:=43)
        (setTape caller (countCommon 7) (RadixZeroFill.encodedBinary (bits (vs 7*vs 6))) 1))
      (CompactChildHeadersArithmetic.scheduleCost CompactSpectatorLeafCountBudget.expand (raw vs)) := by
  have hh := CompactSpectatorLeafCountBudget.expand_runs (a:=2) (raw vs) (vs 6) (vs 7) rfl rfl rfl hc
  unfold CompactSpectatorLeafCountBudget.expanded at hh
  rw [← raw_update] at hh
  apply count_lift _ vs (Function.update vs 7 (vs 7*vs 6)) _ caller _ hin ?_ ?_ hh
  · rw [payload_update _ _ countCommon_injective,hin,originals13_update]
  · exact (strip_update _ _ _ _ _).symm

private theorem count_restore (vs : Fin 13 → ℕ) (caller : Tapes (outer (w:=w)) 2)
    (hin : SharedBank.payload caller countCommon=originals13 vs) (hs : 0<vs 6) :
    HoareTime (countProgram (w:=w) CompactSpectatorLeafCountBudget.restore)
      (fun v => v=CleanSubbank.bank (s:=43)
        (setTape caller (countCommon 7) (RadixZeroFill.encodedBinary (bits (vs 7*vs 6))) 1))
      (fun v => v=CleanSubbank.bank (s:=43) caller)
      (CompactChildHeadersArithmetic.scheduleCost CompactSpectatorLeafCountBudget.restore
        (CompactSpectatorLeafCountBudget.expanded (raw vs) (vs 6) (vs 7))) := by
  have hh := CompactSpectatorLeafCountBudget.restore_runs (a:=2) (raw vs) (vs 6) (vs 7) rfl rfl rfl hs
  unfold CompactSpectatorLeafCountBudget.expanded at hh
  rw [← raw_update] at hh
  apply count_lift _ (Function.update vs 7 (vs 7*vs 6)) vs _ _ caller ?_ hin ?_ hh
  · rw [payload_update _ _ countCommon_injective,hin,originals13_update]
  · exact strip_update _ _ _ _ _

def trim (vs : Fin 15 → ℕ) : Fin 13 → ℕ := fun i => vs (Fin.castAdd 2 i)
def countSlot : Fin (callerCount w) := descriptor (Fin.castAdd 2 (7 : Fin 13))
def sourceSlot : Fin (callerCount w) := common (Fin.castAdd 15 (0 : Fin 1))
def setCount (caller : Tapes (callerCount w) 2) (n : ℕ) :=
  setTape caller countSlot (RadixZeroFill.encodedBinary (bits n)) 1

def updateSource (caller : Tapes (callerCount w) 2) (f : ℤ → Fin 6) := setTape caller sourceSlot f 0

theorem count_payload (caller : Tapes (callerCount w) 2) (f : ℤ → Fin 6) (vs : Fin 15 → ℕ)
    (hd : SharedBank.payload caller common=payload f vs) :
    SharedBank.payload (CleanSubbank.bank (s:=tapes) caller) countCommon=originals13 (trim vs) := by
  apply congrArg₂ Tapes.mk <;> funext i
  · have hh := congrFun (congrArg Tapes.head hd) (Fin.natAdd 1 (Fin.castAdd 2 i))
    simpa [SharedBank.payload,countCommon,common,payload,CleanSubbank.bank,Tapes.append,originals,originals13] using hh
  · have hh := congrFun (congrArg Tapes.tape hd) (Fin.natAdd 1 (Fin.castAdd 2 i))
    simpa [SharedBank.payload,countCommon,common,payload,CleanSubbank.bank,Tapes.append,originals,originals13,trim] using hh

private theorem payload_count_update (f : ℤ → Fin 6) (vs : Fin 15 → ℕ) (n : ℕ) :
    setTape (payload f vs) (Fin.natAdd 1 (7 : Fin 15)) (RadixZeroFill.encodedBinary (bits n)) 1=
      payload f (Function.update vs 7 n) := by
  unfold payload
  rw [SharedPlacementAlphabet.setTape_append_right]
  congr 1
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : i=7
  all_goals simp [originals,Function.update,hi]

private theorem expanded_data (caller : Tapes (callerCount w) 2) (f : ℤ → Fin 6) (vs : Fin 15 → ℕ) (n : ℕ)
    (hd : SharedBank.payload caller common=payload f vs) :
    SharedBank.payload (setCount caller n) common=payload f (Function.update vs 7 n) := by
  have he : countSlot (w:=w)=common (Fin.natAdd 1 (7 : Fin 15)) := rfl
  unfold setCount
  rw [he,payload_update _ _ common_injective,hd,payload_count_update]

private theorem source_data (caller : Tapes (callerCount w) 2) (f g : ℤ → Fin 6) (vs : Fin 15 → ℕ)
    (hd : SharedBank.payload caller common=payload f vs) :
    SharedBank.payload (updateSource caller g) common=payload g vs := by
  unfold updateSource sourceSlot
  rw [payload_update _ _ common_injective,hd]
  unfold payload
  rw [SharedPlacementAlphabet.setTape_append_left]
  congr 1
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem updates_commute (caller : Tapes (callerCount w) 2) (n : ℕ) (f : ℤ → Fin 6) :
    updateSource (setCount caller n) f=setCount (updateSource caller f) n := by
  have hn : countSlot (w:=w)≠sourceSlot := by
    intro h; have hv := congrArg Fin.val h
    change 51=109 at hv
    omega
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i=countSlot
  all_goals by_cases hj : i=sourceSlot
  all_goals simp_all [updateSource,setCount,setTape,Function.update]

private theorem count_bank_update (caller : Tapes (callerCount w) 2) (n : ℕ) :
    setTape (CleanSubbank.bank (s:=tapes) caller) (countCommon 7)
      (RadixZeroFill.encodedBinary (bits n)) 1=
        CleanSubbank.bank (s:=tapes) (setCount caller n) := by
  unfold countCommon CleanSubbank.bank setCount countSlot
  exact SharedPlacementAlphabet.setTape_append_left _ _ _ _ _

def nodeValues (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) : Fin 15 → ℕ :=
  values s rows ell q rho.val left (arity^k) arity
    (node rho visit hactive).right pair.source.val pair.target.val

theorem node_originals (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) :
    trim (nodeValues s rows ell q rho visit hactive pair)=
      ActivePrefixStageHeadersData.originalValues (CompactBinaryBasisSchedule.stage (node rho visit hactive) pair) rows := by
  funext i
  fin_cases i <;> rfl

private theorem node_expanded_values (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) :
    Function.update (nodeValues s rows ell q rho visit hactive pair) 7 (arity^k*arity)=
      values s rows ell q rho.val left (arity^(k+1)) arity
        (node rho visit hactive).right pair.source.val pair.target.val := by
  funext i
  fin_cases i <;> simp [nodeValues,values,Function.update,pow_succ]

def positiveProgram := seq (seq (countProgram (w:=w) CompactSpectatorLeafCountBudget.expand)
  (extend (CompactSpectatorLeafGuardPlacement.program (w:=w)) 43))
  (countProgram (w:=w) CompactSpectatorLeafCountBudget.restore)

def positiveCost (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) :=
  let vs := trim (nodeValues s rows ell q rho visit hactive pair)
  CompactChildHeadersArithmetic.scheduleCost CompactSpectatorLeafCountBudget.expand (raw vs)+
  CompactSpectatorLeafGuardOriginal.cost s rows ell q rho visit arity
    (node rho visit hactive).right pair.source.val pair.target.val+
  CompactChildHeadersArithmetic.scheduleCost CompactSpectatorLeafCountBudget.restore
    (CompactSpectatorLeafCountBudget.expanded (raw vs) arity (arity^k))+2

theorem positive_runs (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (nodeValues s rows ell q rho visit hactive pair)) :
    HoareTime (positiveProgram (w:=w))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes)
        (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)))))
      (positiveCost s rows ell q rho visit hactive pair) := by
  let vs := nodeValues s rows ell q rho visit hactive pair
  let g := CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)
  have hin := count_payload caller (CompactSpectatorLeafAxis.word f) vs hd
  have hc : 0<trim vs 7 := pow_pos (by decide) _
  have he := count_expand (w:=w) (trim vs) (CleanSubbank.bank (s:=tapes) caller) hin hc
  rw [count_bank_update] at he
  have hdata := expanded_data caller (CompactSpectatorLeafAxis.word f) vs (arity^k*arity) hd
  rw [node_expanded_values] at hdata
  have hl := CompactSpectatorLeafGuardPlacement.runs (w:=w) s rows ell q rho visit arity
    (node rho visit hactive).right pair.source.val pair.target.val hG hA hr f hw
    (setCount caller (arity^k*arity)) hdata
  have hl' := hoare_extend_eq hl (SharedBank.empty 43 2)
  change HoareTime (extend (CompactSpectatorLeafGuardPlacement.program (w:=w)) 43)
    (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) (setCount caller (arity^k*arity))))
    (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) (updateSource (setCount caller (arity^k*arity)) g))) _ at hl'
  rw [updates_commute] at hl'
  have hout := count_payload (updateSource caller g) g vs (source_data caller _ g vs hd)
  have hs : 0<trim vs 6 := by change 0<arity; decide
  have hre := count_restore (w:=w) (trim vs) (CleanSubbank.bank (s:=tapes) (updateSource caller g)) hout hs
  rw [count_bank_update] at hre
  have h := (he.seq hl').seq hre
  exact h.consequence (fun _ h => h) (fun _ h => h) (by dsimp [positiveCost,vs,trim,nodeValues,values]; omega)

def scalarProgram := extend (CompactSpectatorLeafGuardPlacement.program (w:=w)) 43

theorem scalar_runs (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left : ℕ}
    (visit : Visit s.active left 0) (right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (values s rows ell q rho.val left 1 arity right source target)) :
    HoareTime (scalarProgram (w:=w))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes)
        (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)))))
      (CompactSpectatorLeafGuardOriginal.cost s rows ell q rho visit arity right source target) :=
  hoare_extend_eq (CompactSpectatorLeafGuardPlacement.runs (w:=w) s rows ell q rho visit arity
    right source target hG hA hr f hw caller hd) (SharedBank.empty 43 2)

theorem positive_correct (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hf : ∀ i,(f i).1.length=q+4*s.bits+4 ∧ (f i).2.length=q+4*s.bits+4)
    (hu : ∀ i,‖ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q 0 f i‖≤1)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (nodeValues s rows ell q rho visit hactive pair)) :
    HoareTime (positiveProgram (w:=w))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes)
        (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)))) ∧
        ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q (2*arity^(k+1))
          (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)=
          ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q 0 f)
      (positiveCost s rows ell q rho visit hactive pair) := by
  have hw := CompactSpectatorLeafGuardHeaders.readiness s rows ell q f hf
  have hh := positive_runs s rows ell q rho visit hactive pair hG hA hr f hw caller hd
  have he := CompactSpectatorLeafSemantics.roundtrip_whole s rows ell q rho visit f hw hu
  exact hh.consequence (fun _ h => h) (fun _ h => ⟨h,he⟩) le_rfl

theorem positive_cost_le (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (hpayload : s.payload=3*(2^ell*ButterflyAxisHeadersData.recordLength s.bits
      (ButterflyIndependentGuardHeaders.reservation s.bits q))) :
    positiveCost s rows ell q rho visit hactive pair≤
      CompactSpectatorLeafGuardBudget.constant*CompactSpectatorLeafGuardBudget.volume s rows ell q*(arity^(k+1))+
      10400*(arity^(k+1)+arity+arity^k+1)^2+2 := by
  have hl := CompactSpectatorLeafGuardBudget.cost_linear s rows ell q rho visit arity
    (node rho visit hactive).right pair.source.val pair.target.val hG hA hr le_rfl
    (Nat.sub_le _ _) pair.source.isLt.le pair.target.isLt.le hpayload
  have he := CompactSpectatorLeafCountBudget.expand_cost (raw (trim (nodeValues s rows ell q rho visit hactive pair)))
    arity (arity^k) rfl rfl
  have hre := CompactSpectatorLeafCountBudget.restore_cost (raw (trim (nodeValues s rows ell q rho visit hactive pair)))
    arity (arity^k) rfl (by decide)
  have hb : 1≤arity^(k+1)+arity+arity^k+1 := by omega
  have hlinear : arity^(k+1)+arity^k+1≤arity^(k+1)+arity+arity^k+1 := by omega
  unfold positiveCost
  rw [pow_succ] at *
  nlinarith only [hl,he,hre,hb,hlinear]

private theorem square_le_exp (n : ℕ) : (n+1)^2≤4*2^n := by
  have aux (m : ℕ) : (m+3)^2≤4*2^(m+2) := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      have hg : (m+4)^2≤2*(m+3)^2 := by
        simp only [pow_two]
        nlinarith
      have he : m+1+2=m+2+1 := by omega
      rw [he,pow_succ 2 (m+2)]
      simp only [pow_two] at *
      nlinarith
  cases n with
  | zero => norm_num
  | succ n =>
    cases n with
    | zero => norm_num
    | succ n => simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using aux n

private theorem exp_le_volume (s : Shape) (rows ell q : ℕ) (hr : 0<rows) :
    2^s.bits≤CompactSpectatorLeafGuardBudget.volume s rows ell q := by
  have hp : 0<rows*2^ell*ButterflyAxisHeadersData.recordLength s.bits
      (ButterflyIndependentGuardHeaders.reservation s.bits q) := by
    unfold ButterflyAxisHeadersData.recordLength
    positivity
  have hh := Nat.le_mul_of_pos_right (2^s.bits) hp
  unfold CompactSpectatorLeafGuardBudget.volume CompactSpectatorLeafAxisBudget.volume
    ButterflySpectatorBudget.volume ButterflyAxisHeadersBudget.logicalVolume
  nlinarith only [hh]

def constant := CompactSpectatorLeafGuardBudget.constant+41600*(arity+3)^2+2

theorem positive_cost_linear (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (hpayload : s.payload=3*(2^ell*ButterflyAxisHeadersData.recordLength s.bits
      (ButterflyIndependentGuardHeaders.reservation s.bits q))) :
    positiveCost s rows ell q rho visit hactive pair≤
      constant*CompactSpectatorLeafGuardBudget.volume s rows ell q*(arity^(k+1)) := by
  have hh := positive_cost_le s rows ell q rho visit hactive pair hG hA hr hpayload
  have hn : 0<arity^k := pow_pos (by decide) _
  have hfit := visit.fits
  have hleft : left<s.active := by
    have hnp : 0<arity^(k+1) := pow_pos (by decide) _
    omega
  obtain ⟨_,_,hb,_,_,_,_,_⟩ := CompactSpectatorLeafAxisBudget.descriptors s rho.val left rho.isLt hleft
  have hpow : arity^k≤arity^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hbase : arity^(k+1)+arity+arity^k+1≤(arity+3)*(s.bits+1) := by nlinarith only [hfit,hb,hpow]
  have hsquare := square_le_exp s.bits
  have hv := exp_le_volume s rows ell q hr
  have hs : (arity^(k+1)+arity+arity^k+1)^2≤4*(arity+3)^2*CompactSpectatorLeafGuardBudget.volume s rows ell q := by
    have hmul := Nat.mul_le_mul hbase hbase
    have hmul' := Nat.mul_le_mul_left ((arity+3)^2) hsquare
    nlinarith only [hmul,hmul',hv]
  have hV := ButterflySpectatorBudget.positive rows s.bits (2^ell)
    (ButterflyIndependentGuardHeaders.reservation s.bits q) hr (pow_pos (by decide) _)
  change 0<CompactSpectatorLeafGuardBudget.volume s rows ell q at hV
  have hc : 0<arity^(k+1) := pow_pos (by decide) _
  unfold constant
  nlinarith only [hh,hs,hV,hc]

theorem positive_correct_uniform (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (hpayload : s.payload=3*(2^ell*ButterflyAxisHeadersData.recordLength s.bits
      (ButterflyIndependentGuardHeaders.reservation s.bits q)))
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hf : ∀ i,(f i).1.length=q+4*s.bits+4 ∧ (f i).2.length=q+4*s.bits+4)
    (hu : ∀ i,‖ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q 0 f i‖≤1)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (nodeValues s rows ell q rho visit hactive pair)) :
    HoareTime (positiveProgram (w:=w))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes)
        (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)))) ∧
        ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q (2*arity^(k+1))
          (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho visit f)=
          ButterflySpectatorSemantics.decoded rows s.bits (2^ell) q 0 f)
      (constant*CompactSpectatorLeafGuardBudget.volume s rows ell q*(arity^(k+1))) := by
  have hh := positive_correct s rows ell q rho visit hactive pair hG hA hr f hf hu caller hd
  exact hh.consequence (fun _ h => h) (fun _ h => h)
    (positive_cost_linear s rows ell q rho visit hactive pair hG hA hr hpayload)

theorem stopped_cost (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (hpayload : s.payload=3*(2^ell*ButterflyAxisHeadersData.recordLength s.bits
      (ButterflyIndependentGuardHeaders.reservation s.bits q)))
    (hs : Networks.ComplexRecursiveCallSchema.stopped s.axes (k+1)=true) :
    (positiveCost s rows ell q rho visit hactive pair : ℝ)≤
      (constant : ℝ)*(CompactSpectatorLeafGuardBudget.volume s rows ell q : ℝ)*(s.axes : ℝ)^Parameters.beta := by
  have hh := (Nat.cast_le (α:=ℝ)).mpr
    (positive_cost_linear s rows ell q rho visit hactive pair hG hA hr hpayload)
  simp only [Nat.cast_mul,Nat.cast_pow] at hh
  have hc := CompactSpectatorLeafCutoffBudget.stopped_count s.axes (k+1) hA hs
  exact hh.trans (mul_le_mul_of_nonneg_left hc (by positivity))

def scalarValues (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) (slot : Fin arity)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (left : ℕ) : Fin 15 → ℕ :=
  values s rows ell q rho.val (left+slot.val) 1 arity
    (s.active-(left+slot.val+1)) pair.source.val pair.target.val

theorem scalar_originals (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) (slot : Fin arity)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (left : ℕ) :
    trim (scalarValues s rows ell q rho slot pair left)=
      CompactComplexLeafHeadersData.values rho slot rows pair left := by
  funext i
  fin_cases i <;> rfl

theorem scalar_actual_runs (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left : ℕ}
    (visit : Visit s.active left 1) (slot : Fin arity)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (scalarValues s rows ell q rho slot pair left)) :
    HoareTime (scalarProgram (w:=w))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes)
        (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.roundtrip s rows ell q rho (Visit.child visit slot) f)))))
      (CompactSpectatorLeafGuardOriginal.cost s rows ell q rho (Visit.child visit slot) arity
        (s.active-(left+slot.val+1)) pair.source.val pair.target.val) := by
  have hh := scalar_runs s rows ell q rho (Visit.child visit slot)
    (s.active-(left+slot.val+1)) pair.source.val pair.target.val hG hA hr f hw caller
  apply hh
  simpa only [scalarValues,pow_zero,Nat.mul_one] using hd

theorem stopped_cost_global (s : Shape) (rows ell q D : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (hpayload : s.payload=3*(2^ell*ButterflyAxisHeadersData.recordLength s.bits
      (ButterflyIndependentGuardHeaders.reservation s.bits q)))
    (hD : 0<D)
    (hs : Networks.ComplexRecursiveCallSchema.stopped D (k+1)=true) :
    (positiveCost s rows ell q rho visit hactive pair : ℝ)≤
      (constant : ℝ)*(CompactSpectatorLeafGuardBudget.volume s rows ell q : ℝ)*(D : ℝ)^Parameters.beta := by
  have hh := (Nat.cast_le (α:=ℝ)).mpr
    (positive_cost_linear s rows ell q rho visit hactive pair hG hA hr hpayload)
  simp only [Nat.cast_mul,Nat.cast_pow] at hh
  have hc := CompactSpectatorLeafCutoffBudget.stopped_count D (k+1) hD hs
  exact hh.trans (mul_le_mul_of_nonneg_left hc (by positivity))

def positivePhaseProgram (dir : CompactSpectatorLeafGuardOriginal.Direction) := seq (seq (countProgram (w:=w) CompactSpectatorLeafCountBudget.expand)
  (extend (CompactSpectatorLeafGuardPlacement.phaseProgram (w:=w) dir) 43))
  (countProgram (w:=w) CompactSpectatorLeafCountBudget.restore)

def positivePhaseCost (dir : CompactSpectatorLeafGuardOriginal.Direction) (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) :=
  let vs := trim (nodeValues s rows ell q rho visit hactive pair)
  CompactChildHeadersArithmetic.scheduleCost CompactSpectatorLeafCountBudget.expand (raw vs)+
  CompactSpectatorLeafGuardOriginal.phaseCost dir s rows ell q rho visit arity
    (node rho visit hactive).right pair.source.val pair.target.val+
  CompactChildHeadersArithmetic.scheduleCost CompactSpectatorLeafCountBudget.restore
    (CompactSpectatorLeafCountBudget.expanded (raw vs) arity (arity^k))+2

theorem positive_phase_runs (dir : CompactSpectatorLeafGuardOriginal.Direction) (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (nodeValues s rows ell q rho visit hactive pair)) :
    HoareTime (positivePhaseProgram (w:=w) dir)
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes)
        (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho visit f)))))
      (positivePhaseCost dir s rows ell q rho visit hactive pair) := by
  let vs := nodeValues s rows ell q rho visit hactive pair
  let g := CompactSpectatorLeafAxis.word (CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho visit f)
  have hin := count_payload caller (CompactSpectatorLeafAxis.word f) vs hd
  have hc : 0<trim vs 7 := pow_pos (by decide) _
  have he := count_expand (w:=w) (trim vs) (CleanSubbank.bank (s:=tapes) caller) hin hc
  rw [count_bank_update] at he
  have hdata := expanded_data caller (CompactSpectatorLeafAxis.word f) vs (arity^k*arity) hd
  rw [node_expanded_values] at hdata
  have hl := CompactSpectatorLeafGuardPlacement.phase_runs (w:=w) dir s rows ell q rho visit arity
    (node rho visit hactive).right pair.source.val pair.target.val hG hA hr f hw
    (setCount caller (arity^k*arity)) hdata
  have hl' := hoare_extend_eq hl (SharedBank.empty 43 2)
  change HoareTime (extend (CompactSpectatorLeafGuardPlacement.phaseProgram (w:=w) dir) 43)
    (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) (setCount caller (arity^k*arity))))
    (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) (updateSource (setCount caller (arity^k*arity)) g))) _ at hl'
  rw [updates_commute] at hl'
  have hout := count_payload (updateSource caller g) g vs (source_data caller _ g vs hd)
  have hs : 0<trim vs 6 := by change 0<arity; decide
  have hre := count_restore (w:=w) (trim vs) (CleanSubbank.bank (s:=tapes) (updateSource caller g)) hout hs
  rw [count_bank_update] at hre
  have h := (he.seq hl').seq hre
  exact h.consequence (fun _ h => h) (fun _ h => h) (by dsimp [positivePhaseCost,vs,trim,nodeValues,values]; omega)

theorem positive_phase_cost_linear (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left k : ℕ}
    (visit : Visit s.active left (k+1)) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (hpayload : s.payload=3*(2^ell*ButterflyAxisHeadersData.recordLength s.bits
      (ButterflyIndependentGuardHeaders.reservation s.bits q))) :
    positivePhaseCost dir s rows ell q rho visit hactive pair≤
      constant*CompactSpectatorLeafGuardBudget.volume s rows ell q*(arity^(k+1)) := by
  apply le_trans _ (positive_cost_linear s rows ell q rho visit hactive pair hG hA hr hpayload)
  dsimp only [positivePhaseCost,positiveCost,CompactSpectatorLeafGuardOriginal.cost]
  cases dir <;> omega

def scalarPhaseProgram (dir : CompactSpectatorLeafGuardOriginal.Direction) := extend (CompactSpectatorLeafGuardPlacement.phaseProgram (w:=w) dir) 43

theorem scalar_phase_runs (dir : CompactSpectatorLeafGuardOriginal.Direction) (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left : ℕ}
    (visit : Visit s.active left 0) (right source target : ℕ)
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (values s rows ell q rho.val left 1 arity right source target)) :
    HoareTime (scalarPhaseProgram (w:=w) dir)
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes)
        (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho visit f)))))
      (CompactSpectatorLeafGuardOriginal.phaseCost dir s rows ell q rho visit arity right source target) :=
  hoare_extend_eq (CompactSpectatorLeafGuardPlacement.phase_runs (w:=w) dir s rows ell q rho visit arity
    right source target hG hA hr f hw caller hd) (SharedBank.empty 43 2)

theorem scalar_actual_phase_runs (dir : CompactSpectatorLeafGuardOriginal.Direction) (s : Shape) (rows ell q : ℕ) (rho : Fin s.chunk) {left : ℕ}
    (visit : Visit s.active left 1) (slot : Fin arity)
    (pair : Networks.BinaryRowProgram.Op (Fin arity))
    (hG : 0<s.guard) (hA : 0<s.axes) (hr : 0<rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ButterflySpectatorSemantics.Width rows s.bits (2^ell) q f)
    (caller : Tapes (callerCount w) 2)
    (hd : SharedBank.payload caller common=payload (CompactSpectatorLeafAxis.word f)
      (scalarValues s rows ell q rho slot pair left)) :
    HoareTime (scalarPhaseProgram (w:=w) dir)
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes) caller))
      (fun v => v=CleanSubbank.bank (s:=43) (CleanSubbank.bank (s:=tapes)
        (updateSource caller (CompactSpectatorLeafAxis.word
          (CompactSpectatorLeafGuardOriginal.result dir s rows ell q rho (Visit.child visit slot) f)))))
      (CompactSpectatorLeafGuardOriginal.phaseCost dir s rows ell q rho (Visit.child visit slot) arity
        (s.active-(left+slot.val+1)) pair.source.val pair.target.val) := by
  have hh := scalar_phase_runs dir s rows ell q rho (Visit.child visit slot)
    (s.active-(left+slot.val+1)) pair.source.val pair.target.val hG hA hr f hw caller
  apply hh
  simpa only [scalarValues,pow_zero,Nat.mul_one] using hd

end
end IntegerMultBounds.Machine.CompactSpectatorStoppedLeafCaller
