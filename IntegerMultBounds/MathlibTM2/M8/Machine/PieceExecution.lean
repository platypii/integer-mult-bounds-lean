module

public import IntegerMultBounds.MathlibTM2.M8.Machine.BaseExecution
public import IntegerMultBounds.MathlibTM2.M8.Machine.NodeTransport
public import IntegerMultBounds.MathlibTM2.M8.Machine.CallRecovery
public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryInvariant

/-! Exact physical traces through suffixes of the literal recursive schedule.
Segment and gate traces use their concrete global-bank contracts. Recursive
calls retain an explicit actual child trace, between charged physical setup and
recovery blocks, so this does not assert recursive termination for free. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.PieceExecution
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Implementation (commonCount implementation widthSlot pcStack)
open Control
open BaseExecution (entryConfig)
open SharedBankStageInput (raw)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewedAction (Data)
open Transport (Child)
variable {k b : ℕ} {v : Descriptor}

/-- Physical call composition, with an actual graph child run starting after
setup and ending at this call's decoded recovery address. Both physical blocks
and their controller edges are charged; every endpoint bank is exact. -/
theorem call_jump (capacity : Fintype.card PC ≤ 2^k) (site : Site)
    (w : Wire) (i j : Fin Machine.width) (hi : pieces[site] = .call w i j)
    (before entered returned after : Tapes commonCount prime) (E C R : ℕ)
    (he : HoareTime (block capacity widthSlot pcStack (implementation k) (.piece site)).program
      (fun ww => ww = raw before (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes)
      (fun ww => ww = raw entered (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes) E)
    (hc : ∃ n ≤ C, Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
      (entryConfig capacity .guard entered) = some (entryConfig capacity (.recover site) returned))
    (hr : HoareTime (block capacity widthSlot pcStack (implementation k) (.recover site)).program
      (fun ww => ww = raw returned (block capacity widthSlot pcStack (implementation k) (.recover site)).tapes)
      (fun ww => ww = raw after (block capacity widthSlot pcStack (implementation k) (.recover site)).tapes) R) :
    ∃ n ≤ E+C+R+2, Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
      (entryConfig capacity (.piece site) before) = some (entryConfig capacity (successor site) after) := by
  obtain ⟨ne,hne,hte⟩ := BlockExecution.block_jump capacity widthSlot pcStack
    (implementation k) (.piece site) .guard before entered E he (call_edge capacity widthSlot pcStack _ site w i j hi)
  obtain ⟨nc,hnc,htc⟩ := hc
  obtain ⟨nr,hnr,htr⟩ := BlockExecution.block_jump capacity widthSlot pcStack
    (implementation k) (.recover site) (successor site) returned after R hr (recover_edge capacity widthSlot pcStack _ site)
  change Machine.run _ ne (entryConfig capacity (.piece site) before) = some (entryConfig capacity .guard entered) at hte
  change Machine.run _ nr (entryConfig capacity (.recover site) returned) = some (entryConfig capacity (successor site) after) at htr
  refine ⟨ne+nc+nr,by omega,?_⟩
  rw [run_add,run_add,hte,Option.bind_some,htc,Option.bind_some]
  exact htr

/-- The finite suffix controller uses the literal index until the final merge. -/
def position (n : ℕ) : PC := if h : n < pieces.length then .piece ⟨n,h⟩ else .tempClear

/-- Complete per-piece bound includes the actual controller edge. A call bound
includes its physical setup, child graph trace, restoration and recovery. -/
def pieceBound (callBound : Wire → Fin Machine.width → Fin Machine.width → ℕ)
    (p : Piece) : ℕ := match p with
  | .segment seg => seg.coefficient*volume prime v+1
  | .gate g => RoleOpsClean.coefficient (Gate.ops g)*volume prime v+1
  | .reset r => RoleOpsClean.coefficient (Reset.ops r)*volume prime v+1
  | .call w i j => callBound w i j

/-- Explicit charged call-site budget, including physical setup, the child
trace, recovery and the two finite controller edges. -/
def actualCallBound (k C : ℕ) (w : Wire) (_i _j : Fin Machine.width) : ℕ :=
  (88*(CallLayout.parked w).length+51884+
    RecursiveRoleChildCallSetup.constant Machine.width k)*volume prime v+C+
    (92*(CallLayout.parked w).length+51883)*volume prime v+2

/-- A compile-time coefficient for the physical work of one literal piece. -/
def overhead (k : ℕ) : Piece → ℕ
  | .segment seg => seg.coefficient+1
  | .gate g => RoleOpsClean.coefficient (Gate.ops g)+1
  | .reset r => RoleOpsClean.coefficient (Reset.ops r)+1
  | .call w _ _ => 88*(CallLayout.parked w).length+51884+
      RecursiveRoleChildCallSetup.constant Machine.width k+
      (92*(CallLayout.parked w).length+51883)+2

/-- Summed physical traces have one child budget per literal call and fixed
linear overhead in the logical parent volume. Parked ancestors are not counted
in that volume. -/
theorem bound_sum (k C : ℕ) (ps : List Piece) (hV : 0 < volume prime v) :
    (ps.map (pieceBound (v := v) (actualCallBound (v := v) k C))).sum ≤
      (ps.map (overhead k)).sum*volume prime v+(ps.map Piece.calls).sum*C := by
  induction ps with
  | nil => simp only [List.map_nil,List.sum_nil,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | cons piece ps ih =>
    cases piece <;>
      simp only [List.map_cons,List.sum_cons,pieceBound,actualCallBound,overhead,Piece.calls] at * <;>
      nlinarith

/-- The original exact call-count theorem now controls actual graph-trace
costs, with every physical nonrecursive operation and edge accounted for. -/
theorem bound_fixed (k C : ℕ) (hV : 0 < volume prime v) :
    (pieces.map (pieceBound (v := v) (actualCallBound (v := v) k C))).sum ≤
      (pieces.map (overhead k)).sum*volume prime v+(Net.net).rankSum*C := by
  simpa only [calls_exact] using bound_sum (v := v) k C pieces hV

variable (capacity : Fintype.card PC ≤ 2^k) (hw : v.width=Machine.width*b)
  (child : Child v) (hp : v.Positive) (hs : Fin 6 → List Bool)
  (hv : RecursiveDimensionBank.Headers v hs) (f : ℤ → Fin (prime+4)) (p : ℤ)
  (node : Tapes 1 prime) (st : Tapes 2 prime)

/-- The permanent bank at each literal piece boundary has clean scalar-view
workspace and retains all parked ancestor data and descriptor/PC stacks. -/
def dataBank (data : Data payloadCount v) : Tapes commonCount prime :=
  Shared50RecursiveBank.bank (RecursiveRoleSerialization.roles data) hs f p node
    (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st

include hp hv hw in
/-- The chosen child headers and both physical boundary contracts are shared by
endpoint/time and prefix-space proofs. -/
theorem call_contracts (site : Site) (w : Wire) (i j : Fin Machine.width)
    (hi : pieces[site] = .call w i j) (data : Data payloadCount v)
    (out : Fin (volume prime v) → Fin 4) (hio : data io = fun _ => blank)
    (hf : ∀ z, p ≤ z → f z = blank) :
    ∃ ch, RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.child prime 1 b v i j) ch ∧
      HoareTime (block capacity widthSlot pcStack (implementation k) (.piece site)).program
        (· = raw (dataBank hs f p node st data)
          (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes)
        (· = raw (RecursiveCallProtocol.childBank
          (RecursiveCallProtocol.entered (CallLayout.parked w) (wireSlot w) io (volume prime v)
            (dataBank hs f p node st data)) ch
          (node.append ((SharedBank.empty 1 prime).append (SharedBank.empty 0 prime)))
          (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site)))
          (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes)
        ((88*(CallLayout.parked w).length+51884+RecursiveRoleChildCallSetup.constant Machine.width k)*volume prime v) ∧
      HoareTime (block capacity widthSlot pcStack (implementation k) (.recover site)).program
        (· = raw (SharedPlacementAlphabet.setTape
          (RecursiveCallProtocol.entered (CallLayout.parked w) (wireSlot w) io (volume prime v)
            (dataBank hs f p node st data))
          (RecursiveCallBank.role (u := 1+(1+0)) io).val (RecursiveShiftRoleBank.source out) 0)
          (block capacity widthSlot pcStack (implementation k) (.recover site)).tapes)
        (· = raw (dataBank hs f p node st (Function.update data (wireSlot w) out))
          (block capacity widthSlot pcStack (implementation k) (.recover site)).tapes)
        ((92*(CallLayout.parked w).length+51883)*volume prime v) := by
  let aux := node.append ((SharedBank.empty 1 prime).append (SharedBank.empty 0 prime))
  let entryBlock := RecursiveCallProtocol.enter (u := 1+(1+0))
    (CallLayout.parked w) (wireSlot w) io
    (CallLayout.active_ne_io w) i j (returnCode capacity site)
  let returnBlock := RecursiveCallProtocol.recover (u := 1+(1+0))
    (CallLayout.parked w) (wireSlot w) io
    (CallLayout.active_ne_io w)
  have hentryEq : block capacity widthSlot pcStack (implementation k) (.piece site) = entryBlock := by
    simp only [block,hi,implementation,entryBlock]
  have hreturnEq : block capacity widthSlot pcStack (implementation k) (.recover site) = returnBlock := by
    simp only [block,hi,implementation,returnBlock]
  obtain ⟨ch,hch,he⟩ := RecursiveCallProtocol.enters
    (CallLayout.parked w) (CallLayout.parked_nodup w)
    (wireSlot w) io
    (CallLayout.active_ne_io w) (CallLayout.active_not_parked w)
    (CallLayout.io_not_parked w) b v i j hw
    (RecursiveRoleSerialization.roles data) hs f p aux st (returnCode capacity site) hv hp
    (fun z _ => CallSemantics.roles_supported data z)
    (CallSemantics.roles_supported data _)
    (by
      constructor
      · rfl
      · change RecursiveShiftRoleBank.source (data io) = _
        rw [hio]
        exact RecursiveRowsSerialization.source_blank v)
  have hr := CallRecovery.recovers w data out hs f p aux st hv hp hf hio
  exact ⟨ch,hch,by rw [hentryEq]; exact he,by rw [hreturnEq]; exact hr⟩

include hp hv hw in
/-- Concrete call entry and recovery require only an actual child graph trace.
The generated child headers and saved return code are fed literally to that
trace; its return endpoint is the entered parent bank with the I/O word changed.
All count generation, parking, descriptor setup and controller edges are paid. -/
theorem call_actual (site : Site) (w : Wire) (i j : Fin Machine.width)
    (hi : pieces[site] = .call w i j) (data : Data payloadCount v)
    (out : Fin (volume prime v) → Fin 4)
    (hio : data io = fun _ => blank)
    (hf : ∀ z, p ≤ z → f z = blank) (C : ℕ)
    (childTrace : ∀ ch : Fin 6 → List Bool,
      RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.child prime 1 b v i j) ch →
      ∃ steps ≤ C, Machine.run (Control.program capacity widthSlot pcStack (implementation k)) steps
        (entryConfig capacity .guard (RecursiveCallProtocol.childBank
          (RecursiveCallProtocol.entered (CallLayout.parked w)
            (wireSlot w) io (volume prime v)
            (dataBank hs f p node st data)) ch
          (node.append ((SharedBank.empty 1 prime).append (SharedBank.empty 0 prime)))
          (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site)))) =
        some (entryConfig capacity (.recover site) (SharedPlacementAlphabet.setTape
          (RecursiveCallProtocol.entered (CallLayout.parked w)
            (wireSlot w) io (volume prime v)
            (dataBank hs f p node st data))
          (RecursiveCallBank.role (u := 1+(1+0)) io).val
          (RecursiveShiftRoleBank.source out) 0))) :
    ∃ steps ≤ (88*(CallLayout.parked w).length+51884+
        RecursiveRoleChildCallSetup.constant Machine.width k)*volume prime v+C+
        (92*(CallLayout.parked w).length+51883)*volume prime v+2,
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) steps
        (entryConfig capacity (.piece site) (dataBank hs f p node st data)) =
        some (entryConfig capacity (successor site) (dataBank hs f p node st
          (Function.update data (wireSlot w) out))) := by
  obtain ⟨ch,hch,he,hr⟩ := call_contracts capacity hw hp hs hv f p node st site w i j hi data out hio hf
  exact call_jump capacity site w i j hi _ _ _ _ _ C _ he (childTrace ch hch) hr

include hp hv in
/-- Nonrecursive pieces run through their actual globally placed programs. The
only remaining premise is the actual call-site execution trace. -/
theorem piece_jump
    (Ready : Data payloadCount v → Prop)
    (callBound : Wire → Fin Machine.width → Fin Machine.width → ℕ)
    (calls : ∀ (site : Site) w i j, pieces[site] = .call w i j → ∀ data : Data payloadCount v, Ready data →
      ∃ n ≤ callBound w i j, Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
        (entryConfig capacity (.piece site) (dataBank hs f p node st data)) =
        some (entryConfig capacity (successor site) (dataBank hs f p node st (child w i j data))))
    (site : Site) (data : Data payloadCount v) (hready : Ready data) :
    ∃ n ≤ pieceBound (v := v) callBound pieces[site],
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
        (entryConfig capacity (.piece site) (dataBank hs f p node st data)) =
      some (entryConfig capacity (successor site)
        (dataBank hs f p node st (Transport.step hw child pieces[site] data))) := by
  generalize hpiece : pieces[site] = piece
  cases piece with
  | call w i j => exact calls site w i j hpiece data hready
  | segment seg =>
    have h := BankNodes.segment_hoare seg hw hp hs hv f p node
      (SharedBank.empty 0 prime) st data
    have hblock : block capacity widthSlot pcStack (implementation k) (.piece site) =
        BankNodes.segment (u := 0) seg := by
      simp only [block,hpiece,implementation]
    have hh : HoareTime (block capacity widthSlot pcStack (implementation k) (.piece site)).program
        (fun ww => ww = raw (dataBank hs f p node st data) (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes)
        (fun ww => ww = raw (dataBank hs f p node st (seg.array hw data))
          (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes)
        (seg.coefficient*volume prime v) := by rw [hblock]; exact h
    exact BlockExecution.block_jump capacity widthSlot pcStack (implementation k)
      (.piece site) (successor site) _ _ _ hh (fun _ => by simp only [edge,hpiece])
  | gate g =>
    have h := BankNodes.ops_hoare (Gate.ops g) hp hs hv f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st data
    have hblock : block capacity widthSlot pcStack (implementation k) (.piece site) =
        BankNodes.gate (u := 0) g := by
      simp only [block,hpiece,implementation]
    have hh : HoareTime (block capacity widthSlot pcStack (implementation k) (.piece site)).program
        (fun ww => ww = raw (dataBank hs f p node st data) (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes)
        (fun ww => ww = raw (dataBank hs f p node st (g.array data))
          (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes)
        (RoleOpsClean.coefficient (Gate.ops g)*volume prime v) := by rw [hblock]; exact h
    exact BlockExecution.block_jump capacity widthSlot pcStack (implementation k)
      (.piece site) (successor site) _ _ _ hh (fun _ => by simp only [edge,hpiece])
  | reset r =>
    have h := BankNodes.ops_hoare (Reset.ops r) hp hs hv f p node
      (SharedBank.empty 1 prime) (SharedBank.empty 0 prime) st data
    have hblock : block capacity widthSlot pcStack (implementation k) (.piece site) =
        BankNodes.reset (u := 0) r := by
      simp only [block,hpiece,implementation]
    have hh : HoareTime (block capacity widthSlot pcStack (implementation k) (.piece site)).program
        (fun ww => ww = raw (dataBank hs f p node st data) (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes)
        (fun ww => ww = raw (dataBank hs f p node st (r.array data))
          (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes)
        (RoleOpsClean.coefficient (Reset.ops r)*volume prime v) := by rw [hblock]; exact h
    exact BlockExecution.block_jump capacity widthSlot pcStack (implementation k)
      (.piece site) (successor site) _ _ _ hh (fun _ => by simp only [edge,hpiece])

include hp hv in
/-- Actual execution of every remaining literal piece, without enumerating the
huge fixed schedule. Costs sum the physical traces, including all graph edges. -/
theorem suffix_run
    (Ready : Data payloadCount v → Prop)
    (preserves : ∀ piece data, Ready data → Ready (Transport.step hw child piece data))
    (callBound : Wire → Fin Machine.width → Fin Machine.width → ℕ)
    (calls : ∀ (site : Site) w i j, pieces[site] = .call w i j → ∀ data : Data payloadCount v, Ready data →
      ∃ n ≤ callBound w i j, Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
        (entryConfig capacity (.piece site) (dataBank hs f p node st data)) =
        some (entryConfig capacity (successor site) (dataBank hs f p node st (child w i j data))))
    (n : ℕ) (hn : n ≤ pieces.length) (data : Data payloadCount v) (hready : Ready data) :
    ∃ steps ≤ ((pieces.drop n).map (pieceBound (v := v) callBound)).sum,
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) steps
        (entryConfig capacity (position n) (dataBank hs f p node st data)) =
      some (entryConfig capacity .tempClear (dataBank hs f p node st
        (Transport.run hw child (pieces.drop n) data))) := by
  generalize he : pieces.length-n = remaining
  induction remaining using Nat.strong_induction_on generalizing n data with
  | h remaining ih =>
    by_cases hlt : n < pieces.length
    · let site : Site := ⟨n,hlt⟩
      obtain ⟨ns,hns,hrs⟩ := piece_jump capacity hw child hp hs hv f p node st Ready callBound calls site data hready
      have hless : pieces.length-(n+1) < remaining := by omega
      obtain ⟨nt,hnt,hrt⟩ := ih (pieces.length-(n+1)) hless (n+1) (by omega)
        (Transport.step hw child pieces[site] data) (preserves _ _ hready) rfl
      have hpos : position n = .piece site := by simp only [position,dite_eq_left hlt]; rfl
      have hsucc : successor site = position (n+1) := rfl
      rw [hsucc] at hrs
      refine ⟨ns+nt,?_,?_⟩
      · rw [List.drop_eq_getElem_cons hlt,List.map_cons,List.sum_cons]
        exact Nat.add_le_add hns hnt
      · rw [hpos,run_add,hrs,Option.bind_some]
        simpa only [List.drop_eq_getElem_cons hlt,Transport.run,List.foldl_cons,Fin.getElem_fin,site] using hrt
    · have heq : n = pieces.length := by omega
      subst n
      refine ⟨0,by simp,?_⟩
      simp only [List.drop_length,Transport.run,List.foldl_nil,position,lt_self_iff_false,dite_false,IntegerMultBounds.Machine.run]

include hp hv in
/-- The entire literal schedule executes through the actual fixed graph to
merge, retaining exact array semantics and summed physical costs. -/
theorem schedule_run
    (Ready : Data payloadCount v → Prop)
    (preserves : ∀ piece data, Ready data → Ready (Transport.step hw child piece data))
    (callBound : Wire → Fin Machine.width → Fin Machine.width → ℕ)
    (calls : ∀ (site : Site) w i j, pieces[site] = .call w i j → ∀ data : Data payloadCount v, Ready data →
      ∃ n ≤ callBound w i j, Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
        (entryConfig capacity (.piece site) (dataBank hs f p node st data)) =
        some (entryConfig capacity (successor site) (dataBank hs f p node st (child w i j data))))
    (data : Data payloadCount v) (hready : Ready data) :
    ∃ steps ≤ (pieces.map (pieceBound (v := v) callBound)).sum,
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) steps
        (entryConfig capacity first (dataBank hs f p node st data)) =
      some (entryConfig capacity .tempClear (dataBank hs f p node st
        (Transport.run hw child pieces data))) := by
  have h := suffix_run capacity hw child hp hs hv f p node st Ready preserves callBound calls
    0 (Nat.zero_le _) data hready
  simpa only [List.drop_zero,show position 0 = first from rfl] using h

include hp hv in
/-- Binary Wire streams and blank I/O are preserved automatically throughout
the actual schedule. Recursive trace premises are required only on these
reachable binary inputs; arbitrary nonbinary Wire data is never assumed. -/
theorem binary_schedule_run
    (hc : Transport.ChildSpec hw child)
    (callBound : Wire → Fin Machine.width → Fin Machine.width → ℕ)
    (calls : ∀ (site : Site) w i j, pieces[site] = .call w i j → ∀ data : Data payloadCount v, BinaryInvariant.Ready data →
      ∃ n ≤ callBound w i j, Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
        (entryConfig capacity (.piece site) (dataBank hs f p node st data)) =
        some (entryConfig capacity (successor site) (dataBank hs f p node st (child w i j data))))
    (data : Data payloadCount v) (hready : BinaryInvariant.Ready data) :
    ∃ steps ≤ (pieces.map (pieceBound (v := v) callBound)).sum,
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) steps
        (entryConfig capacity first (dataBank hs f p node st data)) =
      some (entryConfig capacity .tempClear (dataBank hs f p node st
        (Transport.run hw child pieces data))) := by
  exact schedule_run capacity hw child hp hs hv f p node st
    BinaryInvariant.Ready
    (fun piece data hready => BinaryInvariant.step hw child hc piece data hready)
    callBound calls data hready

include hp hv in
/-- Actual binary schedule trace with a single uniform child budget. This is
the physical schedule contribution to the recursive runtime recurrence. -/
theorem binary_schedule_bound
    (hc : Transport.ChildSpec hw child)
    (C : ℕ)
    (calls : ∀ (site : Site) w i j, pieces[site] = .call w i j → ∀ data : Data payloadCount v, BinaryInvariant.Ready data →
      ∃ n ≤ actualCallBound (v := v) k C w i j, Machine.run (Control.program capacity widthSlot pcStack (implementation k)) n
        (entryConfig capacity (.piece site) (dataBank hs f p node st data)) =
        some (entryConfig capacity (successor site) (dataBank hs f p node st (child w i j data))))
    (data : Data payloadCount v) (hready : BinaryInvariant.Ready data) :
    ∃ steps ≤ (pieces.map (overhead k)).sum*volume prime v+(Net.net).rankSum*C,
      Machine.run (Control.program capacity widthSlot pcStack (implementation k)) steps
        (entryConfig capacity first (dataBank hs f p node st data)) =
      some (entryConfig capacity .tempClear (dataBank hs f p node st
        (Transport.run hw child pieces data))) := by
  obtain ⟨n,hn,hr⟩ := binary_schedule_run capacity hw child hp hs hv f p node st hc
    (actualCallBound (v := v) k C) calls data hready
  exact ⟨n,hn.trans (bound_fixed k C
    (RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp)),hr⟩

end
end IntegerMultBounds.MathlibTM2.M8.Machine.PieceExecution
