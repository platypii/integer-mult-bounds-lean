module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanLive
public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanPadding

/-! Execute all live and padded residual records in physical order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {T r d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def ScanData.recordTime (a : ScanData r d w W) (U : Type) (j : ℕ) :=
  let volume := M^(d+1)*W
  let branch := if LabelStock.live r (w+1) 1 j then
    6*volume+6+(1+signedResidualTime U (a.pivots j) w W a.H a.J)
    else 4*(d+1)*(d+1)+1
  branch+(4*volume+4)+((d+1)*(d+1)*(4*a.H+4)+1)

theorem residualScan_exec (a : ScanData r d w W) (ports : Fin (N+2) ↪ Fin T) (ext : Fin 6 ↪ Fin T)
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
    (start : ScanReady a ports ext 0 S)
    (mask : S.R (ext 0) = (LabelMask.selectors r (w+1) a.records).map bitSymbol) :
    ∃ z F n, z.user = v.user ∧ ScanReady a ports ext a.records F ∧ F.R (ext 0) = [] ∧
      n ≤ ((List.range a.records).map fun j => a.recordTime U j + 4).sum + 2 ∧
      Exec body (residualScan ports (ext 0) (ext 1) (ext 2) (ext 3) (ext 4) (ext 5) d) (mk v S) n (mk z F) := by
  unfold residualScan
  apply maskedRange_exec body _ _ _ a.records (LabelStock.live r (w+1) 1) (a.recordTime U) (ScanReady a ports ext)
    (fun _ _ bits h => h.mask (fun i => off i 0) bits) _ v S start
    (by simpa [LabelMask.selectors,List.map_map,Function.comp_def] using mask)
  intro j inside u D ready
  cases h : LabelStock.live r (w+1) 1 j with
  | false =>
    obtain ⟨symbol,constant⟩ := padding j inside h
    obtain ⟨z,F,n,hz,next,frame,hn,run⟩ := ready.padding a ports ext off j inside h inputs (encoded j inside)
      symbol constant signed body u D
    exact ⟨z,F,n,hz,next,frame _ (ext.injective.ne (by decide)) (ext.injective.ne (by decide))
      (fun i => off i 0),by simpa [ScanData.recordTime,h] using hn,run⟩
  | true =>
    obtain ⟨det,lift⟩ := liveSpec j inside h
    obtain ⟨z,F,n,hz,next,frame,hn,run⟩ := ready.live a ports ext off j inside h det lift inputs (encoded j inside)
      signed hm hw hW body u D
    exact ⟨z,F,n,hz,next,frame _ (ext.injective.ne (by decide)) (ext.injective.ne (by decide))
      (fun i => off i 0),by simpa [ScanData.recordTime,h] using hn,run⟩

/-- Dispatch the concrete residual and padding programs around a good-record program
that advances the same input, output, pivot, and matrix streams. -/
theorem classifiedResidualScan_exec (a : ScanData r d w W) (ports : Fin (N+2) ↪ Fin T) (ext : Fin 6 ↪ Fin T)
    (off : ∀ i k, ports i ≠ ext k) (inputs : ℕ → Record.Array d 1 (w+1) W)
    (encoded : ∀ j < a.records, Record.scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j)
    (signed : (Record.signedInputs a.table (w+1) a.records inputs).Forall₂ Record.Correct a.signed)
    (liveSpec : ∀ j < a.records, LabelStock.live r (w+1) 1 j = true →
      ((a.matrix j).det = 1 ∨ (a.matrix j).det = -1) ∧
      (LabelRing.res prime (w+1) (by omega)).mapMatrix (a.matrix j) = a.table (LabelStock.residue r (w+1) 1 j))
    (padding : ∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
      ∃ symbol, Record.scalarArray (inputs j) = fun _ => symbol)
    (hm : M < 2^a.H) (hw : W < 2^a.J) (hW : 0 < W)
    (body : P → Pr P T columnCapacity prime U)
    (mask : Fin T) (outside : ∀ i, ports i ≠ mask) (separate : ∀ i, ext i ≠ mask)
    (proj : LabelPadding.Label r (w+1)) (rank : ℕ) (fits : rank ≤ r)
    (good : Pr P T columnCapacity prime U) (goodTime : ℕ → ℕ)
    (goodStep : ∀ j < a.records, LabelStock.live r (w+1) 1 j = true →
      fallbackBit fits proj (physicalLabel r (w+1) j) = false →
      ∀ (u : HS T columnCapacity prime U) D, ScanReady a ports ext j D → ∃ z F n, z.user = u.user ∧
        ScanReady a ports ext (j+1) F ∧ F.R (ext 0) = D.R (ext 0) ∧ F.R mask = D.R mask ∧
        n ≤ goodTime j ∧ Exec body good (mk u D) n (mk z F))
    (v : HS T columnCapacity prime U) (S : Stacks T prime) (start : ScanReady a ports ext 0 S)
    (liveBits : S.R (ext 0) = (LabelMask.selectors r (w+1) a.records).map bitSymbol) :
    let bad := fun j => fallbackBit fits proj (physicalLabel r (w+1) j)
    let cost := fun j => if LabelStock.live r (w+1) 1 j && !bad j then goodTime j else a.recordTime U j
    let bank := (columnBank.trans (archivePorts 0)).trans ports
    let advance := dropWords (bank 2) (bank 34) (bank 0) ((d+1)*(d+1))
    let fallback := Prog.seq (collectAnchorRecord ports (ext 1) (ext 2) (ext 3) (ext 4) (ext 5) d) advance
    let pad := Prog.seq (paddingRecord (d+1) (ports (Fin.last N).castSucc) (ext 1) (ext 2) (ext 5) (ext 4)) advance
    S.R mask = (List.range a.records).map (fun j => bitSymbol (bad j)) →
    ∃ z F n, z.user = v.user ∧ ScanReady a ports ext a.records F ∧ F.R (ext 0) = [] ∧ F.R mask = [] ∧
      n ≤ ((List.range a.records).map fun j => (cost j+2)+4).sum+2 ∧
      Exec body (classifiedScan (ext 0) mask good fallback pad) (mk v S) n (mk z F) := by
  intro bad cost bank advance fallback pad badBits
  apply classifiedScan_exec body _ _ (separate 0) good fallback pad a.records
    (LabelStock.live r (w+1) 1) bad cost (ScanReady a ports ext) ?_ ?_ v S start
    (by simpa [LabelMask.selectors,List.map_map,Function.comp_def] using liveBits) badBits
  · intro j D slot bits h ready
    rcases h with rfl | rfl
    · exact ready.mask (fun i => off i 0) bits
    · exact ready.selector _ outside (fun i _ => separate i) bits
  intro j inside u D ready
  cases h : LabelStock.live r (w+1) 1 j with
  | false =>
    obtain ⟨symbol,constant⟩ := padding j inside h
    obtain ⟨z,F,n,hz,next,frame,hn,run⟩ := ready.padding a ports ext off j inside h inputs
      (encoded j inside) symbol constant signed body u D
    exact ⟨z,F,n,hz,next,frame _ (ext.injective.ne (by decide)) (ext.injective.ne (by decide))
      (fun i => off i 0),frame _ (separate 2).symm (separate 5).symm outside,
      by simpa [cost,ScanData.recordTime,h] using hn,by simpa [h,pad,advance,bank] using run⟩
  | true =>
    cases b : bad j with
    | false => simpa [h,b,cost] using goodStep j inside h b u D ready
    | true =>
      obtain ⟨det,lift⟩ := liveSpec j inside h
      obtain ⟨z,F,n,hz,next,frame,hn,run⟩ := ready.live a ports ext off j inside h det lift inputs
        (encoded j inside) signed hm hw hW body u D
      exact ⟨z,F,n,hz,next,frame _ (ext.injective.ne (by decide)) (ext.injective.ne (by decide))
        (fun i => off i 0),frame _ (separate 2).symm (separate 5).symm outside,
        by simpa [cost,ScanData.recordTime,h,b] using hn,by simpa [h,b,fallback,advance,bank] using run⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
