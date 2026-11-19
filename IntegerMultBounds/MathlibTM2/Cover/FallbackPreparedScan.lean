module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanPadding
public import IntegerMultBounds.MathlibTM2.Cover.FallbackArchivedResidual

/-! Scan physical records with the prepared residual machine, reusing its exchange and parent tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Mult.PhaseCellToeplitz
open M8 ActualAffineScaling FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem preparedScan_exec {Q T r : ℕ} (a : ScanData r d w W) (parent : Fin d → (ZMod M)ˣ)
    (capacity : columnCapacity ≤ Q) (signCapacity : (fieldSignProgram (0 : Fin (d+1)) true).1 ≤ Q)
    (inputs : ℕ → Array d 1 (w+1) W)
    (encoded : ∀ j < a.records, scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j)
    (signed : (signedInputs a.table (w+1) a.records inputs).Forall₂ Correct a.signed)
    (liveSpec : ∀ j < a.records, LabelStock.live r (w+1) 1 j = true →
      ((a.matrix j).det = 1 ∨ (a.matrix j).det = -1) ∧
      (LabelRing.res prime (w+1) (by omega)).mapMatrix (a.matrix j) = a.table (LabelStock.residue r (w+1) 1 j))
    (padding : ∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
      ∃ symbol, scalarArray (inputs j) = fun _ => symbol)
    (hm : M < 2^a.H) (hw : W < 2^a.J) (hW : 0 < W) :
    let H := a.H
    let J := a.J
    let rows := List.finRange d
    let reads := pivotReads rows
    let n := reads.length
    let k := fun _ : Fin n => (0 : Fin (d+1))
    let j := fun a => (reads.get a).1
    let t := fun a => (j a).succ
    let i := fun a => (reads.get a).2
    let width := fun a => 22+fieldSignSlots (k a)
    let total := Fintype.card (Σ a, Fin (width a))
    let ports := Fin.castAddEmb (n := (N+1)+total) 1
    let shared := (Fin.castAddEmb (n := N+1) total).trans ports
    let bank := fun a => (exchangeBank (N+1) width a).trans ports
    let program : Fin n → Pr Empty (((N+1)+total)+1) Q prime U := fun a =>
      let host := Fin.castAddEmb (n := N+1) (width a)
      let sign := extendSignBank columnBank (fieldSignSlots (k a))
      statePlacedNormalized (bank a) (le_refl Q) (lt_of_lt_of_le columnCapacity_pos capacity) Empty.elim
        (.seq (statePlacedNormalized host capacity columnCapacity_pos Empty.elim (childExchange (j a).val (i a).val (k a) (t a)))
          (.seq (installFieldHeaders ((installerPorts _).trans sign))
            (placedFieldNeg (k a) ((signPorts _).trans sign) signCapacity)))
    let cost := fun a =>
      let shear := fun neg => 1+cleanChildShearTime (P := Empty) (U := U) (A := prime) Empty.elim
        (Function.Embedding.refl _) prime (j a).val (i a).val (k a) (t a) neg w W H J
      let swap := 1+completeSwapTime (P := Empty) (U := U) Empty.elim (d+1) (k a) (t a) w W H J
      1+(1+(2*shear false+shear true+2*swap)+((10*J+12)+(21*(w+1)+12)+1+
        (1+(AtomSegment.chainConst (fieldSignOps (k a) true)*(M^(d+1)*W)*(width a+5)+6))))
    let spare := Fin.last ((N+1)+total)
    let off : ∀ h, shared h ≠ spare := shared_ne_last (t := total)
    let reverseHost := rewindPorts (d+1) shared spare off
    let reverseBank := fun n => columnBank.trans (archivePorts n)
    let active := reverseBank (d+1)
    let pop : Pr Empty (N+2) columnCapacity prime U := .seq (dropWords (active 2) (active 34) (active 0) (d+1))
      (dropWords (active 2) (Fin.last N).castSucc (active 0) d)
    let rewind : Pr Empty (((N+1)+total)+1) Q prime U := statePlacedNormalized reverseHost capacity columnCapacity_pos Empty.elim
      (.seq pop (reverseStages (d+1) (d+1)))
    let stageCost := fun idx => 1+Finset.univ.sup (fun k => columnProgramTime U k (a.pivots idx k) w W H J)+((d+1)*(d+1)*(4*H+4)+1)
    let rewindCost := fun idx => 1+(((d+1)*(4*H+4)+1+(d*(4*H+4)+1))+((d+1)*stageCost idx+1))
    let residual := .seq ((List.finRange n).foldr (fun a rest => .seq (program a) rest) (.act .done)) rewind
    let privateBank := (Fin.natAddEmb (m := total) (N+1)).trans ports
    let bound := fun idx => ((List.finRange n).map cost).sum+1+rewindCost idx
    let cleanBound := fun idx => bound idx+(total*4+1+total*(6*(Fast.Main.mnProgPush residual*bound idx)))
    let positive := lt_of_lt_of_le columnCapacity_pos capacity
    ∀ (host : Fin (((N+1)+total)+1) ↪ Fin T) (ext : Fin 6 ↪ Fin T) (outside : ∀ i k, host i ≠ ext k)
      (parentTape : Fin T) (parentOff : ∀ i, host i ≠ parentTape) (parentExt : ∀ i, ext i ≠ parentTape)
      (body : P → Pr P T Q prime U) v S,
      let scanPorts := reverseHost.trans host
      let cols := shared.trans host
      let prep := forwardBank.trans (rewindPorts (d+1) cols (host spare) (fun i => host.injective.ne (off i)))
      let stream := cols (Fin.last N)
      let tapes := (reverseBank 0).trans scanPorts
      let count := ext 1
      let src := ext 2
      let saved := ext 3
      let tmp := ext 4
      let acc := ext 5
      let dst := cols (columnBank 24)
      let prepare := Prog.seq (.seq (.seq (recordWeights d prep stream) (copyWordHeader (prep 20) (prep 14) (prep 3) (prep 4)))
          (moveRightOrdered (prep 14) (prep 3) (stageBank prep (d+1) 15))) (copyWordHeader parentTape stream (prep 3) (prep 4))
      let compute := Prog.seq (movePrefix count src dst saved tmp) (statePlacedNormalized host le_rfl positive Empty.elim
        (.seq residual (clearWorkTapes ((List.finRange total).map privateBank))))
      let advance := dropWords (tapes 2) (tapes 34) (tapes 0) ((d+1)*(d+1))
      let live := Prog.seq (.seq (.seq prepare compute) (Mult.ShortConv.transfer count (tapes 24) acc tmp)) advance
      let pad := Prog.seq (paddingRecord (d+1) (scanPorts (Fin.last N).castSucc) count src acc tmp) advance
      let volume := M^(d+1)*W
      let prepTime := (d+1)*(2*(d+1)+(4*w+4+columnTime (d+1) prime w H))+1 +
        (d*(8*((d+1)*(d+1)*H)+14*H+22)+1)+(6*H+6)+(4*((d+1)*H)+4)+(6*(d*H)+6)
      let stepTime := fun idx => (if LabelStock.live r (w+1) 1 idx then prepTime+((6*volume+6)+(1+cleanBound idx))
        else 4*(d+1)*(d+1)+1)+(4*volume+4)+((d+1)*(d+1)*(4*H+4)+1)
      let ready := fun idx (D : Stacks T prime) => ScanReady a scanPorts ext idx D ∧
        D.R parentTape = (List.ofFn fun j => binSyms H (parent j : ZMod M).val).flatten ∧
        ∀ h, D.L (host (privateBank h)) = [] ∧ D.R (host (privateBank h)) = []
      ready 0 S → S.R (ext 0) = (LabelMask.selectors r (w+1) a.records).map bitSymbol →
      ∃ z F l, z.user = v.user ∧ ready a.records F ∧ F.R (ext 0) = [] ∧
        l ≤ ((List.range a.records).map fun idx => stepTime idx+4).sum+2 ∧
        Exec body (maskedScan (ext 0) live pad) (mk v S) l (mk z F) := by
  intro H J rows reads n k j t i width total ports shared bank program cost spare off reverseHost reverseBank active pop rewind stageCost rewindCost residual privateBank bound cleanBound positive host ext outside parentTape parentOff parentExt body v S scanPorts cols prep stream tapes count src saved tmp acc dst prepare compute advance live pad volume prepTime stepTime ready start mask
  have offExt (i : Fin (N+2)) (k : Fin 6) : scanPorts i ≠ ext k := outside _ _
  have streamEq : scanPorts (Fin.last N).castSucc = stream := by
    have eq := DFunLike.congr_fun (rewindPorts_active (d+1) shared spare off) (Fin.last N)
    exact congrArg host (by simpa only [Function.Embedding.trans_apply,archivePorts_stream] using eq)
  have prepOff (i : Fin 23) : prep i ≠ parentTape := by
    have eq := DFunLike.congr_fun (rewindPorts_trans (d+1) shared spare off host) (forwardBank i)
    exact eq ▸ parentOff _
  apply maskedRange_exec body (ext 0) live pad a.records (LabelStock.live r (w+1) 1) stepTime ready ?_ ?_ v S start
    (by simpa [LabelMask.selectors,List.map_map,Function.comp_def] using mask)
  · intro idx D bits h
    exact ⟨h.1.mask (fun i => offExt i 0) bits,(Function.update_of_ne (parentExt 0).symm _ _).trans h.2.1,
      fun i => ⟨(h.2.2 i).1,(Function.update_of_ne (outside _ 0) _ _).trans (h.2.2 i).2⟩⟩
  intro idx inside u D current
  obtain ⟨before,parents,free⟩ := current
  cases bit : LabelStock.live r (w+1) 1 idx with
  | false =>
    obtain ⟨symbol,constant⟩ := padding idx inside bit
    obtain ⟨z,F,l,hz,next,left,frame,hn,run⟩ := before.padding a scanPorts ext offExt idx inside bit inputs
      (encoded idx inside) symbol constant signed body u D
    refine ⟨z,F,l,hz,⟨next,(frame _ (parentExt 2).symm (parentExt 5).symm (fun i => parentOff _)).trans parents,?_⟩,
      frame _ (ext.injective.ne (by decide)) (ext.injective.ne (by decide)) (fun i => offExt i 0),
      by simpa only [stepTime,bit,Bool.false_eq_true,ite_false] using hn,by simpa only [bit,Bool.false_eq_true,ite_false] using run⟩
    intro h
    exact ⟨(congrFun left _).trans (free h).1,(frame _ (outside _ 2) (outside _ 5)
      (fun i => host.injective.ne (private_ne_rewind (d+1) h i).symm)).trans (free h).2⟩
  | true =>
    obtain ⟨det,lift⟩ := liveSpec idx inside bit
    have addr := physicalLabel_index (m := r) (w := w+1) idx
    have res := physicalLabel_residue (m := r) (w := w+1) (by omega) idx
    have step := preparedResidual_exec parent capacity signCapacity H J hm hw hW a.table (physicalLabel r (w+1) idx)
      (a.matrix idx) det (lift.trans (congrArg a.table res)) _ (addr.symm ▸ inside) inputs a.signed signed
      (a.matrices (idx+1)) a.pivotTail (fun _ => blank) 0 (by simp) (a.input idx) host body u D
      count src saved tmp (fun i => outside i 2) a.inputTail parentTape prepOff (parentOff _).symm parents
      (by obtain h := before.bank inside; exact ⟨h.modulus,h.width,h.one,h.padded,h.clock,h.archive,h.scratch,h.src,h.dst⟩)
      (by rw [addr]; exact (congrArg D.R streamEq.symm).trans before.pivots)
    simp only [addr,← res] at step
    have sep (i k : Fin 6) (h : i ≠ k) := ext.injective.ne h
    obtain ⟨z,F,l,word,hz,hn,run,effect,out,blanked,archive,next,reset,clean,pivots,_,queue,frame⟩ :=
      step acc (fun i => outside i 1) (fun i => outside i 4) (fun i => outside i 5) (sep 5 2 (by decide))
        (by simp [count,acc,tmp,ext.injective.eq_iff,outside,Ne.symm (outside _ _)])
        ⟨(outside _ 3).symm,(outside _ 3).symm,(outside _ 3).symm⟩
        (by simp [count,src,saved,tmp,ext.injective.eq_iff,outside,Ne.symm (outside _ _)])
        before.count before.saved before.tmp (encoded idx inside) before.queue before.free free
    have same (h : Fin 6) (hs : h ≠ 2) (ha : h ≠ 5) := (frame (ext h) (sep _ _ hs) (sep _ _ ha) (fun i => outside i h)).2
    have unit : IsUnit (a.matrix idx).det := by rcases det with h | h <;> simp [h]
    refine ⟨z,F,l,hz,⟨⟨queue,(congrArg List.length (same 1 (by decide) (by decide))).trans before.count,
      (same 3 (by decide) (by decide)).trans before.saved,(same 4 (by decide) (by decide)).trans before.tmp,
      ?_,pivots,archive,clean,blanked,fun hj => by
        obtain h := next _ _ (a.input (idx+1)) (a.matrices_succ hj)
        exact ⟨h.modulus,h.width,h.one,h.padded,h.clock,h.archive,h.scratch,h.src,h.dst⟩⟩,
      (frame parentTape (parentExt 2).symm (parentExt 5).symm parentOff).2.trans parents,reset⟩,
      same 0 (by decide) (by decide),by simp only [stepTime,bit,ite_true]; exact hn,
      by simp only [ite_true]; exact run⟩
    rw [outputPrefix_succ,outputRecord_live _ _ _ bit unit word effect,← before.acc]
    exact out

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
