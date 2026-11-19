module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPlacedAnchorPass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanState

/-! Transfer the prepared residual bank across the anchor pass on its shared input queue. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable [M8.Machine.Net] {T K Q d r w W : ℕ} {P U : Type}
local notation "N" => rowSwapBlock.tapes+35

noncomputable def preparedPivots (a : ScanData r d w W) (pivot : Fin K) (S : Stacks K prime) :=
  {S with R := Function.update S.R pivot ((List.range a.records).flatMap a.pivotWord ++ S.R pivot)}

theorem ScanReady.signedHandoff (a : ScanData r d w W) (ports : Fin (N+2) ↪ Fin K) (ext : Fin 6 ↪ Fin K)
    (off : ∀ i k, ports i ≠ ext k) (S F : Stacks K prime) (outs : List (Record.Array d 1 (w+1) W))
    (keep : embStk ports F = embStk ports S)
    (external : ∀ i, i ≠ 2 → F.R (ext i) = S.R (ext i))
    (queue : F.R (ext 2) = outs.flatMap payloadWord ++ a.inputTail)
    (start : ScanReady a ports ext 0 (preparedPivots a (ports (Fin.last N).castSucc) S)) :
    ScanReady {a with signed := outs} ports ext 0 (preparedPivots a (ports (Fin.last N).castSucc) F) := by
  let pivot := ports (Fin.last N).castSucc
  let D := preparedPivots a pivot S
  let G := preparedPivots a pivot F
  have sameR (i) : F.R (ports i) = S.R (ports i) := congrArg (fun B : Stacks (N+2) prime => B.R i) keep
  have sameL (i) : F.L (ports i) = S.L (ports i) := congrArg (fun B : Stacks (N+2) prime => B.L i) keep
  have internal (i) : G.R (ports i) = D.R (ports i) := by
    by_cases h : ports i = pivot
    · simp [G,D,preparedPivots,h,show F.R pivot = S.R pivot from sameR (Fin.last N).castSucc]
    · simpa [G,D,preparedPivots,Function.update_of_ne h] using sameR i
  have bank : embStk ports G = embStk ports D := by
    unfold embStk
    congr 1
    · exact congrArg (fun B : Stacks (N+2) prime => B.inp) keep
    · exact congrArg (fun B : Stacks (N+2) prime => B.out) keep
    · exact funext sameL
    · exact funext internal
  have ex (i) : G.R (ext i) = F.R (ext i) := Function.update_of_ne (off _ i).symm _ _
  have exD (i) : D.R (ext i) = S.R (ext i) := Function.update_of_ne (off _ i).symm _ _
  have unchanged (i) (h : i ≠ 2) := (ex i).trans ((external i h).trans (exD i).symm)
  refine ⟨(ex 2).trans (by simpa using queue),(congrArg List.length (unchanged 1 (by decide))).trans start.count,
    (unchanged 3 (by decide)).trans start.saved,(unchanged 4 (by decide)).trans start.tmp,
    (unchanged 5 (by decide)).trans start.acc,(internal _).trans start.pivots,(internal _).trans start.archive,
    fun i hi => ⟨(sameL _).trans (start.free i hi).1,(internal _).trans (start.free i hi).2⟩,?_,?_⟩
  · intro z
    change readAt blank (F.L _) (G.R _) z = _
    rw [internal,show F.L (ports (archivePorts 0 (columnBank 24))) = S.L _ from sameL _]
    exact start.blankSrc z
  · intro h
    exact bank.symm ▸ start.bank h

open Record RecursiveInterchangeLayout

theorem anchorHandoff (regs : Fin 6 ↪ Fin T) (anchor : Fin (size d+T) ↪ Fin K)
    (ports : Fin (N+2) ↪ Fin K) (ext : Fin 6 ↪ Fin K) (off : ∀ i k, ports i ≠ ext k)
    (banks : ∀ i k, anchor i ≠ ports k) (external : ∀ i k, k ≠ 2 → anchor i ≠ ext k)
    (shared : anchor (port d regs 1) = ext 2)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ Q)
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (body : P → Pr P K Q prime U) (rs : List (Pair (size d+T))) (hk : rs.length = r*r)
    (parents saved : Fin (size d+T)) (layout : (parents :: saved :: (slots rs ++ [port d regs 4])).Nodup) :
    ∃ prog, ∀ {w W : ℕ} (v : Descriptor) (B : ℕ) (a : ScanData r d w W) (inputs : ℕ → Record.Array d 1 (w+1) W)
      (u : HS K Q prime U) (S : Stacks K prime), v.beforeH = B*prime^(r*((w+1)*r)) →
      a.records = LabelMask.records v → 0 < W →
      let D := embStk anchor S
      Ready d 1 (w+1) W D → ready (prime^w) D.R rs → D.R saved = [] →
      (D.R parents).length = v.beforeRows*v.rows*B →
      (D.R (port d regs 0)).length = ActualAffineScaling.modulus (w+1)^((d+1)*1)*W →
      a.signed = (List.range a.records).map inputs →
      (∀ i ∈ ([2,3,4,5] : List (Fin 6)), D.R (port d regs i) = []) →
      ScanReady a ports ext 0 (preparedPivots a (ports (Fin.last N).castSucc) S) →
      let ins := signedInputs table (w+1) a.records inputs
      ∃ outs z F t, ins.Forall₂ Correct outs ∧ z.user = u.user ∧ Exec body prog (mk u S) t (mk z F) ∧
        ScanReady {a with signed := outs} ports ext 0 (preparedPivots a (ports (Fin.last N).castSucc) F) ∧
        (∀ j, (∀ i, anchor i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        t ≤ 1+((v.beforeRows*v.rows*B)*(time (prime^w) (r*r) 1+5)+4 +
          ((ins.map (fun x => cost d T 1 (w+1) W x.1 + 2)).sum + 2) +
          (2*(a.records*(ActualAffineScaling.modulus (w+1)^((d+1)*1)*W))+2)) := by
  obtain ⟨prog,run⟩ := placedAnchorPass regs anchor capacity table body rs hk parents saved layout
  refine ⟨prog,?_⟩
  intro w W v B a inputs u S shape records hW D neutral radix free count width unsigned clean start ins
  have srcOff : ports (Fin.last N).castSucc ≠ ext 2 := off _ _
  have queue := start.queue
  simp only [preparedPivots,Function.update_of_ne srcOff.symm,List.drop_zero,unsigned] at queue
  have packed : D.R (port d regs 1) = ((signedInputs table (w+1) (LabelMask.records v) inputs).flatMap
      (fun x => payloadWord x.2)) ++ a.inputTail := by
    simpa [D,embStk_R,shared,signedInputs,← records,List.flatMap_map,Function.comp_def] using queue
  obtain ⟨outs,z,F,t,correct,exec,ht,_,hz,hi,ho,frame,untouched⟩ :=
    run v (w+1) B (by omega) shape 1 (w+1) W (by decide) (by omega) hW inputs u S a.inputTail
      neutral (by simpa using radix) free count width packed clean
  have bank : embStk ports F = embStk ports S := by
    unfold embStk
    congr 1
    · exact funext (fun i => (untouched _ (fun k => banks k i)).1)
    · exact funext (fun i => (untouched _ (fun k => banks k i)).2)
  have output := frame (regs 1)
  have out : F.R (ext 2) = outs.flatMap payloadWord ++ a.inputTail := by
    rw [← shared]
    simpa [port] using output
  exact ⟨outs,z,F,t,by simpa [ins,records] using correct,hz,exec,
    start.signedHandoff a ports ext off S F outs bank (fun i h => (untouched _ (fun k => external k i h)).2) out,
    untouched,by simpa [ins,records] using ht⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
