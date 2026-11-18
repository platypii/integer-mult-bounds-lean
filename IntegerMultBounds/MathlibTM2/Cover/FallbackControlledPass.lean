module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackResidualPass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackControlStreams

/-! Generate the control tapes and execute the residual pass on the signed queue. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {T r d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

open LabelTraversal

theorem controlledPass_exec (body : P → Pr P T columnCapacity prime U)
    (ports : Fin (N+2) ↪ Fin T) (ext : Fin 6 ↪ Fin T) (off : ∀ i k, ports i ≠ ext k)
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (rs : List (Pair T)) (size : rs.length = r*r) (parents saved : Fin T)
    (maskRegs : (parents :: saved :: (slots rs ++ [ext 0])).Nodup)
    (pivotRegs : (parents :: saved :: (slots rs ++ [ports (Fin.last N).castSucc])).Nodup) :
    ∃ prog, ∀ (v : RecursiveInterchangeLayout.Descriptor) (B : ℕ) (a : ScanData r d w W)
    (records : a.records = LabelMask.records v) (tables : a.table = table)
    (layout : v.beforeH = B*prime^(r*((w+1)*r))) (inputs : ℕ → Record.Array d 1 (w+1) W)
    (encoded : ∀ j < a.records, Record.scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j)
    (signed : (Record.signedInputs table (w+1) a.records inputs).Forall₂ Record.Correct a.signed)
    (liveSpec : ∀ j < a.records, LabelStock.live r (w+1) 1 j = true →
      ((a.matrix j).det = 1 ∨ (a.matrix j).det = -1) ∧
      (LabelRing.res prime (w+1) (by omega)).mapMatrix (a.matrix j) = table (LabelStock.residue r (w+1) 1 j))
    (padding : ∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
      ∃ symbol, Record.scalarArray (inputs j) = fun _ => symbol)
    (hm : M < 2^a.H) (hw : W < 2^a.J) (hW : 0 < W)
    (u : HS T columnCapacity prime U) (S : Stacks T prime)
    (radix : ready (prime^w) S.R rs) (free : S.R saved = []) (count : (S.R parents).length = v.beforeRows*v.rows*B)
    (empty : S.R (ext 0) = []) (fresh : a.outputTail = [])
    (start : ScanReady a ports ext 0 {S with R := Function.update S.R (ports (Fin.last N).castSucc) ((List.range a.records).flatMap a.pivotWord ++ S.R (ports (Fin.last N).castSucc))}),
    let output := (List.range a.records).flatMap (outputRecord (LabelStock.live r (w+1) 1) a.matrix a.input)
    ∃ z F n, z.user = u.user ∧ F.R (ext 2) = output ++ a.inputTail ∧ F.R (ext 5) = [] ∧
      F.R (ext 0) = [] ∧ F.R (ports (Fin.last N).castSucc) = a.pivotTail ∧
      F.R (ports (archivePorts 0 (columnBank 34))) = a.matrixTail ∧
      n ≤ 2*((v.beforeRows*v.rows*B)*(time (prime^w) (r*r) 1+5)+4) + (((List.range a.records).map fun j => a.recordTime U j + 4).sum + 2 + (2*(a.records*(M^(d+1)*W))+2)) ∧
      Exec body prog (mk u S) n (mk z F) := by
  obtain ⟨writer,emit⟩ := controlStreams_exec body table rs size (ext 0) (ports (Fin.last N).castSucc)
    parents saved maskRegs pivotRegs
  refine ⟨.seq writer (residualPass ports ext d),?_⟩
  intro v B a records tables layout inputs encoded signed liveSpec padding hm hw hW u S radix free count empty fresh start output
  subst table
  obtain ⟨y,l,hy,hl,write⟩ := emit v (w+1) B (by omega) layout u S (by simpa using radix) free count
  let pivot := ports (Fin.last N).castSucc
  let bits := (LabelMask.selectors r (w+1) a.records).map (bitSymbol (a := prime))
  let D := {S with R := Function.update S.R pivot ((List.range a.records).flatMap a.pivotWord ++ S.R pivot)}
  let F := {D with R := Function.update D.R (ext 0) bits}
  have code : a.pivotWord = fun j => scheduleCode (a.pivots j) ++ orderedScheduleCode (List.finRange (d+1)).reverse (a.pivots j) := rfl
  have gen : Exec body writer (mk u S) l (mk y F) := by
    dsimp only [F,D]
    rw [code]
    simpa [F,D,bits,pivot,← records,ScanData.pivotWord,ScanData.pivots,empty,off,
      Function.update_comm (off (Fin.last N).castSucc 0)] using write
  obtain ⟨z,G,n,hz,queue,acc,mask,pivots,archive,hn,run⟩ :=
    residualPass_exec a ports ext off inputs encoded signed liveSpec padding hm hw hW body y F fresh
      (start.mask (fun i => off i 0) bits) (Function.update_self ..)
  exact ⟨z,G,l+n,hz.trans hy,queue,acc,mask,pivots,archive,Nat.add_le_add (by simpa using hl) hn,.seq gen run⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
