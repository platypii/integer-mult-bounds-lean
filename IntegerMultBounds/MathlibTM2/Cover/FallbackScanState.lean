module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackAdvanceLive
public import IntegerMultBounds.MathlibTM2.Cover.FallbackOutputPrefix
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalLabel

/-! Tape contents after a prefix of the physical residual records. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {T r d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

structure ScanData (r d w W : ℕ) where
  records : ℕ
  H : ℕ
  J : ℕ
  table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime)
  matrix : ℕ → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod (prime^(w+1)))
  input : ℕ → Fin ((prime^(w+1))^(d+1)*W) → ZMod 2
  signed : List (Record.Array d 1 (w+1) W)
  matrixTail : List (Fin (prime+4))
  pivotTail : List (Fin (prime+4))
  inputTail : List (Fin (prime+4))
  outputTail : List (Fin (prime+4))

namespace ScanData
variable (a : ScanData r d w W)

def pivots (j : ℕ) := classPivots (a.table (LabelStock.residue r (w+1) 1 j))

def pivotWord (j : ℕ) :=
  scheduleCode (A := prime) (a.pivots j) ++ orderedScheduleCode (List.finRange (d+1)).reverse (a.pivots j)

def matrices (j : ℕ) :=
  ((List.range a.records).drop j).flatMap (fun i => matrixWords prime a.H (a.matrix i)) ++ a.matrixTail

theorem matrices_succ {j : ℕ} (inside : j < a.records) :
    a.matrices j = matrixWords prime a.H (a.matrix j) ++ a.matrices (j+1) := by
  have h : j < (List.range a.records).length := by simpa using inside
  simp only [matrices,← List.getElem_cons_drop h,List.flatMap_cons,List.getElem_range,List.append_assoc]

end ScanData

/-- External tapes in order: mask, count, signed input, saved stack, scratch, output. -/
structure ScanReady (a : ScanData r d w W) (ports : Fin (N+2) ↪ Fin T) (ext : Fin 6 ↪ Fin T)
    (j : ℕ) (S : Stacks T prime) : Prop where
  queue : S.R (ext 2) = (a.signed.drop j).flatMap payloadWord ++ a.inputTail
  count : (S.R (ext 1)).length = M^(d+1)*W
  saved : S.R (ext 3) = []
  tmp : S.R (ext 4) = []
  acc : S.R (ext 5) = outputPrefix (LabelStock.live r (w+1) 1) a.matrix a.input j a.outputTail
  pivots : S.R (ports (Fin.last N).castSucc) = ((List.range a.records).drop j).flatMap a.pivotWord ++ a.pivotTail
  archive : S.R (ports (archivePorts 0 (columnBank 34))) = a.matrices j
  free : ∀ i : Fin N, 35 ≤ i.val → S.L (ports (columnPorts i).castSucc) = [] ∧ S.R (ports (columnPorts i).castSucc) = []
  blankSrc : ∀ z, readAt blank (S.L (ports (archivePorts 0 (columnBank 24)))) (S.R (ports (archivePorts 0 (columnBank 24)))) z = blank
  bank : j < a.records → ShearReady (columnBank.trans (archivePorts 0)) a.H a.J (a.matrix j)
    (a.matrices (j+1)) (fun _ : ZMod 2 => blank) (fun _ => blank) (fun _ => blank) 0 0 (a.input j) (embStk ports S)

theorem ScanReady.mask {a : ScanData r d w W} {ports : Fin (N+2) ↪ Fin T} {ext : Fin 6 ↪ Fin T}
    (off : ∀ i, ports i ≠ ext 0) {j S} (ready : ScanReady a ports ext j S) (bits : List (Fin (prime+4))) :
    ScanReady a ports ext j {S with R := Function.update S.R (ext 0) bits} := by
  let F := {S with R := Function.update S.R (ext 0) bits}
  have keep (i : Fin 6) (h : i ≠ 0) : F.R (ext i) = S.R (ext i) := Function.update_of_ne (ext.injective.ne h) _ _
  have internal (i) : F.R (ports i) = S.R (ports i) := Function.update_of_ne (off i) _ _
  have bank : embStk ports F = embStk ports S := by
    unfold embStk
    congr 1
    exact funext internal
  exact ⟨(keep 2 (by decide)).trans ready.queue,(congrArg List.length (keep 1 (by decide))).trans ready.count,
    (keep 3 (by decide)).trans ready.saved,(keep 4 (by decide)).trans ready.tmp,(keep 5 (by decide)).trans ready.acc,
    (internal _).trans ready.pivots,(internal _).trans ready.archive,
    fun i hi => ⟨(ready.free i hi).1,(internal _).trans (ready.free i hi).2⟩,
    fun z => by change readAt blank _ (F.R _) z = _; rw [internal]; exact ready.blankSrc z,
    fun h => bank.symm ▸ ready.bank h⟩

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
