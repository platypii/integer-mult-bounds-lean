module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanState

/-! The padding branch preserves the complete residual scan invariant. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {T r d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem ScanReady.padding (a : ScanData r d w W) (ports : Fin (N+2) ↪ Fin T) (ext : Fin 6 ↪ Fin T)
    (off : ∀ i k, ports i ≠ ext k) (j : ℕ) (inside : j < a.records) (pad : LabelStock.live r (w+1) 1 j = false)
    (inputs : ℕ → Record.Array d 1 (w+1) W) (encoded : Record.scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j)
    (symbol : Fin 4) (constant : Record.scalarArray (inputs j) = fun _ => symbol)
    (signed : (Record.signedInputs a.table (w+1) a.records inputs).Forall₂ Record.Correct a.signed)
    (body : P → Pr P T columnCapacity prime U) (v : HS T columnCapacity prime U) (S : Stacks T prime)
    (ready : ScanReady a ports ext j S) :
    let bank := (columnBank.trans (archivePorts 0)).trans ports
    let pivot := ports (Fin.last N).castSucc
    ∃ z F n, z.user = v.user ∧ ScanReady a ports ext (j+1) F ∧ (∀ k, k ≠ ext 2 → k ≠ ext 5 → (∀ i, ports i ≠ k) → F.R k = S.R k) ∧
      n ≤ 4*(d+1)*(d+1)+1+(4*(M^(d+1)*W)+4)+((d+1)*(d+1)*(4*a.H+4)+1) ∧
      Exec body (.seq (paddingRecord (d+1) pivot (ext 1) (ext 2) (ext 5) (ext 4))
        (dropWords (bank 2) (bank 34) (bank 0) ((d+1)*(d+1)))) (Host.mk v S) n (Host.mk z F) := by
  intro bank pivot
  let word := payloadWord (inputs j)
  let queue := (a.signed.drop (j+1)).flatMap payloadWord ++ a.inputTail
  let schedule := ((List.range a.records).drop (j+1)).flatMap a.pivotWord ++ a.pivotTail
  let F := {S with R := Function.update (Function.update (Function.update (Function.update S.R pivot schedule)
    (ext 2) queue) (ext 5) (word.reverse ++ S.R (ext 5))) (bank 34) (a.matrices (j+1))}
  have bp (i : Fin 35) : bank i ≠ pivot := by
    apply ports.injective.ne
    intro h
    have e := congrArg Fin.val h
    change i.val = rowSwapBlock.tapes+35 at e
    omega
  have be (i : Fin 35) (k : Fin 6) : bank i ≠ ext k := off _ _
  have pe (k : Fin 6) : pivot ≠ ext k := off _ _
  have lo : j < (List.range a.records).length := by simpa using inside
  have split := Record.paddingOutput a.table inputs a.signed signed j inside symbol constant
  have len : word.length = M^(d+1)*W := by simp [word,payloadWord,ActualAffineScaling.modulus]
  have layout := ready.bank inside
  obtain ⟨z,n,hz,hn,run⟩ := advancePadding_exec bank body pivot (ext 1) (ext 2) (ext 5) (ext 4)
    (by simp [pe,ext.injective.eq_iff]) (fun i => ⟨bp i,be i _,be i _⟩) v S a.H (a.matrix j) (a.pivots j)
    _ word queue schedule layout.archive ((congrArg List.length layout.modulus).trans (length_binSyms ..))
    (layout.scratch 0 (by decide)).2 (by simpa [schedule,← List.getElem_cons_drop lo,ScanData.pivotWord,List.append_assoc] using ready.pivots)
    (by simpa [queue,word,split,List.append_assoc] using ready.queue) (ready.count.trans len.symm) ready.tmp
  have external (k : Fin 6) (hs : k ≠ 2) (ha : k ≠ 5) : F.R (ext k) = S.R (ext k) := by
    simp [F,Function.update_of_ne,(be 34 k).symm,(pe k).symm,ext.injective.ne hs,ext.injective.ne ha]
  have internal (i : Fin (N+2)) (hp : ports i ≠ pivot) (hm : ports i ≠ bank 34) : F.R (ports i) = S.R (ports i) := by
    simp [F,Function.update_of_ne,hp,hm,off]
  have cells (i : Fin 35) (hi : i ≠ 34) : F.R (bank i) = S.R (bank i) :=
    internal _ (bp i) (bank.injective.ne hi)
  have archive : F.R (bank 34) = a.matrices (j+1) := Function.update_self ..
  refine ⟨z,F,n,hz,⟨?_,(congrArg List.length (external 1 (by decide) (by decide))).trans ready.count,
    (external 3 (by decide) (by decide)).trans ready.saved,(external 4 (by decide) (by decide)).trans ready.tmp,
    ?_,?_,archive,?_,?_,?_⟩,(fun k hs ha outside => by simp [F, Function.update_of_ne, hs, ha,
      show k ≠ pivot from (outside _).symm, show k ≠ bank 34 from (outside _).symm]),by simpa [len] using hn,run⟩
  · simp [F,queue,(be 34 2).symm,ext.injective.eq_iff]
  · have out : outputRecord (LabelStock.live r (w+1) 1) a.matrix a.input j = word := by
      exact outputRecord_padding (b := w+1) _ pad a.matrix a.input (inputs j) encoded
    rw [outputPrefix_succ,out,← ready.acc]
    simp [F,word,(be 34 5).symm]
  · change F.R pivot = schedule
    simp [F,(bp 34).symm,pe]
  · intro i hi
    refine ⟨(ready.free i hi).1,(internal _ (ports.injective.ne ?_) (ports.injective.ne ?_)).trans (ready.free i hi).2⟩
    · intro h
      have e := congrArg Fin.val h
      change i.val = rowSwapBlock.tapes+35 at e
      omega
    · intro h
      have e := congrArg Fin.val h
      change i.val = 34 at e
      omega
  · intro x
    change readAt blank _ (F.R (bank 24)) x = _
    rw [cells 24 (by decide)]
    exact ready.blankSrc x
  · intro hj
    exact layout.next (F := embStk ports F) (archive.trans (a.matrices_succ hj)) (fun _ => rfl) cells rfl

end IntegerMultBounds.MathlibTM2.Cover.Fallback
