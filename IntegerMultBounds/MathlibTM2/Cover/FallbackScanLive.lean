module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackScanState

/-! The live branch preserves the complete residual scan invariant. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {T r d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem ScanReady.live (a : ScanData r d w W) (ports : Fin (N+2) ↪ Fin T) (ext : Fin 6 ↪ Fin T)
    (off : ∀ i k, ports i ≠ ext k) (j : ℕ) (inside : j < a.records) (live : LabelStock.live r (w+1) 1 j = true)
    (det : (a.matrix j).det = 1 ∨ (a.matrix j).det = -1)
    (lift : (LabelRing.res prime (w+1) (by omega)).mapMatrix (a.matrix j) = a.table (LabelStock.residue r (w+1) 1 j))
    (inputs : ℕ → Record.Array d 1 (w+1) W) (encoded : Record.scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j)
    (signed : (Record.signedInputs a.table (w+1) a.records inputs).Forall₂ Record.Correct a.signed)
    (hm : M < 2^a.H) (hw : W < 2^a.J) (hW : 0 < W)
    (body : P → Pr P T columnCapacity prime U) (v : HS T columnCapacity prime U) (S : Stacks T prime)
    (ready : ScanReady a ports ext j S) :
    let bank := (columnBank.trans (archivePorts 0)).trans ports
    ∃ z F n, z.user = v.user ∧ ScanReady a ports ext (j+1) F ∧ F.R (ext 0) = S.R (ext 0) ∧
      n ≤ 6*(M^(d+1)*W)+6+(1+signedResidualTime U (a.pivots j) w W a.H a.J)+(4*(M^(d+1)*W)+4)+((d+1)*(d+1)*(4*a.H+4)+1) ∧
      Exec body (.seq (collectAnchorRecord ports (ext 1) (ext 2) (ext 3) (ext 4) (ext 5) d)
        (dropWords (bank 2) (bank 34) (bank 0) ((d+1)*(d+1)))) (Host.mk v S) n (Host.mk z F) := by
  intro bank
  have distinct (i k : Fin 6) (ne : i ≠ k) := ext.injective.ne ne
  have addr := physicalLabel_index (m := r) (w := w+1) j
  have res := physicalLabel_residue (m := r) (w := w+1) (by omega) j
  have run := advanceLive_exec (P := P) (U := U) ports (fun i => off i 2)
    (count := ext 1) (saved := ext 3) (tmp := ext 4) (acc := ext 5)
    (by simp [ext.injective.eq_iff,off,Ne.symm (off _ _)]) (by simp [ext.injective.eq_iff,off,Ne.symm (off _ _)])
    (fun i => off i _) (fun i => off i _) (fun i => off i _) (distinct _ _ (by decide))
    a.table (physicalLabel r (w+1) j) (a.matrix j) det (lift.trans (congrArg a.table res))
    _ (addr.symm ▸ inside) inputs a.signed signed a.H a.J hm hw hW body v S
    (a.matrices (j+1)) a.pivotTail a.inputTail (fun _ => blank) 0 (by simp) (a.input j)
  simp only [addr,← res] at run
  obtain ⟨z,F,n,word,hz,hn,exec,effect,acc,blanked,archive,next,free,pivots,queue,_,frame⟩ :=
    run (ready.bank inside) ready.free encoded ready.queue ready.count ready.blankSrc ready.saved ready.tmp ready.pivots
  have same (i : Fin 6) (hs : i ≠ 2) (ha : i ≠ 5) := (frame (ext i) (distinct _ _ hs) (distinct _ _ ha) (fun k => off k i)).2
  have unit : IsUnit (a.matrix j).det := by rcases det with h | h <;> simp [h]
  refine ⟨z,F,n,hz,⟨queue,(congrArg List.length (same 1 (by decide) (by decide))).trans ready.count,
    (same 3 (by decide) (by decide)).trans ready.saved,(same 4 (by decide) (by decide)).trans ready.tmp,
    ?_,pivots,archive,free,blanked,fun hj => next _ _ _ (a.matrices_succ hj)⟩,same 0 (by decide) (by decide),hn,exec⟩
  rw [outputPrefix_succ,outputRecord_live _ _ _ live unit word effect,← ready.acc]
  exact acc

end IntegerMultBounds.MathlibTM2.Cover.Fallback
