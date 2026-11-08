module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMetadataBoundaryMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingBounds

/-! Emit a boundary mask from cached interval metadata to a disjoint owned port.
The cached bank, including its former mask port, is preserved in full. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def replicaBoundaryMaskPort {T : ℕ} (bank : Fin 168 → Fin T) (dst : Fin T) (i : Fin 168) : Fin T :=
  if i = 167 then dst else bank i

theorem replicaBoundaryMaskPort_injective {T : ℕ} (bank : Fin 168 → Fin T)
    (hinj : Function.Injective bank) (dst : Fin T) (hoff : ∀ i, bank i ≠ dst) :
    Function.Injective (replicaBoundaryMaskPort bank dst) := by
  intro i j he
  by_cases hi : i = 167 <;> by_cases hj : j = 167
  · exact hi.trans hj.symm
  · have h : dst = bank j := by simpa only [replicaBoundaryMaskPort,ite_eq_left hi,ite_eq_right hj] using he
    exact False.elim (hoff j h.symm)
  · have h : bank i = dst := by simpa only [replicaBoundaryMaskPort,ite_eq_right hi,ite_eq_left hj] using he
    exact False.elim (hoff i h)
  · exact hinj (by simpa only [replicaBoundaryMaskPort,ite_eq_right hi,ite_eq_right hj] using he)

variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def placedReplicaBoundaryMask (bank : Fin 168 → Fin T) (dst : Fin T) : Pr P T Q A U :=
  embProg (replicaBoundaryMaskPort bank dst) Empty.elim (metadataBoundaryMask (P := Empty))

def placedReplicaBoundaryMaskCost (H : ReplicaHaloProblem s) :=
  144*H.metadataWidth+145+((29*H.span+2)*tblC H.metadataWidth 1+66*H.metadataWidth+2*H.span+70)

theorem placedReplicaBoundaryMask_exec (H : ReplicaHaloProblem s)
    (bank : Fin 168 → Fin T) (hinj : Function.Injective bank) (dst : Fin T)
    (hoff : ∀ i, bank i ≠ dst) (v : HS T Q A U) (S : Stacks T A)
    (hmeta : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk bank S))
    (hblank : ∀ i : Fin 168, i.val < 32 → S.R (bank i) = []) :
    ∃ vf m, vf.user = v.user ∧ m ≤ placedReplicaBoundaryMaskCost H ∧
      Exec body (placedReplicaBoundaryMask bank dst) (mk v S) m
        (mk vf {S with R := (Function.update S.R dst
          (couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span++S.R dst))}) := by
  let e := replicaBoundaryMaskPort bank dst
  have heinj : Function.Injective e := replicaBoundaryMaskPort_injective bank hinj dst hoff
  have hmeta' : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk e S) := by
    apply hmeta.of_frame
    · rfl
    · intro k hk
      have hk167 : k ≠ 167 := by intro h; subst k; norm_num [couplingIntervalPorts] at hk
      simp [embStk,e,replicaBoundaryMaskPort,hk167]
  have hgeom := H.coupling_geometry
  obtain ⟨vi,m,hui,hm,hei⟩ := metadataBoundaryMask_exec (body := fun z : Empty => nomatch z)
    (embDn e v) (embStk e S) hmeta' H.span_fit H.s_lt_t (by have := H.span_fit; omega)
    H.span_fit (by nlinarith [hgeom.2]) hgeom.1
    (by intro i hi
        have hi167 : i ≠ 167 := by intro he; have := congrArg Fin.val he; simp at this; omega
        simpa [embStk,e,replicaBoundaryMaskPort,hi167] using hblank i hi)
  obtain ⟨vf,hvf,hu,he⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) heinj
    (fun z => nomatch z) hei v rfl S rfl
  refine ⟨vf,m,hu.trans hui,hm,he.cast rfl ?_⟩
  apply congrArg (mk vf)
  rw [embOvr_updR heinj,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
