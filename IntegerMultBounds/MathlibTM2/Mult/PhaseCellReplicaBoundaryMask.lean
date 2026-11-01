module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMetadataBoundaryMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingBounds
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Generate the shared mask and boundary count from retained interval geometry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

def replicaBoundaryMask : Pr P 242 Q A U :=
  .seq (embProg (Fin.castLE (by decide : 168 ≤ 242)) Empty.elim (metadataBoundaryMask (P := Empty)))
    (countSelectors 167 0 116 pairRe)

def replicaBoundaryMaskState (H : ReplicaHaloProblem s) (S : Stacks 242 A) : Stacks 242 A :=
  {S with R := (Function.update (Function.update S.R 167
    (couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span))
    116 (List.replicate (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card tick))}

def replicaBoundaryMaskCost (H : ReplicaHaloProblem s) :=
  144*H.metadataWidth+145+((29*H.span+2)*tblC H.metadataWidth 1+66*H.metadataWidth+2*H.span+70)+(7*H.span+4)

theorem replicaBoundaryMask_exec (H : ReplicaHaloProblem s) (hA : 4 ≤ A)
    (v : HS 242 Q A U) (S : Stacks 242 A)
    (hmeta : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk (Fin.castLE (by decide : 168 ≤ 242)) S))
    (hblank : ∀ k : Fin 242, k.val < 32 → S.R k = [])
    (h167 : S.R 167 = []) (h116 : S.R 116 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ replicaBoundaryMaskCost H ∧
      Exec body replicaBoundaryMask (mk v S) m (mk v' (replicaBoundaryMaskState H S)) := by
  let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
  have hinj : Function.Injective e := by intro i j he; exact Fin.ext (congrArg (fun k : Fin 242 => k.val) he)
  have hgeom := H.coupling_geometry
  obtain ⟨vi,m₁,hui,hm₁,hei⟩ := metadataBoundaryMask_exec (body := fun z : Empty => nomatch z)
    (embDn e v) (embStk e S) hmeta H.span_fit H.s_lt_t (by have h := H.span_fit; omega) H.span_fit
    (by nlinarith [hgeom.2]) hgeom.1 (by intro k hk; exact hblank (e k) hk)
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun z => nomatch z) hei v rfl S rfl
  let mask := couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span
  let J : Stacks 242 A := {S with R := Function.update S.R 167 mask}
  have he₁' : Exec body (embProg e Empty.elim (metadataBoundaryMask (P := Empty)))
      (mk v S) m₁ (mk v₁ J) := by
    apply he₁.cast rfl
    apply congrArg (mk v₁)
    rw [embOvr_updR hinj,embOvr_stk]
    simp [J,mask,e,embStk,h167]
  have hB : ∀ i ∈ haloBoundary s H.t H.band H.origin (H.origin+H.span),
      H.origin ≤ i.val ∧ i.val < H.origin+H.span := by
    intro i hi
    exact (mem_haloVertices _ _ _).mp (Finset.mem_sdiff.mp hi).1
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := countSelectors_exec (body := body)
    (src := 167) (saved := 0) (dst := 116) (by decide) pairRe v₁ J
    (by simpa [J] using hblank 0 (by decide))
  have hc := packedBoundaryMask_count H.s_lt_t hA H.band H.origin (H.origin+H.span) H.span_fit H.span_fit hB
  have hm₂' : m₂ ≤ 7*H.span+4 := by simpa [J,mask] using hm₂
  have he₂' : Exec body (countSelectors 167 0 116 pairRe) (mk v₁ J) m₂
      (mk v₂ (replicaBoundaryMaskState H S)) := by
    simpa [J,mask,hc,h116,replicaBoundaryMaskState] using he₂
  exact ⟨v₂,m₁+m₂,hu₂.trans (hu₁.trans hui),by unfold replicaBoundaryMaskCost; omega,Exec.seq he₁' he₂'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
