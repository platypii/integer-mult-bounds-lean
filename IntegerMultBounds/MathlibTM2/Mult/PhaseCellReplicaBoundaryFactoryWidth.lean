module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth

/-! The factory retains all runtime masters with a blank width header. Generate
that single missing header from precision while preserving its numerical data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  ScalarPlacement

theorem PackedHaloRetainedHeaders.update_width {A P stage q l s t u band a b V old : ℕ}
    {S : Stacks 168 A} (h : PackedHaloRetainedHeaders P stage q l s t u band a b V old S) (w : ℕ) :
    PackedHaloRetainedHeaders P stage q l s t u band a b V w
      {S with R := Function.update S.R 130 (List.replicate w tick)} := by
  constructor
  · constructor
    · simpa using h.masters.precision
    · simpa using h.masters.fraction
    · simpa using h.masters.axis
    · simpa using h.masters.period
    · simpa using h.masters.parameter
    · simpa using h.masters.bandwidth
    · simpa using h.masters.lower
    · simpa using h.masters.upper
    · simp
  · apply h.geometry.of_frame
    · simp
    · intro k hk
      have hne : k ≠ 130 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact Function.update_of_ne hne _ _
  · simpa using h.stage
  · simpa using h.level

namespace ScalarPlacement
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

def replicaBoundaryFactoryWidthState (H : ReplicaHaloProblem s) (S : Stacks 242 A) : Stacks 242 A :=
  {S with R := Function.update S.R 130 (List.replicate H.wordWidth tick)}

theorem replicaBoundaryFactoryWidth_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (columns : List (ZMod s → GaussianInt)) (v : HS 242 Q A U) (S : Stacks 242 A)
    (hdata : ReplicaBoundaryFactorData H target columns S)
    (hbetween : PackedHaloBetweenInputs (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
      H.origin (H.origin+H.span) (publicationGeometryWidth H.t H.band) H.wordWidth (12*H.band+1)
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (extendStacks (by decide) S))
    (hwork : ReplicaFactoryWorkspace S) :
    let F := replicaBoundaryFactoryWidthState H S
    ∃ v', v'.user = v.user ∧
      Exec body (generateWordWidth 119 130 135) (mk v S) (8*H.precision+9) (mk v' F) ∧
      ReplicaBoundaryFactorData H target columns F ∧
      PackedHaloRetainedHeaders (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
        H.origin (H.origin+H.span) (publicationGeometryWidth H.t H.band) H.wordWidth
        (embStk packedRecoveryRuntimeReg (extendStacks (by decide) F)) ∧
      (F.R 157).length ≤ publicationGeometryWidth H.t H.band ∧ ReplicaFactoryWorkspace F := by
  dsimp only
  have hw : H.wordWidth = 2*H.precision+8 := by
    unfold ReplicaHaloProblem.wordWidth ReplicaHaloProblem.precision executionWidth executionPrecision
    omega
  have h130 : S.R 130 = [] := List.length_eq_zero_iff.mp hbetween.headers.masters.width
  have h135 : S.R 135 = [] := hbetween.scratch 135 (by decide)
  obtain ⟨v',hu,he⟩ := generateWordWidth_exec (body := body) (precision := 119) (width := 130) (tmp := 135)
    (by decide) H.precision v S hdata.bank.workspace.precision h130 h135
  have hframe (k : Fin 242) (hk : k ≠ 130) : (replicaBoundaryFactoryWidthState H S).R k = S.R k :=
    Function.update_of_ne hk _ _
  refine ⟨v',hu,by simpa only [←hw,replicaBoundaryFactoryWidthState] using he,?_,?_,?_,?_⟩
  · apply hdata.of_runtime_frame H target columns (F := replicaBoundaryFactoryWidthState H S) rfl
    · intro k hk; apply hframe; intro he; have hv := congrArg Fin.val he; norm_num at hv; omega
    · exact hframe 119 (by decide)
    · intro k hk h238; apply hframe; intro he; have hv := congrArg Fin.val he; norm_num at hv; omega
  · unfold replicaBoundaryFactoryWidthState
    rw [extendStacks_updateR]
    change PackedHaloRetainedHeaders _ _ _ _ _ _ _ _ _ _ _ _
      (embStk packedRecoveryRuntimeReg {extendStacks (by decide : 242 ≤ 248) S with
        R := Function.update (extendStacks (by decide : 242 ≤ 248) S).R
          (packedRecoveryRuntimeReg 130) (List.replicate H.wordWidth tick)})
    rw [embStk_updateR packedRecoveryRuntimeReg_injective]
    exact hbetween.headers.update_width H.wordWidth
  · change (Function.update S.R 130 (List.replicate H.wordWidth tick) 157).length ≤ _
    rw [Function.update_of_ne (by decide : (157 : Fin 242) ≠ 130)]
    exact hbetween.binaryLength
  · apply hwork.of_frame (F := replicaBoundaryFactoryWidthState H S)
    · intro i; apply hframe
      intro he; have hv := congrArg (fun k : Fin 242 => k.val) he
      have hi := i.isLt; change i.val = 130 at hv; omega
    · intro k hk; apply hframe
      simp only [replicaFactoryScratchPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
      norm_num at hk ⊢
      omega
    · rfl

noncomputable def replicaBoundaryFactoryWithWidth (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 242 Q A U :=
  .seq (packedBoundaryFactoryGeometry (P := P) (Q := Q) (A := A) (U := U) hR hQ)
    (generateWordWidth (P₀ := P) (Q := Q) (A := A) (U := U) 119 130 135)

theorem replicaBoundaryFactoryWithWidth_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (v : HS 242 Q A U) (S : Stacks 242 A) :
    ∃ v' F n, ∃ columns : List (ZMod s → GaussianInt), v'.user = v.user ∧
      n ≤ replicaBoundaryFactoryCost H target+(8*H.precision+9) ∧
      Exec body (replicaBoundaryFactoryWithWidth hR hQ) (mk v (replicaBoundaryFactoryInput H S)) n (mk v' F) ∧
      ReplicaBoundaryFactorData H target columns F ∧
      PackedHaloRetainedHeaders (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
        H.origin (H.origin+H.span) (publicationGeometryWidth H.t H.band) H.wordWidth
        (embStk packedRecoveryRuntimeReg (extendStacks (by decide) F)) ∧
      (F.R 157).length ≤ publicationGeometryWidth H.t H.band ∧ F.inp = S.inp ∧ F.out = S.out ∧
      ReplicaFactoryWorkspace F ∧ (F.R 159 = [] ∧ F.R 161 = []) := by
  obtain ⟨v₁,J,m,columns,hu₁,hm,he₁,hdata,hbetween,hinp,hout,hwork,hmasks⟩ := replicaBoundaryFactory_exec (body := body)
    H target hR hQ hA hp hwidth hpad htarget v S
  obtain ⟨v₂,hu₂,he₂,hdataF,hheaders,hcursor,hworkF⟩ := replicaBoundaryFactoryWidth_exec (body := body)
    H target columns v₁ J hdata hbetween hwork
  exact ⟨v₂,replicaBoundaryFactoryWidthState H J,m+(8*H.precision+9),columns,
    hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,hdataF,hheaders,hcursor,hinp,hout,hworkF,by simpa [replicaBoundaryFactoryWidthState] using hmasks⟩

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
