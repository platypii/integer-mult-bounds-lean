module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingIntervalMetadata
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBoundaryWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCellInputBank
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Generate post-factory geometry in the shared machine, with a complete frame
for the retained factors, native input and publication destination. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U}

def packedBoundaryGeometryPorts : List (Fin 242) := [145,146,147,148,149,151,154,156,164]

def placedRetainedCouplingIntervalMetadata : Pr P 242 Q A U :=
  embProg packedHaloRuntimeReg Empty.elim prepareRetainedCouplingIntervalMetadata

theorem placedRetainedCouplingIntervalMetadata_exec {V s t band a b origin N : ℕ}
    (hfitV : origin+(N+2*band)+s < 2^V)
    (v : HS 242 Q A U) (S : Stacks 242 A) (hV : (S.R 163).length = V)
    (hs : (S.R 121).length = s) (ht : (S.R 122).length = t)
    (hband : (S.R 124).length = band) (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (h155 : S.R 155 = binSyms V origin) (h165 : S.R 165 = binSyms V N)
    (hblank : ∀ k ∈ [(0 : Fin 168),1,2,3,145,146,147,148,149,151,154,156,164],
      (embStk packedHaloRuntimeReg S).R k = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ (s+t+band+a+b)*(4*V+10)+56*V+77 ∧
      Exec body placedRetainedCouplingIntervalMetadata (mk v S) n (mk v' F) ∧
      CouplingIntervalMetadata V s t band a b origin N (embStk packedHaloRuntimeReg F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, k ∉ packedBoundaryGeometryPorts → F.R k = S.R k := by
  obtain ⟨v₁,n,hu₁,hn,he,hmeta⟩ := prepareRetainedCouplingIntervalMetadata_exec
    (body := fun p : Empty => nomatch p) hfitV (embDn packedHaloRuntimeReg v)
    (embStk packedHaloRuntimeReg S) hV hs ht hband ha hb h155 h165 hblank
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    packedHaloRuntimeReg_injective (fun p => nomatch p) he v rfl S rfl
  let T := embStk packedHaloRuntimeReg S
  let T₁ : Stacks 168 A := {T with R := (completedCouplingIntervalR
    (retainedCouplingMetadataR T.R V s t band a b) V band origin N)}
  let F := embOvr packedHaloRuntimeReg T₁.get S
  have hproj : embStk packedHaloRuntimeReg F = T₁ :=
    embStk_ovr packedHaloRuntimeReg_injective T₁ S
  refine ⟨v₂,F,n,hu₂.trans hu₁,hn,he₂,?_,rfl,rfl,embOvr_right_left S _,?_⟩
  · rw [hproj]; exact hmeta
  · intro k hk
    by_cases hlo : k.val < 168
    · let i : Fin 168 := ⟨k.val,hlo⟩
      have hi : packedHaloRuntimeReg i = k := Fin.ext rfl
      have hnot : i ∉ [(145 : Fin 168),146,147,148,149,151,154,156,164] := by
        simpa [packedBoundaryGeometryPorts,Fin.ext_iff,i] using hk
      have hh := congrArg (fun B : Stacks 168 A => B.R i) hproj
      have hh' : F.R k = T₁.R i := by
        simpa only [embStk,Function.comp_apply,hi] using hh
      exact hh'.trans (retainedCouplingIntervalMetadataR_off T.R V s t band a b origin N i hnot)
    · exact (packedHaloRuntime_high_frame S T₁ k (by omega)).2

theorem packedBoundaryGeometry_factorState {A : ℕ} (S F : Stacks 242 A)
    (hframe : ∀ k, k ∉ packedBoundaryGeometryPorts → F.R k = S.R k) :
    boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg F)) =
      boundaryFactorState (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg S)) := by
  have hhigh (k : Fin 242) (hk : 168 ≤ k.val) : F.R k = S.R k := by
    apply hframe
    intro hm
    simp only [packedBoundaryGeometryPorts,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> contradiction
  rw [packedBoundaryFactorState_of_high_frame S F hhigh,hframe 143 (by decide)]
  exact Function.update_eq_self _ _

theorem packedBoundaryGeometry_native {A : ℕ} (S F : Stacks 242 A) (hL : F.L = S.L)
    (hframe : ∀ k, k ∉ packedBoundaryGeometryPorts → F.R k = S.R k)
    (hinp : F.inp = S.inp) (hout : F.out = S.out) :
    embStk ScalarPlacement.packedCellCoreReg (embStk packedHaloRuntimeReg F) =
      embStk ScalarPlacement.packedCellCoreReg (embStk packedHaloRuntimeReg S) := by
  refine Stacks.ext hinp hout ?_ ?_
  · funext i; exact congrFun hL _
  · funext i
    apply hframe
    intro hm
    have hi := i.isLt
    simp only [packedBoundaryGeometryPorts,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with he | he | he | he | he | he | he | he | he
    all_goals
      have hv := congrArg (fun k : Fin 242 => k.val) he
      change i.val = _ at hv
      omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
