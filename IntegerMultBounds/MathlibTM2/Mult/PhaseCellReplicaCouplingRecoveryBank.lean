module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoverySharedBank

/-! Assemble recovery's shared bank from retained factory data and coupling's
generated page. Native arithmetic headers may still be live. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

theorem ReplicaBoundaryFactorData.coupling_recovery_bank
    (H : ReplicaHaloProblem s) (target : ℕ) (columns : List (ZMod s → GaussianInt))
    {S : Stacks 242 A} {F : Stacks 248 A}
    (h : ReplicaBoundaryFactorData H target columns S)
    (hL : (embStk packedBoundaryRecoveryBase F).L = S.L)
    (hmul : ∀ i : Fin 64, F.R ⟨i.val,by omega⟩ = [])
    (hq : F.R 119 = S.R 119)
    (hhigh : ∀ k : Fin 242, 168 ≤ k.val → k ≠ 238 →
      F.R (packedBoundaryRecoveryBase k) = S.R k)
    (hheaders : PackedHaloRetainedHeaders (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
      H.origin (H.origin+H.span) H.metadataWidth H.wordWidth (embStk packedRecoveryRuntimeReg F))
    (hprivate : ∀ k : Fin 248, 242 ≤ k.val → F.L k = [] ∧ F.R k = [])
    (hclean : ∀ k ∈ ([129,131,133,134,136,153] : List (Fin 242)), S.R k = [])
    (hframe : ∀ k ∈ ([129,131,133,134,136,153] : List (Fin 242)),
      F.R (packedBoundaryRecoveryBase k) = S.R k)
    (hfresh : ∀ k ∈ ([127,135,143,158,166] : List (Fin 248)), F.R k = [])
    (hrows : (F.R 140).length = 2*H.band+1)
    (hpage : F.R 138 = cstream A H.wordWidth
      (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span))
    (hcount : (F.R 139).length =
      (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band
        H.origin (H.origin+H.span) H.origin H.span).length) :
    ReplicaBoundaryFactorData H target columns (embStk packedBoundaryRecoveryBase F) ∧
      ReplicaRecoverySharedBank H (12*H.band+1) F := by
  have hdata : ReplicaBoundaryFactorData H target columns (embStk packedBoundaryRecoveryBase F) := by
    apply h.of_recovery_frame H target columns hL
    · exact hmul
    · exact hq
    · exact hhigh
  refine ⟨hdata,hdata.bank,hheaders,hfresh 143 (by decide),hprivate,?_,hrows,hpage,hcount⟩
  intro k hk
  have hc : k ∈ ([127,135,143,158,166] : List (Fin 248)) ∨
      ∃ i : Fin 242, i ∈ ([129,131,133,134,136,153] : List (Fin 242)) ∧
        packedBoundaryRecoveryBase i = k := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl (by decide)
      | exact Or.inr ⟨129,by decide,rfl⟩
      | exact Or.inr ⟨131,by decide,rfl⟩
      | exact Or.inr ⟨133,by decide,rfl⟩
      | exact Or.inr ⟨134,by decide,rfl⟩
      | exact Or.inr ⟨136,by decide,rfl⟩
      | exact Or.inr ⟨153,by decide,rfl⟩
  rcases hc with hk | ⟨i,hi,rfl⟩
  · exact hfresh k hk
  · exact (hframe i hi).trans (hclean i hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
