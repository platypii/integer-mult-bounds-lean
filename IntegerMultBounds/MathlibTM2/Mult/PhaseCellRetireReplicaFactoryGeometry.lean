module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Retire the factory's old binary geometry once before coupling regenerates
its wider geometry. Numerical factors and ordinary masters survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 242 Q A U}

def replicaFactoryGeometryPorts : List (Fin 168) := couplingIntervalPorts++[157,163]

def replicaFactoryGeometryNativePorts : List (Fin 242) :=
  replicaFactoryGeometryPorts.map (Fin.castLE (by decide : 168 ≤ 242))

def retiredReplicaFactoryGeometry (S : Stacks 242 A) : Stacks 242 A :=
  {S with R := fun k => if k ∈ replicaFactoryGeometryNativePorts then [] else S.R k}

def retireReplicaFactoryGeometry : Pr P 242 Q A U := clearWords replicaFactoryGeometryNativePorts

theorem retiredReplicaFactoryGeometry_frame (S : Stacks 242 A) (k : Fin 242)
    (hk : k ∉ replicaFactoryGeometryNativePorts) : (retiredReplicaFactoryGeometry S).R k = S.R k := by
  simp only [retiredReplicaFactoryGeometry,if_neg hk]

theorem retiredReplicaFactoryGeometry_blank (S : Stacks 242 A) (k : Fin 168)
    (hk : k ∈ replicaFactoryGeometryPorts) :
    (retiredReplicaFactoryGeometry S).R (Fin.castLE (by decide) k) = [] := by
  have hm : Fin.castLE (by decide : 168 ≤ 242) k ∈ replicaFactoryGeometryNativePorts :=
    List.mem_map.mpr ⟨k,hk,rfl⟩
  simp only [retiredReplicaFactoryGeometry,if_pos hm]

theorem retiredReplicaFactoryGeometry_low (S : Stacks 242 A) (k : Fin 242) (hk : k.val < 145) :
    (retiredReplicaFactoryGeometry S).R k = S.R k := by
  apply retiredReplicaFactoryGeometry_frame
  intro hm
  have hc : replicaFactoryGeometryNativePorts.all (fun k => decide (145 ≤ k.val)) = true := by decide +kernel
  have hh := of_decide_eq_true (List.all_eq_true.mp hc k hm)
  omega

theorem retireReplicaFactoryGeometry_exec (H : ReplicaHaloProblem s) (target V : ℕ)
    (columns : List (ZMod s → GaussianInt)) (v : HS 242 Q A U) (S : Stacks 242 A)
    (hdata : ReplicaBoundaryFactorData H target columns S)
    (hheaders : PackedHaloRetainedHeaders (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
      H.origin (H.origin+H.span) V H.wordWidth (embStk (Fin.castLE (by decide : 168 ≤ 242)) S))
    (hcursor : (S.R 157).length ≤ V) (hwork : ReplicaFactoryWorkspace S) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 26*V+27 ∧
      Exec body retireReplicaFactoryGeometry (mk v S) n (mk v' (retiredReplicaFactoryGeometry S)) ∧
      ReplicaBoundaryFactorData H target columns (retiredReplicaFactoryGeometry S) ∧
      CouplingMasterHeaders (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)
        (embStk (Fin.castLE (by decide : 168 ≤ 242)) (retiredReplicaFactoryGeometry S)) ∧
      ((retiredReplicaFactoryGeometry S).R 118).length = H.stage+1 ∧
      ((retiredReplicaFactoryGeometry S).R 120).length = H.l ∧
      ReplicaFactoryWorkspace (retiredReplicaFactoryGeometry S) := by
  have hbound (k : Fin 168) (hk : k ∈ replicaFactoryGeometryPorts) :
      (S.R (Fin.castLE (by decide : 168 ≤ 242) k)).length ≤ V := by
    rcases List.mem_append.mp hk with hk | hk
    · have hh := congrArg List.length (hheaders.geometry.encoded k hk)
      simp only [length_binSyms] at hh
      exact hh.le
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl
      · exact hcursor
      · exact hheaders.geometry.width.le
  have hsum := List.sum_le_length_nsmul
    (replicaFactoryGeometryNativePorts.map (fun k => (S.R k).length)) V (by
      intro x hx
      obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hk
      exact hbound i hi)
  have hstock : (replicaFactoryGeometryNativePorts.map (fun k => (S.R k).length)).sum ≤ 13*V := by
    simp only [List.length_map,show replicaFactoryGeometryNativePorts.length = 13 from rfl,
      nsmul_eq_mul] at hsum
    exact hsum
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) replicaFactoryGeometryNativePorts
    (by decide) v S
  refine ⟨v',_,hu,?_,he,?_,?_,?_,?_,?_⟩
  · change 2*(replicaFactoryGeometryNativePorts.map (fun k => (S.R k).length)).sum+2*13+1 ≤ _
    omega
  · apply hdata.of_runtime_frame H target columns (F := retiredReplicaFactoryGeometry S) rfl
    · intro k hk; exact retiredReplicaFactoryGeometry_low S k (by omega)
    · exact retiredReplicaFactoryGeometry_low S 119 (by decide)
    · intro k hk h238
      apply retiredReplicaFactoryGeometry_frame
      intro hm
      obtain ⟨i,hi,he⟩ := List.mem_map.mp hm
      have hv := congrArg (fun k : Fin 242 => k.val) he
      change i.val = k.val at hv
      have hi' := i.isLt
      omega
  · apply hheaders.masters.of_frame
    intro k hk
    apply retiredReplicaFactoryGeometry_frame
    simp only [couplingMasterPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [retiredReplicaFactoryGeometry_frame S 118 (by decide)]
    exact hheaders.stage
  · rw [retiredReplicaFactoryGeometry_frame S 120 (by decide)]
    exact hheaders.level
  · apply hwork.of_frame (F := retiredReplicaFactoryGeometry S)
    · intro i
      apply retiredReplicaFactoryGeometry_low
      have hi := i.isLt
      change i.val < 145
      omega
    · intro k hk
      apply retiredReplicaFactoryGeometry_frame
      have hc : replicaFactoryScratchPorts.all (fun k => decide (k ∉ replicaFactoryGeometryNativePorts)) = true := by decide +kernel
      exact of_decide_eq_true (List.all_eq_true.mp hc k hk)
    · rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
