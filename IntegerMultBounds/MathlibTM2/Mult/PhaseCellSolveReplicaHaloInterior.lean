module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRunReplicaHaloCells
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaEndpoints
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeHaloReplicaSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseKeyRuntime

/-! Initialize and execute the full replica halo interior from ordinary parameters,
then release runtime widths and restore borrowed endpoints. Only the packed
output changes; raw input, native stacks, masters and borrowed suffixes restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def solveReplicaHaloInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 144 Q A U :=
  .seq initializeHaloReplicaSchedule (.seq borrowReplicaEndpoints
    (.seq (runReplicaHaloCells hR hQ) (.seq releaseReplicaEndpoints releaseKeyRuntime)))

def solveReplicaHaloInteriorCost (p l B s t u target rhsExp a b : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let V := weightWorkspaceWidth P q w t u
  initializeHaloReplicaScheduleCost P N q l s t u band a b+
    (replicaHaloLoopCost p l B s t u target rhsExp V a b (haloCellPhases s t band a b)+1)+
    (4*a+4*b+6*B+14)+(2*(V+w)+5)

theorem solveReplicaHaloInterior_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hB : 0 < B)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ℕ → ZMod s → ℝ)
    (hx : ∀ n < B, SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) (x n)
      (fun k => (value (executionPrecision p l target rhsExp) (C n k)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed : List (Fin (A+4)))
    (h143 : (S.R 143).length = B) (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = [])
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l target rhsExp) (replicaAmbientWords B C)++borrowed) S) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let band := PhaseCellBand.width p u
    let phases := haloCellPhases s t band a b
    ∃ v' n, ∃ blocks : List (List (Fin (A+4))), v'.user = v.user ∧
      n ≤ solveReplicaHaloInteriorCost p l B s t u target rhsExp a b ∧
      blocks.reverse.flatten.length = B*(haloInterior s t band a b).card*w ∧
      Exec (embTab groupReg body) (solveReplicaHaloInterior hR hQ) (mk v S) n
        (mk v' {S with R := Function.update S.R 93 (blocks.reverse.flatten++S.R 93)}) ∧
      List.Forall₂ (fun phase ys => ReplicaBlockAccurate B (haloLength s t band a b phase)
        q w target (haloStart s t band a phase : ℕ) x ys) phases blocks ∧
      ∀ n : Fin B, PhaseCellInterface.ErrorOn (haloInterior s t band a b)
        (replicaBlocksRead q w n t band a b phases blocks) (x n) (1/(2 : ℝ)^target) := by
  dsimp only
  let P := 2^15*p
  let N := executionStagePrecision p l target rhsExp+1
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let band := PhaseCellBand.width p u
  let V := weightWorkspaceWidth P q w t u
  let K := (haloCellPhases s t band a b).length
  let keys := haloDescriptorPackets A V s t band a b
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  have hP : 13 ≤ P := by dsimp [P]; omega
  have hs : 0 < s := NeZero.pos s
  have h125 : S.R 125 = [] := List.eq_nil_of_length_eq_zero hready.keyWidth
  have h130 : S.R 130 = [] := List.eq_nil_of_length_eq_zero hready.wordWidth
  have h128 : S.R 128 = [] := by
    have hh := hready.masters (128,102) (by simp [groupHeaderCopies])
    exact List.eq_nil_of_length_eq_zero (by simpa [groupHeaderValue] using hh)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := initializeHaloReplicaSchedule_exec (body := body)
    P N q l s t u band a b hP hs hst hu hband has hbs (by omega) v S
    hready.masters haMaster hbMaster hready.left hready.blank (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact h125
      · exact h127
      · exact h130
      · exact hready.headerTemp
      · exact h138)
  simp only [hw] at he₁
  let S₁ : Stacks 144 A := {S with R := initializedKeyRuntimeR S.R V w K keys}
  obtain ⟨v₂,hu₂,he₂⟩ := borrowReplicaEndpoints_exec (body := embTab groupReg body) B a b v₁ S₁
    (by simpa [S₁,initializedKeyRuntimeR] using h143)
    (by simpa [S₁,initializedKeyRuntimeR] using haMaster)
    (by simpa [S₁,initializedKeyRuntimeR] using hbMaster)
    (by simpa [S₁,initializedKeyRuntimeR] using h139)
    (by simpa [S₁,initializedKeyRuntimeR] using hready.fresh 140 (by simp))
    (by simpa [S₁,initializedKeyRuntimeR] using hready.headerTemp)
  let S₂ : Stacks 144 A := {S₁ with R := borrowedReplicaEndpointR S₁.R B}
  have hprivate (k : Fin 144) (hk : k.val < 117) : S₂.R k = S.R k := by
    have h139' : k ≠ 139 := by intro he; subst k; norm_num at hk
    have h140' : k ≠ 140 := by intro he; subst k; norm_num at hk
    have h141' : k ≠ 141 := by intro he; subst k; norm_num at hk
    have h142' : k ≠ 142 := by intro he; subst k; norm_num at hk
    simp only [S₂,borrowedReplicaEndpointR,Function.update_of_ne h139',Function.update_of_ne h140',
      Function.update_of_ne h141',Function.update_of_ne h142']
    exact initializedKeyRuntimeR_private S.R V w K keys k hk
  have hready₂ : ReplicaCellReady P N q l s t u band B V w
      (cstream A w (replicaAmbientWords B C)++borrowed) S₂ := by
    constructor
    · intro r hr
      have hh := hready.masters r hr
      simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR,P,N,q,band] using hh
    · exact hready.left
    · intro k hk hk93 hk110; rw [hprivate k hk]; exact hready.blank k hk hk93 hk110
    · rw [hprivate 110 (by decide)]; exact hready.source
    · simp [S₂,borrowedReplicaEndpointR]
    · simp [S₂,borrowedReplicaEndpointR]
    · simpa [S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR] using hready.countSaved
    · simpa [S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR] using hready.headerTemp
    · simp [S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR]
    · simp [S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR]
    · intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR] using h128
      all_goals simpa [S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR] using hready.fresh _ (by simp)
  have hwide : s < 2^V := by
    obtain ⟨hb,_⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP hs hst hu hband
    dsimp only [V]; nlinarith only [hb,hst,hs]
  obtain ⟨v₃,S₃,n₃,blocks,hu₃,hn₃,he₃,hi₃,ho₃,hl₃,hframe,hvolume,hblocks,herror⟩ :=
    runReplicaHaloCells_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hB hpad C hC x hx
      v₂ S₂ borrowed (S.R 126) hwide
      (by simp [S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR,keys,band])
      (by simp [S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR,K,band]) hready₂
  obtain ⟨v₄,hu₄,he₄⟩ := releaseReplicaEndpoints_exec (body := embTab groupReg body)
    B (S.R 141) (S.R 142) v₃ S₃
    (by rw [hframe]; simp [replicaLoopR,S₂,borrowedReplicaEndpointR])
    (by rw [hframe]; simp [replicaLoopR,S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR])
    (by rw [hframe]; simp [replicaLoopR,S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR])
    (by rw [hframe]; simp [replicaLoopR,S₂,borrowedReplicaEndpointR])
  let S₄ : Stacks 144 A := {S₃ with R := (Function.update (Function.update (Function.update
    (Function.update S₃.R 139 []) 140 []) 141 (S.R 141)) 142 (S.R 142))}
  obtain ⟨v₅,hu₅,he₅⟩ := releaseKeyRuntime_exec (body := embTab groupReg body) V w v₄ S₄
    (by have hh : S₃.R 125 = List.replicate V tick := by
          rw [hframe]; simp [replicaLoopR,S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR]
        simpa [S₄,hh])
    (by have hh : S₃.R 130 = List.replicate w tick := by
          rw [hframe]; simp [replicaLoopR,S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR]
        simpa [S₄,hh])
  have hfinal : {S₄ with R := releasedKeyRuntimeR S₄.R} =
      {S with R := Function.update S.R 93 (blocks.reverse.flatten++S.R 93)} := by
    refine Stacks.ext hi₃ ho₃ hl₃ ?_
    funext k
    have h93 : S₂.R 93 = S.R 93 := hprivate 93 (by decide)
    simp only [S₄,releasedKeyRuntimeR]
    rw [hframe]
    by_cases h125' : k = 125
    · subst k; simp [h125]
    by_cases h130' : k = 130
    · subst k; simp [h130]
    by_cases h127' : k = 127
    · subst k; simp [replicaLoopR,h127]
    by_cases h139' : k = 139
    · subst k; simp [h139]
    by_cases h140' : k = 140
    · subst k; simp [hready.fresh 140 (by simp)]
    by_cases h141' : k = 141
    · subst k; simp
    by_cases h142' : k = 142
    · subst k; simp
    by_cases h126' : k = 126
    · subst k; simp [replicaLoopR]
    simp [replicaLoopR,S₂,S₁,borrowedReplicaEndpointR,initializedKeyRuntimeR,h93,h126',
      h125',h130',h127',h139',h140',h141',h142',Function.update_apply]
  refine ⟨v₅,n₁+((2*a+2*b+4*B+8)+(n₃+((2*B+2*(S.R 141).length+2*(S.R 142).length+6)+(2*(V+w)+5)))),
    blocks,hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,hvolume,?_,hblocks,herror⟩
  · dsimp only [solveReplicaHaloInteriorCost]
    dsimp only [P,N,q,w,band,V] at hn₁ hn₃ ⊢
    rw [haMaster,hbMaster]
    omega
  · exact Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃
      (Exec.seq he₄ (he₅.cast rfl (congrArg (mk v₅) hfinal)))))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
