module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingMasterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata

/-! A shared retained-header interface for recovery and subsequent halo calls.
Only the fixed register placement is checked here; numerical facts remain generic. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack ScalarPlacement

def haloRetainedHeaderPorts : List (Fin 168) :=
  couplingMasterPorts++[118,120,163]++couplingIntervalPorts

def packedRecoveryRetainedPorts : List (Fin 248) :=
  [125,128,130,138,140,157]++haloRetainedHeaderPorts.map (Fin.castLE (by decide))

def packedRecoveryRetainedSafe (k : Fin 248) : Prop :=
  117 ≤ k.val ∧ k.val < 168 ∧ k ≠ 132 ∧ k ≠ 167 ∧
    (k ∈ ([125,128,130,138,140,157] : List (Fin 248)) ∨
      let i : Fin 168 := ⟨k.val%168,Nat.mod_lt _ (by decide)⟩
      packedRecoveryInteriorReg i = k ∧ 117 ≤ i.val ∧ i ≠ 125 ∧ i ≠ 130 ∧
        i ≠ 126 ∧ i ≠ 127 ∧ i ≠ 128 ∧ i ≠ 157 ∧ i ≠ 132)

instance (k : Fin 248) : Decidable (packedRecoveryRetainedSafe k) := by
  unfold packedRecoveryRetainedSafe
  infer_instance

theorem packedRecoveryRetainedPorts_safe (k : Fin 248) (hk : k ∈ packedRecoveryRetainedPorts) :
    packedRecoveryRetainedSafe k := by
  have h : packedRecoveryRetainedPorts.all (fun k => decide (packedRecoveryRetainedSafe k)) = true := by decide
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp h k hk

theorem haloRetainedHeaderPorts_safe (k : Fin 168) (hk : k ∈ haloRetainedHeaderPorts) :
    117 ≤ k.val ∧ k ≠ 132 ∧ k ≠ 138 ∧ k ≠ 139 ∧ k ≠ 140 ∧ k ≠ 167 := by
  have h : haloRetainedHeaderPorts.all (fun k => decide
      (117 ≤ k.val ∧ k ≠ 132 ∧ k ≠ 138 ∧ k ≠ 139 ∧ k ≠ 140 ∧ k ≠ 167)) = true := by decide
  simpa only [decide_eq_true_eq] using List.all_eq_true.mp h k hk

theorem haloRetainedHeaderPorts_mem (k : Fin 168) (hk : k ∈ haloRetainedHeaderPorts) :
    Fin.castLE (by decide : 168 ≤ 248) k ∈ packedRecoveryRetainedPorts :=
  List.mem_append_right _ (List.mem_map.mpr ⟨k,hk,rfl⟩)

/-- Transport retained ports through any execution with the placed view and
its existing frame; no numerical state is unfolded here. -/
theorem packedRecoveryRetained_frame {A : ℕ} (F S : Stacks 248 A) (H : Stacks 168 A)
    (hproj : embStk packedRecoveryInteriorReg F = H)
    (hoff : ∀ k, (∀ i, packedRecoveryInteriorReg i ≠ k) → F.L k = S.L k ∧ F.R k = S.R k)
    (hframe : ∀ i : Fin 168, 117 ≤ i.val → i ≠ 125 → i ≠ 130 → i ≠ 126 →
      i ≠ 127 → i ≠ 128 → i ≠ 157 → i ≠ 132 →
      H.L i = (embStk packedRecoveryInteriorReg S).L i ∧
      H.R i = (embStk packedRecoveryInteriorReg S).R i)
    (k : Fin 248) (hk : k ∈ packedRecoveryRetainedPorts) :
    F.L k = S.L k ∧ F.R k = S.R k := by
  have hs := packedRecoveryRetainedPorts_safe k hk
  rcases hs.2.2.2.2 with hold | hplaced
  · exact hoff k (fun i => packedRecoveryInteriorReg_avoids_retained i k hold)
  · let i : Fin 168 := ⟨k.val%168,Nat.mod_lt _ (by decide)⟩
    obtain ⟨hfix,hi,h125,h130,h126,h127,h128,h157,h132⟩ := hplaced
    have hpL := congrArg (fun B : Stacks 168 A => B.L i) hproj
    have hpR := congrArg (fun B : Stacks 168 A => B.R i) hproj
    have hf := hframe i hi h125 h130 h126 h127 h128 h157 h132
    exact ⟨(congrArg F.L hfix).symm.trans ((hpL.trans hf.1).trans (congrArg S.L hfix)),
      (congrArg F.R hfix).symm.trans ((hpR.trans hf.2).trans (congrArg S.R hfix))⟩

/-- Native scratch available between calls; width and borrowed source are retained. -/
def PackedHaloNativeClean {A : ℕ} (S : Stacks 168 A) : Prop :=
  ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → S.R (Fin.castLE (by decide) i) = []

structure PackedHaloRetainedHeaders {A : ℕ} (P stage q l s t u band a b V w : ℕ)
    (S : Stacks 168 A) : Prop where
  masters : CouplingMasterHeaders P q w s t u band a b S
  geometry : CouplingIntervalMetadata V s t band a b a (b-a) S
  stage : (S.R 118).length = stage
  level : (S.R 120).length = l

/-- Equal ready parameters give equal retained-header stock, even when the
unary symbols themselves differ. Geometry words agree by their encoding. -/
theorem PackedHaloRetainedHeaders.length_eq
    {A P stage q l s t u band a b V w : ℕ} {S F : Stacks 168 A}
    (h : PackedHaloRetainedHeaders P stage q l s t u band a b V w S)
    (h' : PackedHaloRetainedHeaders P stage q l s t u band a b V w F)
    (k : Fin 168) (hk : k ∈ haloRetainedHeaderPorts) :
    (F.R k).length = (S.R k).length := by
  rcases List.mem_append.mp hk with hk | hk
  · have hm := h.masters
    have hm' := h'.masters
    rcases hm with ⟨hP,hq,hs,ht,hu,hband,ha,hb,hw⟩
    rcases hm' with ⟨hP',hq',hs',ht',hu',hband',ha',hb',hw'⟩
    have hstage := h.stage
    have hstage' := h'.stage
    have hl := h.level
    have hl' := h'.level
    have hV := h.geometry.width
    have hV' := h'.geometry.width
    simp only [List.mem_append,couplingMasterPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;> omega
  · rw [h'.geometry.encoded k hk,h.geometry.encoded k hk]

theorem PackedHaloRetainedHeaders.of_frame {A P stage q l s t u band a b V w : ℕ}
    {S F : Stacks 168 A} (h : PackedHaloRetainedHeaders P stage q l s t u band a b V w S)
    (hframe : ∀ k ∈ haloRetainedHeaderPorts, F.R k = S.R k) :
    PackedHaloRetainedHeaders P stage q l s t u band a b V w F := by
  constructor
  · apply h.masters.of_frame
    intro k hk
    exact hframe k (List.mem_append_left _ (List.mem_append_left _ hk))
  · apply h.geometry.of_frame
    · exact hframe 163 (by simp [haloRetainedHeaderPorts])
    · intro k hk
      exact hframe k (List.mem_append_right _ hk)
  · rw [hframe 118 (by simp [haloRetainedHeaderPorts])]
    exact h.stage
  · rw [hframe 120 (by simp [haloRetainedHeaderPorts])]
    exact h.level

/-- Resetting the per-input width preserves every other retained header. -/
theorem PackedHaloRetainedHeaders.of_frame_except_width
    {A P stage q l s t u band a b V w w' : ℕ} {S F : Stacks 168 A}
    (h : PackedHaloRetainedHeaders P stage q l s t u band a b V w S)
    (hwidth : (F.R 130).length = w')
    (hframe : ∀ k ∈ haloRetainedHeaderPorts, k ≠ 130 → F.R k = S.R k) :
    PackedHaloRetainedHeaders P stage q l s t u band a b V w' F := by
  constructor
  · constructor
    · rw [hframe 117 (by decide) (by decide)]; exact h.masters.precision
    · rw [hframe 119 (by decide) (by decide)]; exact h.masters.fraction
    · rw [hframe 121 (by decide) (by decide)]; exact h.masters.axis
    · rw [hframe 122 (by decide) (by decide)]; exact h.masters.period
    · rw [hframe 123 (by decide) (by decide)]; exact h.masters.parameter
    · rw [hframe 124 (by decide) (by decide)]; exact h.masters.bandwidth
    · rw [hframe 141 (by decide) (by decide)]; exact h.masters.lower
    · rw [hframe 142 (by decide) (by decide)]; exact h.masters.upper
    · exact hwidth
  · apply h.geometry.of_frame (hframe 163 (by decide) (by decide))
    intro k hk
    apply hframe k (List.mem_append_right _ hk)
    simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hframe 118 (by decide) (by decide)]; exact h.stage
  · rw [hframe 120 (by decide) (by decide)]; exact h.level

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
