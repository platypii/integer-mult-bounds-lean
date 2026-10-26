module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBlock
public import IntegerMultBounds.NLogN.PhaseCellHaloGeometry

/-! Select each ambient coordinate from its returned phase block. The complete
replica interior retains the cell tolerance without any phase-count factor. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def replicaBlocksRead {A s : ℕ} (q w n t band a b : ℕ) :
    List ℕ → List (List (Fin (A+4))) → ZMod s → ℝ
  | phase::phases, ys::blocks, j =>
    if phase = naturalPhase s t j.val then
      publishedBatchRead q w n (haloLength s t band a b phase)
        (haloStart s t band a phase : ℕ) ys j
    else replicaBlocksRead q w n t band a b phases blocks j
  | _, _, _ => 0

theorem replicaBlocksRead_errorOn {A s t B q w target : ℕ} [NeZero s]
    (hst : s < t) (band a b : ℕ) (x : ℕ → ZMod s → ℝ)
    (blocks : List (List (Fin (A+4))))
    (hblocks : List.Forall₂ (fun phase ys => ReplicaBlockAccurate B (haloLength s t band a b phase)
      q w target (haloStart s t band a phase : ℕ) x ys) (haloCellPhases s t band a b) blocks)
    (n : Fin B) :
    PhaseCellInterface.ErrorOn (haloInterior s t band a b)
      (replicaBlocksRead q w n t band a b (haloCellPhases s t band a b) blocks)
      (x n) (1/(2 : ℝ)^target) := by
  intro j hj
  let phase := naturalPhase s t j.val
  have hinterval := (haloInterior_phase_iff hst band a b phase j).mp
    ⟨hj,cell_eq_naturalPhase hst j⟩
  have hphase : phase ∈ haloCellPhases s t band a b :=
    (mem_haloCellPhases s t band a b phase).mpr
      ⟨naturalPhase_le_gap (NeZero.pos s) (ZMod.val_lt j).le,by dsimp only [haloLength]; omega⟩
  have hread : ∀ {phases : List ℕ} {blocks : List (List (Fin (A+4)))},
      List.Forall₂ (fun ph ys => ReplicaBlockAccurate B (haloLength s t band a b ph)
        q w target (haloStart s t band a ph : ℕ) x ys) phases blocks →
      phase ∈ phases →
      ‖replicaBlocksRead q w n t band a b phases blocks j-x n j‖ ≤ 1/(2 : ℝ)^target := by
    intro phases blocks hh
    induction hh with
    | nil => simp
    | @cons ph ys phases blocks hhead htail ih =>
      intro hmem
      by_cases he : ph = phase
      · subst ph
        have hp := ((mem_haloCellPhases s t band a b phase).mp hphase).2
        have hfit := (halo_solver_geometry hst band a b phase hp).2.1
        let i := j.val-haloStart s t band a phase
        have hi : i < haloLength s t band a b phase := by dsimp [i,haloLength]; omega
        have hji : (haloStart s t band a phase : ZMod s)+(i : ZMod s) = j := by
          have hh : haloStart s t band a phase+i = j.val := by dsimp [i]; omega
          simpa only [Nat.cast_add,ZMod.natCast_zmod_val] using
            congrArg (fun z : ℕ => (z : ZMod s)) hh
        have hcore : j ∈ publishedCellCore (haloStart s t band a phase : ℕ) (haloLength s t band a b phase) :=
          Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,hji⟩
        simpa only [replicaBlocksRead,if_pos (show phase = naturalPhase s t j.val from rfl)] using
          hhead.errorOn hfit n j hcore
      · have hmem' : phase ∈ phases := (List.mem_cons.mp hmem).resolve_left (Ne.symm he)
        have hne : ph ≠ naturalPhase s t j.val := he
        simpa only [replicaBlocksRead,if_neg hne] using
          ih hmem'
  exact hread hblocks hphase

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
