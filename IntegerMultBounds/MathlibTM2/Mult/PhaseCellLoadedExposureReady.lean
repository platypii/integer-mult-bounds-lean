module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedExposureHeaders

/-! Actual caller-word loading supplies the allocated exposure readiness record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T A : ℕ}

noncomputable def loadedExposureHeaders_ready (src : Fin 8 → Fin T)
    (input output : Fin T) (hne : input ≠ output)
    (V s width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (borrowed : List (Fin (A+4))) (S : Stacks (T+175) A)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (hs : S.R (Fin.castAdd 175 (src 0)) = binSyms V s)
    (hw : S.R (Fin.castAdd 175 (src 1)) = binSyms V width)
    (hr : S.R (Fin.castAdd 175 (src 2)) = binSyms V radius)
    (hL : S.R (Fin.castAdd 175 (src 3)) = binSyms V L)
    (hV : (S.R (Fin.castAdd 175 (src 4))).length = V)
    (hword : (S.R (Fin.castAdd 175 (src 5))).length = w)
    (hcount : (S.R (Fin.castAdd 175 (src 6))).length = s*w)
    (hreplicas : (S.R (Fin.castAdd 175 (src 7))).length = Fs.length)
    (hsource : S.R (Fin.castAdd 175 input) = Fs.flatMap (fun C => cstream A w (chirpLine s C))++borrowed)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) :
    RealGatherExposureData V s width radius L w Fs borrowed (loadedExposureHeaders src S) := by
  have hread := loadedExposureHeaders_read src S hblank
  apply allocatedExposureReady input output hne V s width radius L w Fs borrowed (loadedExposureHeaders src S)
    hwidth hwide hLfit hwV hvol hA hVpos hgroup
  · rw [hread (4,163) (by simp [exposureHeaderAssignments])]; exact hV
  · rw [hread (0,145) (by simp [exposureHeaderAssignments])]; exact hs
  · rw [hread (1,150) (by simp [exposureHeaderAssignments])]; exact hw
  · rw [hread (2,152) (by simp [exposureHeaderAssignments])]; exact hr
  · rw [hread (3,165) (by simp [exposureHeaderAssignments])]; exact hL
  · rw [hread (5,94) (by simp [exposureHeaderAssignments])]; exact hword
  · rw [hread (6,168) (by simp [exposureHeaderAssignments])]; exact hcount
  · rw [hread (7,173) (by simp [exposureHeaderAssignments])]; exact hreplicas
  · change copyWordHeadersR S.R (exposureHeaderCopies src) S.R (Fin.castAdd 175 input) = _
    rw [copyWordHeadersR_off S.R (exposureHeaderCopies src) S.R _ ?_]
    · exact hsource
    · intro r hr
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      exact (exposure_prefix_ne_private _ _).symm
  · intro i hi
    change copyWordHeadersR S.R (exposureHeaderCopies src) S.R (Fin.natAdd T i) = []
    rw [copyWordHeadersR_off S.R (exposureHeaderCopies src) S.R _ ?_]
    · exact hblank i
    · intro r hr
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
      intro he
      have he' : p.2 = i := by
        apply Fin.ext
        have hv := congrArg (fun j : Fin (T+175) => j.val) he
        simp only [Fin.val_natAdd] at hv
        omega
      apply hi
      rw [←he']
      simp only [exposureHeaderAssignments,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
