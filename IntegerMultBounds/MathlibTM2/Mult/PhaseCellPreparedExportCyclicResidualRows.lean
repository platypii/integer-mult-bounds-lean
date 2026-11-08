module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExportCyclicResidualRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaBoundaryVolumes

/-! Derive packed volumes from actual endpoint headers, then generate, traverse
and retire the remaining counters. No precomputed volume headers are inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def cyclicResidualVolumeState {A : ℕ} (left right w : ℕ) (S : Stacks 234 A) : Stacks 234 A :=
  {S with R := (Function.update (Function.update S.R 168 (List.replicate (left*w) tick))
    171 (List.replicate (right*w) tick))}

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 234 Q A U}

def preparedExportCyclicResidualRows : Pr P 234 Q A U :=
  .seq (embProg cyclicResidualRowsReg Empty.elim (cyclicReplicaBoundaryVolumes (P := Empty))) exportCyclicResidualRows

theorem preparedExportCyclicResidualRows_exec {s t : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (pairs : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt))) (w : ℕ)
    (v : HS 234 Q A U) (S : Stacks 234 A)
    (inputs : CyclicReplicaBoundaryInputs (s := s) t band a n w
      (embStk cyclicResidualRowsReg
        (cyclicResidualVolumeState (min n (s-a)) (n-min n (s-a)) w S)))
    (hblank : ∀ r : Fin 180, r.val < 6 → S.R (cyclicResidualRowsReg r) = [])
    (hleft : S.R 169 = pairs.flatMap (fun z => cstream A w (packedInterval a (min n (s-a)) z.1)))
    (hright : S.R 172 = pairs.flatMap (fun z => cstream A w (packedInterval 0 (n-min n (s-a)) z.2)))
    (hreplicas : (S.R 229).length = pairs.length)
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ r ∈ [(168 : Fin 234),171,174,175,176,177,178], S.R r = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ cyclicReplicaBoundaryVolumesCost a n w+
        exportCyclicResidualRowsCost pairs.length n (cyclicPrincipalBoundary s t band a n).card w ∧
      Exec body preparedExportCyclicResidualRows (mk v S) m
        (mk v' (exportedCyclicResidualRows S
          (pairs.flatMap (fun z => cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2))))) := by
  have hw : (S.R 130).length = w := by
    simpa [embStk,cyclicResidualRowsReg,cyclicResidualVolumeState] using inputs.width
  obtain ⟨vi,m₁,hui,hm₁,hei⟩ := cyclicReplicaBoundaryVolumes_exec
    (body := fun z : Empty => nomatch z) a (min n (s-a)) (n-min n (s-a)) w
    (embDn cyclicResidualRowsReg v) (embStk cyclicResidualRowsReg S)
    (by simpa [embStk,cyclicResidualRowsReg] using haSrc)
    (by simpa [embStk,cyclicResidualRowsReg] using hleftEnd)
    (by simpa [embStk,cyclicResidualRowsReg] using hrightEnd)
    (by simpa [embStk,cyclicResidualRowsReg] using hw)
    (by intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simpa [embStk,cyclicResidualRowsReg] using hfresh _ (by simp))
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    cyclicResidualRowsReg_injective (fun z => nomatch z) hei v rfl S rfl
  let J := cyclicResidualVolumeState (min n (s-a)) (n-min n (s-a)) w S
  have he₁' : Exec body (embProg cyclicResidualRowsReg Empty.elim (cyclicReplicaBoundaryVolumes (P := Empty)))
      (mk v S) m₁ (mk v₁ J) := by
    refine he₁.cast rfl ?_
    apply congrArg (mk v₁)
    rw [embOvr_updateR_updateR cyclicResidualRowsReg_injective]
    rfl
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := exportCyclicResidualRows_exec (body := body)
    hst hA band a n ha hn pairs w v₁ J inputs
    (by intro r hr
        have hr6 : r ≠ 6 := by intro he; have := congrArg Fin.val he; simp at this; omega
        have hr179 : r ≠ 179 := by intro he; have := congrArg Fin.val he; simp at this; omega
        have h168 : cyclicResidualRowsReg r ≠ 168 := by
          intro he; have hv := congrArg Fin.val he
          simp only [cyclicResidualRowsReg,ite_eq_right hr6,ite_eq_right hr179] at hv
          omega
        have h171 : cyclicResidualRowsReg r ≠ 171 := by
          intro he; have hv := congrArg Fin.val he
          simp only [cyclicResidualRowsReg,ite_eq_right hr6,ite_eq_right hr179] at hv
          omega
        simpa [J,cyclicResidualVolumeState,h168,h171] using hblank r hr)
    (by simpa [J,cyclicResidualVolumeState] using hleft)
    (by simpa [J,cyclicResidualVolumeState] using hright)
    (by simpa [J,cyclicResidualVolumeState] using hreplicas)
    (by simpa [J,cyclicResidualVolumeState] using hfresh 176 (by simp))
    (by simpa [J,cyclicResidualVolumeState] using hfresh 177 (by simp))
    (by simpa [J,cyclicResidualVolumeState] using hfresh 178 (by simp))
  have hfinal (rows : List (Fin (A+4))) : exportedCyclicResidualRows J rows = exportedCyclicResidualRows S rows := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ cyclicResidualRowsRetired
    · simp [exportedCyclicResidualRows,hk]
    · have h168 : k ≠ 168 := by intro h; subst k; exact hk (by simp [cyclicResidualRowsRetired])
      have h171 : k ≠ 171 := by intro h; subst k; exact hk (by simp [cyclicResidualRowsRetired])
      simp [exportedCyclicResidualRows,J,cyclicResidualVolumeState,hk,h168,h171,Function.update_apply]
  have hsplit : min n (s-a)+(n-min n (s-a)) = n := Nat.add_sub_of_le (Nat.min_le_left n (s-a))
  exact ⟨v₂,m₁+m₂,hu₂.trans (hu₁.trans hui),
    Nat.add_le_add (by simpa only [hsplit] using hm₁) hm₂,
    (Exec.seq he₁' he₂).cast rfl (congrArg (mk v₂) (hfinal _))⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
