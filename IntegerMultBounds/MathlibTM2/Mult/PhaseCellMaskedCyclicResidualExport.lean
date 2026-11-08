module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedCyclicResidualExportState

/-! Execute mask generation and residual export in one arbitrary global
placement. Both cached source banks survive for the later recovery passes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def maskedCyclicResidualExport (leftBank rightBank : Fin 168 → Fin T) (e : Fin 234 → Fin T) : Pr P T Q A U :=
  .seq (cyclicReplicaBoundaryMasks leftBank rightBank (e 170) (e 173))
    (embProg e Empty.elim (preparedExportCyclicResidualRows (P := Empty)))

theorem maskedCyclicResidualExport_exec (H K : ReplicaHaloProblem s)
    (leftBank rightBank : Fin 168 → Fin T) (e : Fin 234 → Fin T)
    (hleftInj : Function.Injective leftBank) (hrightInj : Function.Injective rightBank) (he : Function.Injective e)
    (hleftDisjoint : ∀ i j, leftBank i ≠ e j) (hrightDisjoint : ∀ i j, rightBank i ≠ e j)
    {t : ℕ} (hst : s < t) (hA : 4 ≤ A) (band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (pairs : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt))) (w : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hleft : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk leftBank S))
    (hright : CouplingIntervalMetadata K.metadataWidth s K.t K.band K.origin (K.origin+K.span) K.origin K.span
      (embStk rightBank S))
    (hleftBlank : ∀ i : Fin 168, i.val < 32 → S.R (leftBank i) = [])
    (hrightBlank : ∀ i : Fin 168, i.val < 32 → S.R (rightBank i) = [])
    (hleftDst : S.R (e 170) = []) (hrightDst : S.R (e 173) = [])
    (inputs : CyclicReplicaBoundaryInputs (s := s) t band a n w
      (embStk cyclicResidualRowsReg (cyclicResidualVolumeState (min n (s-a)) (n-min n (s-a)) w
        (embStk e (cyclicResidualMaskState H K e S)))))
    (hblank : ∀ r : Fin 180, r.val < 6 → S.R (e (cyclicResidualRowsReg r)) = [])
    (hleftArchive : S.R (e 169) = pairs.flatMap (fun z => cstream A w (packedInterval a (min n (s-a)) z.1)))
    (hrightArchive : S.R (e 172) = pairs.flatMap (fun z => cstream A w (packedInterval 0 (n-min n (s-a)) z.2)))
    (hreplicas : (S.R (e 229)).length = pairs.length)
    (haSrc : (S.R (e 144)).length = a) (hleftEnd : (S.R (e 145)).length = a+min n (s-a))
    (hrightEnd : (S.R (e 146)).length = n-min n (s-a))
    (hfresh : ∀ r ∈ [(168 : Fin 234),171,174,175,176,177,178], S.R (e r) = []) :
    let rows := pairs.flatMap (fun z => cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2))
    let F := embOvr e (exportedCyclicResidualRows (embStk e S) rows).get S
    ∃ vf m, vf.user = v.user ∧
      m ≤ (placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K)+
        (cyclicReplicaBoundaryVolumesCost a n w+exportCyclicResidualRowsCost pairs.length n
          (cyclicPrincipalBoundary s t band a n).card w) ∧
      Exec body (maskedCyclicResidualExport leftBank rightBank e) (mk v S) m (mk vf F) ∧
      embStk e F = exportedCyclicResidualRows (embStk e S) rows ∧
      embStk leftBank F = embStk leftBank S ∧ embStk rightBank F = embStk rightBank S := by
  let M := cyclicResidualMaskState H K e S
  have hsep : e 170 ≠ e 173 := he.ne (by decide)
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hleftM,hrightM⟩ := cyclicReplicaBoundaryMasks_exec (body := body)
    H K leftBank rightBank hleftInj hrightInj (e 170) (e 173) hsep
    (fun i => hleftDisjoint i 170) (fun i => hrightDisjoint i 173)
    (fun i => hrightDisjoint i 170) (fun i => hleftDisjoint i 173)
    v S hleft hright hleftBlank hrightBlank hleftDst hrightDst
  have hproj := cyclicResidualMaskState_projection H K e he S
  have hread (k : Fin 234) (hk170 : k ≠ 170) (hk173 : k ≠ 173) :
      (embStk e M).R k = S.R (e k) := by
    change (embStk e (cyclicResidualMaskState H K e S)).R k = _
    rw [hproj]
    simp [Function.update_of_ne hk173,Function.update_of_ne hk170,embStk]
  obtain ⟨vi,m₂,hui,hm₂,hei⟩ := preparedExportCyclicResidualRows_exec
    (body := fun z : Empty => nomatch z) hst hA band a n ha hn pairs w
    (embDn e v₁) (embStk e M) inputs
    (by intro r hr
        have hr6 : r ≠ 6 := by intro h; have := congrArg Fin.val h; simp at this; omega
        have hr179 : r ≠ 179 := by intro h; have := congrArg Fin.val h; simp at this; omega
        have hsmall : (cyclicResidualRowsReg r).val < 6 := by
          simpa only [cyclicResidualRowsReg,ite_eq_right hr6,ite_eq_right hr179] using hr
        rw [hread _ (by intro h; have := congrArg Fin.val h; simp at this; omega)
          (by intro h; have := congrArg Fin.val h; simp at this; omega)]
        exact hblank r hr)
    (by rw [hread 169 (by decide) (by decide)]; exact hleftArchive)
    (by rw [hread 172 (by decide) (by decide)]; exact hrightArchive)
    (by rw [hread 229 (by decide) (by decide)]; exact hreplicas)
    (by rw [hread 144 (by decide) (by decide)]; exact haSrc)
    (by rw [hread 145 (by decide) (by decide)]; exact hleftEnd)
    (by rw [hread 146 (by decide) (by decide)]; exact hrightEnd)
    (by intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals rw [hread _ (by decide) (by decide)]; exact hfresh _ (by simp))
  obtain ⟨vf,hvf,hu,he₂⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) he
    (fun z => nomatch z) hei v₁ rfl M rfl
  let rows := pairs.flatMap (fun z => cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2))
  let E := exportedCyclicResidualRows (embStk e S) rows
  let F := embOvr e E.get S
  refine ⟨vf,m₁+m₂,hu.trans (hui.trans hu₁),Nat.add_le_add hm₁ hm₂,
    (Exec.seq he₁ he₂).cast rfl (congrArg (mk vf) (exportedCyclicResidualRows_maskFrame H K e he S rows)),
    embStk_ovr he E S,?_,?_⟩
  · refine Stacks.ext rfl rfl ?_ ?_
    · funext i
      exact (embOvr_off E.get S (fun j => (hleftDisjoint i j).symm)).1
    · funext i
      exact (embOvr_off E.get S (fun j => (hleftDisjoint i j).symm)).2
  · refine Stacks.ext rfl rfl ?_ ?_
    · funext i
      exact (embOvr_off E.get S (fun j => (hrightDisjoint i j).symm)).1
    · funext i
      exact (embOvr_off E.get S (fun j => (hrightDisjoint i j).symm)).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
