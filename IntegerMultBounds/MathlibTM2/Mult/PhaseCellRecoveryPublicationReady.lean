module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryNormalizationBanks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCroppedRecoveryReady

/-! Raw recovery readiness supplies all ordinary publication controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RecoveryBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {T A s : ℕ} [NeZero s]

structure PublicationReady (bank : RecoveryBank → Fin T) (hinj : Function.Injective bank)
    (d : InverseMasterInput s) (p W rows N : ℕ) (wl : List (Fin (A+4))) (S : Stacks T A) : Prop where
  width : S.R ((normalize bank hinj).scalar .wr) = wl
  scalar : ∀ i : TblR 25, i ≠ .wr → S.R ((normalize bank hinj).scalar i) = []
  values : ∀ i, (S.R ((queue bank hinj).parameters i)).length = d.values i
  queueBlank : ∀ k ∈ [(queue bank hinj).word,(queue bank hinj).saved,(queue bank hinj).tmp], S.R k = []
  header : S.R (normalize bank hinj).header = []
  precision : (S.R (normalize bank hinj).precision).length = p
  wide : (S.R (normalize bank hinj).wide).length = W
  rowCount : (S.R (normalize bank hinj).rows).length = rows
  replicas : (S.R (normalize bank hinj).replicas).length = N
  blank : ∀ k ∈ [(normalize bank hinj).count,(normalize bank hinj).work,(normalize bank hinj).saved,
    (normalize bank hinj).tmp,(normalize bank hinj).sp,(normalize bank hinj).sg,(normalize bank hinj).cy], S.R k = []
  ports : ∀ i, S.R ((normalize bank hinj).ports i) = []
  inputWidth : S.R (normalize bank hinj).inputWidth = []

theorem publicationReady_of_cropped (bank : RecoveryBank → Fin T) (hinj : Function.Injective bank)
    (d : InverseMasterInput s) (r : RawRecoveryJob s) (N offset rows : ℕ)
    (wl : List (Fin (A+4))) (S : Stacks T A)
    (h : (plan bank hinj).CroppedReady (crop bank hinj) d r N offset rows wl S) :
    PublicationReady bank hinj d r.problem.p r.W rows N wl S := by
  refine ⟨h.width,h.scalar,h.values,?_,?_,h.precision,h.packet,h.rows,h.replicas,?_,?_,?_⟩
  · intro k hk
    rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hk) with hk | hk | hk <;>
      subst k <;> exact h.masterScratch _ (by simp [queue,plan,masterPlan])
  · exact h.masterScratch _ (by simp [normalize,plan,masterPlan])
  · intro k hk
    simp only [normalize,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with hk | hk | hk | hk | hk | hk | hk <;> subst k <;> exact h.blank _ (by decide)
  · intro i
    exact h.blank _ (normalizePortIndex_ne_payload i)
  · exact h.blank 9 (by decide)

/-- Publication controls do not include the accumulated output tape. -/
theorem PublicationReady.of_bank_frame {bank : RecoveryBank → Fin T} {hinj : Function.Injective bank}
    {d : InverseMasterInput s} {p W rows N : ℕ} {wl : List (Fin (A+4))} {S F : Stacks T A}
    (h : PublicationReady bank hinj d p W rows N wl S)
    (hframe : ∀ i : RecoveryBank, i ≠ .control .cropDst → F.R (bank i) = S.R (bank i)) :
    PublicationReady bank hinj d p W rows N wl F := by
  have hs i : F.R (bank (.scalar i)) = S.R (bank (.scalar i)) := hframe _ (by simp)
  have hv i : F.R (bank (.parameter i)) = S.R (bank (.parameter i)) := hframe _ (by simp)
  have hw i : F.R (bank (.work i)) = S.R (bank (.work i)) := hframe _ (by simp)
  have hc i (hi : i ≠ RecoveryControl.cropDst) : F.R (bank (.control i)) = S.R (bank (.control i)) :=
    hframe _ (by simpa using hi)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hs .wr).trans h.width
  · intro i hi; exact (hs i).trans (h.scalar i hi)
  · intro i; rw [show (queue bank hinj).parameters i = bank (.parameter i) from rfl,hv]; exact h.values i
  · intro k hk
    simp only [queue,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with hk | hk | hk <;> subst k <;> rw [hc _ (by decide)] <;> exact h.queueBlank _ (by simp [queue])
  · exact (hc _ (by decide)).trans h.header
  · change (F.R (bank (.control .precision))).length = p
    rw [hc _ (by decide)]; exact h.precision
  · change (F.R (bank (.control .packet))).length = W
    rw [hc _ (by decide)]; exact h.wide
  · change (F.R (bank (.control .cropRows))).length = rows
    rw [hc _ (by decide)]; exact h.rowCount
  · change (F.R (bank (.control .replicas))).length = N
    rw [hc _ (by decide)]; exact h.replicas
  · intro k hk
    simp only [normalize,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with hk | hk | hk | hk | hk | hk | hk <;> subst k <;> rw [hw] <;> exact h.blank _ (by simp [normalize])
  · intro i; exact (hw _).trans (h.ports i)
  · exact (hw 9).trans h.inputWidth

/-- The exact bulk endpoint clears an external input port and publishes the
cropped batch; every normalization control is inherited from raw readiness. -/
theorem publicationReady_after_bulk (bank : RecoveryBank → Fin T) (hinj : Function.Injective bank)
    (d : InverseMasterInput s) (r : RawRecoveryJob s) (N offset rows : ℕ)
    (wl : List (Fin (A+4))) (S F : Stacks T A)
    (h : (plan bank hinj).CroppedReady (crop bank hinj) d r N offset rows wl S)
    (hframe : ∀ i, F.R (bank i) = S.R (bank i)) (source : Fin T)
    (hsource : ∀ i, source ≠ bank i) (output : List (Fin (A+4))) :
    PublicationReady bank hinj d r.problem.p r.W rows N wl
      {F with R := Function.update (Function.update F.R source []) ((crop bank hinj).reg 12) output} := by
  apply (publicationReady_of_cropped bank hinj d r N offset rows wl S h).of_bank_frame
  intro i hi
  have hdst : bank i ≠ (crop bank hinj).reg 12 := by
    change bank i ≠ bank (.control .cropDst)
    exact fun he => hi (hinj he)
  change Function.update (Function.update F.R source []) ((crop bank hinj).reg 12) output (bank i) = _
  rw [Function.update_of_ne hdst,Function.update_of_ne (hsource i).symm]
  exact hframe i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RecoveryBanks
