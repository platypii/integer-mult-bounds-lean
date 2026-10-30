module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveControls

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def packedCoreArchiveFromDimensions (radiusHeader coreHeader replicas clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T) : Pr P T Q A U :=
  .seq (.seq (packedCoreArchiveControls radiusHeader coreHeader width replicas skip count rows clock trash tmp)
    (packedCoreArchiveLoop clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp))
      (clearWords [skip,count,rows])

/-- Generate all slice controls and the loop count from borrowed dimensions,
publish the reversed halo archive in input order, and erase owned controls. -/
theorem packedCoreArchiveFromDimensions_exec
    (radiusHeader coreHeader replicas clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [radiusHeader,coreHeader,replicas,clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (q w coreWidth k radius : ℕ)
    (hleft : radius ≤ coreStart coreWidth k)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s)
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (hsrc : S.R src = (Ds.reverse.map (fun D => cstream A w
      (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D))).flatten++tail)
    (hR : (S.R radiusHeader).length = radius)
    (hL : (S.R coreHeader).length = coreLength s coreWidth k)
    (hw : (S.R width).length = w) (hN : (S.R replicas).length = Ds.length)
    (hclean : ∀ i ∈ [clock,skip,count,rows,savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = [])
    (inputs : List ((ZMod s → GaussianInt) × (ZMod s → ℝ))) (e : ℝ)
    (hgood : List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn
      (haloVertices s (coreStart coreWidth k-radius) (coreStart coreWidth k+coreLength s coreWidth k+radius))
      (fun i => (packedIntervalRead q w (coreStart coreWidth k-radius)
        (cstream A w (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D)) i).re)
      x.2 e) inputs Ds) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ packedCoreArchiveControlsCost radius (coreLength s coreWidth k) w Ds.length+
        (Ds.length*(packedCoreArchiveStepCost radius (coreLength s coreWidth k)
          (coreLength s coreWidth k+2*radius) w+3)+2)+
        (2*(radius*w+coreLength s coreWidth k*w+(coreLength s coreWidth k+2*radius))+7) ∧
      Exec body (packedCoreArchiveFromDimensions radiusHeader coreHeader replicas clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' F) ∧
      F.R src = tail ∧ F.R dst = (Ds.map (fun D => cstream A w (ownedCoreWords coreWidth k D))).flatten++S.R dst ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → F.R i = S.R i) ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (fun i => (packedIntervalRead q w (coreStart coreWidth k)
          (cstream A w (ownedCoreWords coreWidth k D)++S.R dst) i).re) x.2 e) inputs Ds := by
  have hr := hreg
  regs_ne hr
  have hc : [radiusHeader,coreHeader,width,replicas,skip,count,rows,clock,trash,tmp].Nodup := by regs_nodup
  have hlp : [clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup := by regs_nodup
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := packedCoreArchiveControls_exec (body := body)
    radiusHeader coreHeader width replicas skip count rows clock trash tmp hc radius (coreLength s coreWidth k) w Ds.length v S
    hR hL hw hN (by
      intro i hi
      apply hclean i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let B := packedCoreArchiveControlsState S skip count rows clock radius (coreLength s coreWidth k) w Ds.length
  have hB (i : Fin T) (hs : i ≠ skip) (hc : i ≠ count) (hr : i ≠ rows) (ht : i ≠ clock) : B.R i = S.R i := by
    simp only [B,packedCoreArchiveControlsState,Function.update_of_ne hs,Function.update_of_ne hc,
      Function.update_of_ne hr,Function.update_of_ne ht]
  have hz : ∀ i ∈ [savedSkip,saved,tmp,retireCount,trash,retireTmp], B.R i = [] := by
    intro i hi
    have hz := hclean i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    rw [hB i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | assumption | (apply Ne.symm; assumption)) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | assumption | (apply Ne.symm; assumption)) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | assumption | (apply Ne.symm; assumption)) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | assumption | (apply Ne.symm; assumption))]
    exact hz
  obtain ⟨v₂,G,n₂,hu₂,hn₂,he₂,hsrc',hdst,hclock,hi,ho,hleft',hframe,hgood'⟩ := packedCoreArchiveLoop_accurate_exec (body := body)
    clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp hlp
    v₁ B q w coreWidth k radius hleft hright Ds tail
    (by rw [hB src ‹skip ≠ src›.symm ‹count ≠ src›.symm ‹src ≠ rows› ‹clock ≠ src›.symm]; exact hsrc)
    (by simp [B,packedCoreArchiveControlsState])
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,packedCoreArchiveControlsState])
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,packedCoreArchiveControlsState])
    (by simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,packedCoreArchiveControlsState])
    (by rw [hB width ‹skip ≠ width›.symm ‹count ≠ width›.symm ‹rows ≠ width›.symm ‹clock ≠ width›.symm]; exact hw)
    hz inputs e hgood
  have hdstB : B.R dst = S.R dst := hB dst ‹skip ≠ dst›.symm ‹count ≠ dst›.symm ‹dst ≠ rows› ‹clock ≠ dst›.symm
  have hskipG : (G.R skip).length = radius*w := by
    rw [hframe skip ‹skip ≠ src› ‹skip ≠ dst› ‹clock ≠ skip›.symm]
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,packedCoreArchiveControlsState]
  have hcountG : (G.R count).length = coreLength s coreWidth k*w := by
    rw [hframe count ‹count ≠ src› ‹count ≠ dst› ‹clock ≠ count›.symm]
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,packedCoreArchiveControlsState]
  have hrowsG : (G.R rows).length = coreLength s coreWidth k+2*radius := by
    rw [hframe rows ‹src ≠ rows›.symm ‹dst ≠ rows›.symm ‹clock ≠ rows›.symm]
    simp (disch := first | assumption | (apply Ne.symm; assumption)) [B,packedCoreArchiveControlsState]
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [skip,count,rows] (by regs_nodup) v₂ G
  let F : Stacks T A := {G with R := fun i => if i ∈ [skip,count,rows] then [] else G.R i}
  have hn₃ : 2*([skip,count,rows].map (fun i => (G.R i).length)).sum+2*([skip,count,rows] : List (Fin T)).length+1 =
      2*(radius*w+coreLength s coreWidth k*w+(coreLength s coreWidth k+2*radius))+7 := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,hskipG,hcountG,hrowsG]
    omega
  rw [hn₃] at he₃
  have hF (i : Fin T) (hi : i ∉ [skip,count,rows]) : F.R i = G.R i := by simp only [F,ite_eq_right hi]
  refine ⟨v₃,F,n₁+n₂+(2*(radius*w+coreLength s coreWidth k*w+(coreLength s coreWidth k+2*radius))+7),hu₃.trans (hu₂.trans hu₁),Nat.add_le_add (Nat.add_le_add hn₁ hn₂) (Nat.le_refl _),
    (by simpa only [packedCoreArchiveFromDimensions] using Exec.seq (Exec.seq he₁ he₂) he₃),?_,?_,hi,ho,hleft',?_,?_⟩
  · rw [hF src (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨‹skip ≠ src›.symm,‹count ≠ src›.symm,‹src ≠ rows›⟩),hsrc']
  · rw [hF dst (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨‹skip ≠ dst›.symm,‹count ≠ dst›.symm,‹dst ≠ rows›⟩),hdst,hdstB]
  · intro i his hid
    by_cases hc : i = clock
    · subst i
      rw [hF clock (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨‹clock ≠ skip›,‹clock ≠ count›,‹clock ≠ rows›⟩),hclock,hclean clock (by simp)]
    by_cases hm : i ∈ [skip,count,rows]
    · simp only [F,ite_eq_left hm]
      symm
      apply hclean i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm ⊢
      rcases hm with rfl | rfl | rfl <;> simp
    · rw [hF i hm,hframe i his hid hc]
      apply hB i
      all_goals
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hm
        first | exact hm.1 | exact hm.2.1 | exact hm.2.2 | exact hc
  · simpa only [hdstB] using hgood'

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
