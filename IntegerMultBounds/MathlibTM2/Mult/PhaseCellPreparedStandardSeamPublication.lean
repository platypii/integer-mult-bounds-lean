module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardSeamArchivePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStandardBoundaryMasterRetirement

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement BoundaryCropMetadata
variable {Q A s : ℕ} [NeZero s] {P U : Type}

/-- Publication and release depend only on the exact prepared master state. -/
def preparedStandardSeamPublication (preparation : Pr P 117 Q A U) : Pr P 117 Q A U :=
  .seq preparation (.seq standardRestoringSeamProgram (clearWords [26,24,54,19]))

def preparedStandardSeamCost (preparationCost N narrowWidth s width k W : ℕ) : ℕ :=
  let L := coreLength s width k
  preparationCost + restoringSeamCost narrowWidth W N s (coreStart width k) L +
    (2*(coreStart width k*W+L*W+L*narrowWidth+N*L*narrowWidth)+9)

theorem preparedStandardSeamPublication_native (preparation : Pr P 117 Q A U)
    (hnative : mnNativePushBound 3 preparation) :
    mnNativePushBound 13 (preparedStandardSeamPublication preparation) := by
  exact ⟨mnNativePushBound_mono (by decide) hnative,
    ⟨restoringSeamPublication_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
      mnNativePushBound_mono (by decide) (clearWords_native _)⟩⟩

theorem preparedStandardSeamPublication_exec (body : P → Pr P 117 Q A U)
    (p coreWidth k W : ℕ) (hA : 4 ≤ A) (hW : 2*p+13 ≤ W)
    (cropCount : Fin 117)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (ks : List ℕ) (banks : List (List (List GaussianInt)))
    (hbanks : List.Forall₂ (SeamCropRows p coreWidth r J) (k::ks) banks)
    (hcoreWidth : 0 < coreWidth) (hk : k ∈ coreIndices s coreWidth)
    (ambient : List (List (Fin (A+4)))) (hlen : ambient.length = r.inputs.length)
    (hambient : ∀ line ∈ ambient, line.length = s*W)
    (sourceTail outputTail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hmasters : S.R 26 = [] ∧ S.R 24 = [] ∧ S.R 54 = [] ∧ S.R 19 = [])
    (hbits : (S.R cropCount).length = coreLength s coreWidth k*(2*p+13))
    (hfresh : ∀ i ∈ standardSeamPublicationPlan.support, i ≠ standardSeamPublicationPlan.advances → S.R i = [])
    (hsetupTmp : S.R (27:Fin 117) = []) (hsetupSaved : S.R (28:Fin 117) = [])
    (hretireTmp : S.R (29:Fin 117) = [])
    (hwide : (S.R (17:Fin 117)).length = W) (hword : (S.R (18:Fin 117)).length = 2*p+13)

    (hsrc : S.R (95:Fin 117) = (banks.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)
    (hdst : S.R (96:Fin 117) = ambient.flatten++outputTail)
    (hclock : (S.R (15:Fin 117)).length = r.inputs.length) (hline : (S.R (16:Fin 117)).length = s)
    (hblank : ∀ i ∈ [(20:Fin 117),(21:Fin 117),(22:Fin 117),(23:Fin 117)], S.R i = []) (depth : ℕ)
    (preparation : Pr P 117 Q A U) (preparationCost : ℕ)
    (hnative : mnNativePushBound 3 preparation)
    (hprepare : ∃ u m, u.user = v.user ∧ m ≤ preparationCost ∧
      Exec body preparation (mk v S) m
        (mk u (standardBoundaryMasterState cropCount r.inputs.length (2*p+13) s coreWidth k W S))) :
    ∃ rows rest, banks = rows::rest ∧ SeamCropRows p coreWidth r J k rows ∧
    List.Forall₂ (SeamCropRows p coreWidth r J) ks rest ∧
    let F : Stacks 117 A := {S with R := (Function.update
          (Function.update S.R (95:Fin 117)
            ((rest.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail)) (96:Fin 117)
            ((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail))}
    ∃ v' n, v'.user = v.user ∧
      n ≤ preparedStandardSeamCost preparationCost r.inputs.length (2*p+13) s coreWidth k W ∧
      Exec body (preparedStandardSeamPublication preparation) (mk v S) n (mk v' F) ∧
      mnSize (mk v' F) ≤ mnSize (mk v S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+13*preparedStandardSeamCost preparationCost r.inputs.length (2*p+13) s coreWidth k W) depth
        (preparedStandardSeamPublication preparation) (mk v S) n (mk v' F) ∧
      (∀ classes : ℕ → CorePublicationClass s coreWidth,
        classes k = singletonCorePublication s coreWidth k hk →
        PublicationBankPending ((k::ks).map classes) p W
          (seamPublicationTargets p r J) (3/(2:ℝ)^p) ambient →
        SeamArchiveNumericalState p coreWidth W r J classes 95 96 sourceTail outputTail S ks F) ∧
      ∀ j (hj : j < r.inputs.reverse.length),
        let out := pairedCellRead p W
          (((List.zipWith (fun row line =>
              (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
              (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail).drop (j*(s*W)))
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r)
            ((1/2 : ℂ) • fun i => value p (r.inputs.reverse[j] i))) (3/(2 : ℝ)^p) := by
  obtain ⟨u,m,hu,hm,hprep⟩ := hprepare
  let M := standardBoundaryMasterState cropCount r.inputs.length (2*p+13) s coreWidth k W S
  have hread (i : Fin 117) (hi : i ∉ [(26:Fin 117),24,54,19]) : M.R i = S.R i :=
    standardBoundaryMasterState_off cropCount r.inputs.length (2*p+13) s coreWidth k W S i hi
  obtain ⟨rows,rest,hbanks',hrows,hrest,u',n,hu',hn,hvol,hex,hstock,hstate,hpending,hnum,hgood⟩ :=
    standardSeamArchivePublication_exec body id Function.injective_id p coreWidth k W hA hW r J
      ks banks hbanks hcoreWidth hk ambient hlen hambient sourceTail outputTail u M
      (by simp [M,standardBoundaryMasterState]) (by simp [M,standardBoundaryMasterState])
      (by simpa [PreparedPublicationPlan.map,PreparedPublicationPlan.support,standardSeamPublicationPlan] using
        standardBoundaryMasterState_fresh cropCount r.inputs.length (2*p+13) s coreWidth k W S hfresh)
      (by simp only [id_eq]; rw [hread 27 (by decide)]; exact hsetupTmp)
      (by simp only [id_eq]; rw [hread 28 (by decide)]; exact hsetupSaved)
      (by simp only [id_eq]; rw [hread 29 (by decide)]; exact hretireTmp)
      (by simp only [id_eq]; rw [hread 17 (by decide)]; exact hwide)
      (by simp only [id_eq]; rw [hread 18 (by decide)]; exact hword)
      (by simp [M,standardBoundaryMasterState])
      (by simp only [id_eq]; rw [hread 95 (by decide)]; exact hsrc)
      (by simp only [id_eq]; rw [hread 96 (by decide)]; exact hdst)
      (by simp only [id_eq]; rw [hread 15 (by decide)]; exact hclock)
      (by simp only [id_eq]; rw [hread 16 (by decide)]; exact hline)
      (by intro i hi; rw [hread i (by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl <;> decide)]; exact hblank i hi) depth
  let source := (rest.map (fun rs => cstream A (2*p+13) rs.flatten)).flatten++sourceTail
  let output := (List.zipWith (fun row line =>
    (singletonCorePublication s coreWidth k hk).output W hcoreWidth (fun _ => row) line)
    (rows.map (List.map (symZ (2*p+13)))) ambient).flatten++outputTail
  obtain ⟨v',hv,hretire⟩ := standardBoundaryMasterRetirement_exec (body := body) u' S hmasters
    (List.replicate (coreStart coreWidth k*W) tick)
    (List.replicate (coreLength s coreWidth k*W) tick) (S.R cropCount)
    (List.replicate (r.inputs.length*coreLength s coreWidth k*(2*p+13)) tick) source output
  have hstage := hex.toExec
  change Exec body standardRestoringSeamProgram _ _ _ at hstage
  have hfull := Exec.seq hprep (Exec.seq hstage hretire)
  have hnumFinal (classes : ℕ → CorePublicationClass s coreWidth)
      (hclass : classes k = singletonCorePublication s coreWidth k hk)
      (hp : PublicationBankPending ((k::ks).map classes) p W
        (seamPublicationTargets p r J) (3/(2:ℝ)^p) ambient) :
      SeamArchiveNumericalState p coreWidth W r J classes 95 96 sourceTail outputTail S ks
        {S with R := Function.update (Function.update S.R 95 source) 96 output} := by
    refine ⟨rest,_,hrest,?_,rfl⟩
    apply hpending (ks.map classes)
    simpa only [List.map_cons,hclass] using hp

  refine ⟨rows,rest,hbanks',hrows,hrest,v',m + n + (2 * ((coreStart coreWidth k*W) +
    (coreLength s coreWidth k*W) + (S.R cropCount).length +
    (r.inputs.length*coreLength s coreWidth k*(2*p+13))) + 9),hv.trans (hu'.trans hu),?_,?_,?_,?_,hnumFinal,hgood⟩
  · dsimp only [preparedStandardSeamCost]
    rw [hbits]
    omega
  · simpa only [preparedStandardSeamPublication,M,standardBoundaryMasterState,List.length_replicate,Nat.add_assoc] using hfull
  · apply mn_replace_input_output_size_le v v' S 95 96 (by decide) source output
    · rw [hsrc,hbanks']
      simp only [List.map_cons,List.flatten_cons,List.length_append]
      dsimp only [source]
      simp only [List.length_append]
      omega
    · have hrowCount : rows.length = r.inputs.length := by
        simpa only [List.length_reverse] using hrows.2.length_eq.symm
      have hwideRows : ∀ row ∈ rows.map (List.map (symZ (2*p+13))),
          row.length = coreLength s coreWidth k := by
        intro row hr
        obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hr
        simpa only [List.length_map] using hrows.1 xs hxs
      have houtlen := singletonPublication_class_length hcoreWidth hk W
        (rows.map (List.map (symZ (2*p+13)))) ambient
        (by simp [hrowCount,hlen]) hwideRows hambient
      rw [hdst]
      simpa only [output,List.length_append,houtlen]
  · have he : Exec body (preparedStandardSeamPublication preparation) (mk v S) _
        (mk v' {S with R := Function.update (Function.update S.R 95 source) 96 output}) := hfull
    have hw := mn_native_exec_within he 13
      (preparedStandardSeamPublication_native preparation hnative) depth
      (mnSize (mk v S)+depth+13*preparedStandardSeamCost preparationCost r.inputs.length (2*p+13) s coreWidth k W)
      (by
        simp only [List.length_replicate]
        dsimp only [preparedStandardSeamCost]
        rw [hbits]
        omega)
    simpa only [List.length_replicate,Nat.add_assoc] using hw

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
