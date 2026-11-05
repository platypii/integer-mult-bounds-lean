module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryCropRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryGeometryWrites
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedOverwrite

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
  IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type}

/-- Run the fixed crop program in a larger bank. Generated controls stay in
place, the full-line source is retired, and every spectator tape is retained. -/
theorem embeddedGeneratedBoundaryCropRun_exec (body : P → Pr P T Q A U)
    (e : Fin 117 → Fin T) (hinj : Function.Injective e)
    (p width : ℕ) (hw : 0 < width) (hroom : 3*width < s)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (output : List (Fin (A+4))) (hproduced : ExactCoreProduced p s (fun _ => 0) J r output)
    (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R (e 15)).length = r.inputs.length) (hrows : (S.R (e 16)).length = s)
    (hword : (S.R (e 17)).length = 2*p+13)
    (hclean : ∀ i ∈ (generatedBoundaryCropPlan s width).cleanPorts, S.R (e i) = [])
    (hsource : S.R (e 94) = []) (depth : ℕ) :
    let F := rightUpdates ((boundaryGeometryWrites s width (2*p+13) [0,1,2]).map
      (fun (i,xs) => (e i,xs))) S
    let volume := r.inputs.length*s*(2*p+13)
    ∃ banks : List (List (List GaussianInt)), ∃ v' n, v'.user = v.user ∧
      n ≤ 242*volume+45 ∧
      List.Forall₂ (SeamCropRows p width r J) (boundaryCropSchedule s width).reverse banks ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v {F with R := Function.update F.R (e 94) output})+depth+(480*volume+86)) depth
        (embProg e (fun f : Empty => nomatch f) generatedBoundaryCropProgram)
        (mk v {F with R := Function.update F.R (e 94) output}) n
        (mk v' {F with R := (Function.update F.R (e 95)
          ((banks.map (fun (rows : List (List GaussianInt)) => cstream A (2*p+13) rows.flatten)).flatten++S.R (e 95)))}) := by
  dsimp only
  let L := exportBoundaryGeometryState s width (2*p+13) [0,1,2] (embStk e S)
  let F := rightUpdates ((boundaryGeometryWrites s width (2*p+13) [0,1,2]).map
    (fun (i,xs) => (e i,xs))) S
  have hF : embOvr e L.get S = F := embOvr_exportBoundaryGeometryState e hinj _ _ _ _ _
  have hstart : embOvr e {L with R := Function.update L.R 94 output}.get S =
      {F with R := Function.update F.R (e 94) output} := by
    rw [embOvr_updR hinj,hF]
  have hread : L.R 95 = S.R (e 95) :=
    exportBoundaryGeometryState_off s width (2*p+13) [0,1,2] (embStk e S) 95 (by decide +kernel)
  obtain ⟨banks,u,n,hu,hn,hbanks,hex⟩ := generatedBoundaryCropRun_exec
    (fun f : Empty => nomatch f) p width hw hroom r J output hproduced
    (embDn e v) (embStk e S) hclock hrows hword hclean hsource depth
  obtain ⟨v',hdn,huser,htrace⟩ := exec_emb_ovr_within_stock e hinj
    (ι := fun f : Empty => nomatch f) (body' := body) (by intro f; exact nomatch f)
    hex v rfl {F with R := Function.update F.R (e 94) output} (by
      rw [← hstart,embStk_ovr hinj])
  have hend (xs : List (Fin (A+4))) :
      embOvr e {L with R := Function.update L.R 95 xs}.get
        {F with R := Function.update F.R (e 94) output} =
      {F with R := Function.update F.R (e 95) xs} := by
    rw [← hstart,Host.embOvr_overwrite,embOvr_updR hinj,hF]
  change ExecWithin _ _ _ _ _ _ (mk v'
    (embOvr e {L with R := (Function.update L.R 95
      ((banks.map (fun (rows : List (List GaussianInt)) => cstream A (2*p+13) rows.flatten)).flatten++L.R 95))}.get
      {F with R := Function.update F.R (e 94) output})) at htrace
  rw [hend,hread] at htrace
  exact ⟨banks,v',n,huser.trans hu,hn,hbanks,htrace⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
