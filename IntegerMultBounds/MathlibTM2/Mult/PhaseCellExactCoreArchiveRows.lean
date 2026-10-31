module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreArchive
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRowReader
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandStreams
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalArchive

/-! Return actual S3 archive output as coefficient rows, with suffix-independent
accuracy and the reversed replica order used by the transpose input. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement PhaseCellInterface
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem exactCoreArchive_rows_exec
    (clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (p coreWidth k : ℕ)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (output : List (Fin (A+4)))
    (hproduced : ExactCoreProduced p coreWidth (fun _ => k) J r output)
    (hstart : coreStart coreWidth k ≤ s)
    (tail : List (Fin (A+4)))
    (hsrc : S.R src = output++tail)
    (hclock : (S.R clock).length = r.inputs.length)
    (hskip : (S.R skip).length = coreStart coreWidth k*(2*p+13))
    (hcount : (S.R count).length = coreLength s coreWidth k*(2*p+13))
    (hrows : (S.R rows).length = s)
    (hwidth : (S.R width).length = (2*p+13))
    (hclean : ∀ i ∈ [savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = []) :
    ∃ coreRows : List (List GaussianInt), ∃ v' F n, v'.user = v.user ∧
      n ≤ r.inputs.length*(packedCoreArchiveStepCost (coreStart coreWidth k) (coreLength s coreWidth k)
        s (2*p+13)+3)+2 ∧
      Exec body (packedCoreArchiveLoop clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' F) ∧
      F.R src = tail ∧ F.R dst = cstream A (2*p+13) coreRows.flatten++S.R dst ∧
      F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i) ∧
      (∀ row ∈ coreRows, row.length = coreLength s coreWidth k) ∧
      List.Forall₂ (fun input row =>
        let out := packedIntervalRead p (2*p+13) (coreStart coreWidth k) (cstream A (2*p+13) row)
        (∀ i ∈ ownedCore s coreWidth k, ‖out i‖ ≤ 1) ∧
        ErrorOn (ownedCore s coreWidth k) out
          ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r) ((1/2 : ℂ) • fun i => value p (input i)))
          (3/(2 : ℝ)^p)) r.inputs.reverse coreRows := by
  obtain ⟨Ds,v',F,n,hu,hn,he,hs,hd,hc,hi,ho,hl,hframe,hgood⟩ := exactCoreArchive_exec (body := body)
    clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp hreg
    v S p coreWidth k r J output hproduced hstart tail hsrc hclock hskip hcount hrows hwidth hclean
  let coreRows := Ds.reverse.map (ownedCoreWords coreWidth k)
  have hbytes : cstream A (2*p+13) coreRows.flatten =
      (Ds.reverse.map (fun D => cstream A (2*p+13) (ownedCoreWords coreWidth k D))).flatten := by
    simpa only [List.flatMap] using cstream_flatMap_rows (A := A) (w := 2*p+13) Ds.reverse (ownedCoreWords coreWidth k)
  refine ⟨coreRows,v',F,n,hu,hn,he,hs,by rw [hbytes]; exact hd,hc,hi,ho,hl,hframe,?_,?_⟩
  · intro row hr
    obtain ⟨D,hD,he⟩ := List.mem_map.mp hr
    subst row
    exact ownedCoreWords_length coreWidth k D
  · apply List.forall₂_map_right_iff.mpr
    apply hgood.imp
    intro input D hD
    have hread (i : ZMod s) (hi : i ∈ ownedCore s coreWidth k) :
        packedIntervalRead p (2*p+13) (coreStart coreWidth k)
          (cstream A (2*p+13) (ownedCoreWords coreWidth k D)++S.R dst) i =
        packedIntervalRead p (2*p+13) (coreStart coreWidth k)
          (cstream A (2*p+13) (ownedCoreWords coreWidth k D)) i := by
      obtain ⟨hlo,hhi⟩ := (mem_haloVertices _ _ i).mp hi
      apply packedIntervalRead_append_row
      · exact hlo
      · simpa only [ownedCoreWords_length] using hhi
    constructor
    · intro i hi; rw [←hread i hi]; exact hD.1 i hi
    · intro i hi; rw [←hread i hi]; exact hD.2 i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
