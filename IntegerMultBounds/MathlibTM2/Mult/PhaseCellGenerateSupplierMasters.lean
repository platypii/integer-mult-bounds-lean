module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateInverseMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierInputPlan

/-! Compute changing supplier master headers from eight retained scalar words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

/-- The existing computed inverse dimensions are exactly the packed factory masters. -/
theorem PackedNormalizedJob.factoryMasters_eq_inverse (r : PackedNormalizedJob A s) :
    r.factoryMasters = inverseMasterValues r.p r.u r.l r.targetOut s r.t r.a r.b := by
  have hE := inverseExecutionExponent_eq r.p r.u r.l r.targetOut
    (haloBoundary s r.t (PhaseCellBand.width r.p r.u) r.a r.b).card
  simp only [PackedNormalizedJob.factoryMasters,PackedNormalizedJob.factoryTarget,inverseMasterValues,
    masterHeaderValues,executionStagePrecision,executionPrecision,hE]

noncomputable def generateSupplierMastersCost (r : PackedNormalizedJob A s) : ℕ :=
  ((r.p+r.u+r.l+r.targetOut+s+r.t+r.a+r.b)*(4*r.Bcore+10)+228*r.Bcore+263)+
    (inverseScalarAtoms r.p s r.t r.u r.a r.b*tblC r.Bcore 0+
      inverseMasterCopyCost r.Bcore r.factoryMasters)

theorem generateSupplierMasters_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (source : Fin 8 → Fin T) (ports : Fin 10 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i) (word saved tmp queue carry : Fin T)
    (hregs : ∀ i, [source i,rg .wr,word,saved,tmp,queue].Nodup) (hqueueOff : ∀ r, rg r ≠ queue)
    (r : PackedNormalizedJob A s)
    (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = ![r.p,r.u,r.l,r.targetOut,s,r.t,r.a,r.b] i)
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ k : TblR 25, k ≠ .wr → S.R (rg k) = [])
    (hmasters : ∀ i, S.R (ports i) = [])
    (hscratch : ∀ i ∈ [word,saved,tmp,queue], S.R i = []) (depth : ℕ) :
    ∃ v' F n z, v'.user = v.user ∧ n ≤ generateSupplierMastersCost r ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        ((392*r.Bcore+396)+3*(inverseScalarAtoms r.p s r.t r.u r.a r.b*tblC r.Bcore 0+
          inverseMasterCopyCost r.Bcore r.factoryMasters))) depth
        (generateSupplierMasters rg source ports word saved tmp queue carry) (Host.mk v S) n (Host.mk v' F) ∧
      tblHolds rg F (tblRho r.Bcore wl [] z) ∧
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ =
        (inverseInputScalars (A := A) r.p r.u r.l r.targetOut s r.t r.a r.b).val ⟨i.val,by omega⟩) ∧
      z.acc = [] ∧ (∀ i, z.val i < 2^r.Bcore) ∧
      (∀ i, F.R (ports i) = List.replicate (r.factoryMasters i) Node.tick) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ j, rg j ≠ k) → (∀ i, ports i ≠ k) → F.R k = S.R k := by
  simpa only [generateSupplierMastersCost,generateInverseMastersCost,r.factoryMasters_eq_inverse] using
    generateInverseMasters_exec (body := body) rg hrg source ports hports hsep word saved tmp queue carry hregs hqueueOff
      r.bounds.hst r.bounds.has r.bounds.hbs r.bounds.hband r.hbandRoom r.hgeometryRoom r.hprecisionRoom
      r.hvaluesFit wl hwl v S hvalues hwidth hblank hmasters hscratch depth

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
