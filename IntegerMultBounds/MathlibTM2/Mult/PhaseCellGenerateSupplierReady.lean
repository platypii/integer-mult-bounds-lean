module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierChangingHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierBaseReady

/-! Actual numerical-header generation completes ordinary supplier readiness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierInputPlan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem generateReady_exec (input : SupplierInputPlan T) (hmastersInjective : Function.Injective input.masters)
    (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (hsep : ∀ i r, rg r ≠ input.masters i) (word saved tmp queue carry : Fin T)
    (hregs : ∀ i, [input.parameters i,rg .wr,word,saved,tmp,queue].Nodup)
    (hqueueOff : ∀ r, rg r ≠ queue) (hscalarWidth : rg .wr = input.width)
    (e : Fin 117 → Fin T) (he : Function.Injective e)
    (hP : e 114 = input.masters 0) (hq : e 112 = input.masters 2)
    (ht : e 98 = input.masters 5) (hu : e 99 = input.masters 6)
    (hgeometryDst : e 115 = input.publication.retained 1)
    (hgeometryOff : ∀ k ∈ [(0 : Fin 117),1,2,3,4,94,104,115], ∀ i, input.masters i ≠ e k)
    (hprotected : ∀ k ∈ input.baseSupport, (∀ i, input.masters i ≠ k) ∧ k ≠ input.publication.retained 1)
    (r : PackedNormalizedJob A s) (v : HS T Q A U) (S : Stacks T A) (hbase : input.BaseReady r S)
    (hblank : ∀ k : TblR 25, k ≠ .wr → S.R (rg k) = []) (hmasters : ∀ i, S.R (input.masters i) = [])
    (hscratch : ∀ i ∈ [word,saved,tmp,queue], S.R i = [])
    (hgeometryBlank : ∀ k ∈ [(0 : Fin 117),1,2,3,4,94,104,115], S.R (e k) = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (generateSupplierMastersCost r+(50*r.Bcore+51))+supplierGeometryWidthCost r ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        (((392*r.Bcore+396)+3*(inverseScalarAtoms r.p s r.t r.u r.a r.b*tblC r.Bcore 0+
          inverseMasterCopyCost r.Bcore r.factoryMasters))+
          (8*(8*r.q+9)+18*weightWidthCost (2^15*r.p) r.q (2*r.q+8) r.t r.u))) depth
        (supplierChangingHeaders rg input.parameters input.masters word saved tmp queue carry e)
        (Host.mk v S) n (Host.mk v' F) ∧ input.Ready r F ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ i, input.masters i ≠ k) → k ≠ input.publication.retained 1 → F.R k = S.R k := by
  obtain ⟨v',F,n,huser,hn,hex,hheads,hgeometry,hI,hO,hL,hframe⟩ := supplierChangingHeaders_exec (body := body)
    rg hrg input.parameters input.masters hmastersInjective hsep word saved tmp queue carry hregs hqueueOff e he hP hq ht hu hgeometryOff
    r (S.R input.width) hbase.classHeaders.width v S hbase.parameters (by rw [hscalarWidth]) hblank hmasters
    hscratch hgeometryBlank depth
  have hbaseF := hbase.of_frame (F := F) (by
    intro k hk
    exact hframe k (hprotected k hk).1 (by simpa only [hgeometryDst] using (hprotected k hk).2)) hL
  refine ⟨v',F,n,huser,hn,hex,hbaseF.complete ?_ ?_,hI,hO,hL,?_⟩
  · intro i
    rw [hheads,List.length_replicate]
  · rw [←hgeometryDst,hgeometry,List.length_replicate]
  · intro k hp hk
    exact hframe k hp (by simpa only [hgeometryDst] using hk)
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierInputPlan
