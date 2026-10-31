module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredSupplierMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateSupplierGeometryWidth

/-! Per-job header setup reuses one scalar table and one geometry bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def supplierChangingHeaders (rg : TblR 25 → Fin T) (source : Fin 8 → Fin T)
    (ports : Fin 10 → Fin T) (word saved tmp queue carry : Fin T) (e : Fin 117 → Fin T) : Pr P T Q A U :=
  .seq (restoredSupplierMasters rg source ports word saved tmp queue carry) (generateSupplierGeometryWidth e)

theorem supplierChangingHeaders_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (source : Fin 8 → Fin T) (ports : Fin 10 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i) (word saved tmp queue carry : Fin T)
    (hregs : ∀ i, [source i,rg .wr,word,saved,tmp,queue].Nodup) (hqueueOff : ∀ r, rg r ≠ queue)
    (e : Fin 117 → Fin T) (he : Function.Injective e)
    (hP : e 114 = ports 0) (hq : e 112 = ports 2) (ht : e 98 = ports 5) (hu : e 99 = ports 6)
    (hgeometryOff : ∀ k ∈ [(0 : Fin 117),1,2,3,4,94,104,115], ∀ i, ports i ≠ e k)
    (r : PackedNormalizedJob A s)
    (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = ![r.p,r.u,r.l,r.targetOut,s,r.t,r.a,r.b] i)
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ k : TblR 25, k ≠ .wr → S.R (rg k) = [])
    (hmasters : ∀ i, S.R (ports i) = [])
    (hscratch : ∀ i ∈ [word,saved,tmp,queue], S.R i = [])
    (hgeometryBlank : ∀ k ∈ [(0 : Fin 117),1,2,3,4,94,104,115], S.R (e k) = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ (generateSupplierMastersCost r+(50*r.Bcore+51))+supplierGeometryWidthCost r ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        (((392*r.Bcore+396)+3*(inverseScalarAtoms r.p s r.t r.u r.a r.b*tblC r.Bcore 0+
          inverseMasterCopyCost r.Bcore r.factoryMasters))+
          (8*(8*r.q+9)+18*weightWidthCost (2^15*r.p) r.q (2*r.q+8) r.t r.u))) depth
        (supplierChangingHeaders rg source ports word saved tmp queue carry e) (Host.mk v S) n (Host.mk v' F) ∧
      (∀ i, F.R (ports i) = List.replicate (r.factoryMasters i) Node.tick) ∧
      F.R (e 115) = List.replicate r.V Node.tick ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ i, ports i ≠ k) → k ≠ e 115 → F.R k = S.R k := by
  obtain ⟨v₁,M,n₁,hu₁,hn₁,he₁,hheads,hI,hO,hL,hframe⟩ := restoredSupplierMasters_exec (body := body)
    rg hrg source ports hports hsep word saved tmp queue carry hregs hqueueOff r wl hwl v S
    hvalues hwidth hblank hmasters hscratch depth
  have hmasterLen (i : Fin 10) : (M.R (ports i)).length = r.factoryMasters i := by
    rw [hheads,List.length_replicate]
  have hprecision : r.factoryMasters 2 = r.q := r.factoryPrecision_eq
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generateSupplierGeometryWidth_exec (body := body) e he r v₁ M
    (by rw [hP,hmasterLen]; rfl) (by rw [hq,hmasterLen,hprecision])
    (by rw [ht,hmasterLen]; rfl) (by rw [hu,hmasterLen]; rfl)
    (by intro k hk; rw [hframe _ (hgeometryOff k hk)]; exact hgeometryBlank k hk) depth
  let F : Stacks T A := {M with R := Function.update M.R (e 115) (List.replicate r.V Node.tick)}
  refine ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,mn_seq_within_add he₁ he₂,?_,?_,hI,hO,hL,?_⟩
  · intro i
    simp only [F,Function.update_of_ne (hgeometryOff 115 (by simp) i)]
    exact hheads i
  · simp [F]
  · intro k hp hk
    simp only [F,Function.update_of_ne hk]
    exact hframe k hp
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
