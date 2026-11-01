module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateInverseMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Inverse master generation retires its temporary scalar values, preserving
only the exported masters and restoring the complete caller table. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def scalarValueRegs (rg : TblR 25 → Fin T) : List (Fin T) := List.ofFn (fun i => rg (.v i))

def restoredSupplierMasters (rg : TblR 25 → Fin T) (source : Fin 8 → Fin T)
    (ports : Fin 10 → Fin T) (word saved tmp queue carry : Fin T) : Pr P T Q A U :=
  .seq (generateSupplierMasters rg source ports word saved tmp queue carry) (clearWords (scalarValueRegs rg))

theorem restoredInverseMasters_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (source : Fin 8 → Fin T) (ports : Fin 10 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i) (word saved tmp queue carry : Fin T)
    (hregs : ∀ i, [source i,rg .wr,word,saved,tmp,queue].Nodup) (hqueueOff : ∀ r, rg r ≠ queue)
    {B p u l target t a b : ℕ}
    (hst : s < t) (has : a ≤ s) (hbs : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^B)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^B)
    (hvaluesFit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,b] i < 2^B)
    (wl : List (Fin (A+4))) (hwl : wl.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = ![p,u,l,target,s,t,a,b] i)
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ k : TblR 25, k ≠ .wr → S.R (rg k) = [])
    (hmasters : ∀ i, S.R (ports i) = [])
    (hscratch : ∀ i ∈ [word,saved,tmp,queue], S.R i = []) (depth : ℕ) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ generateInverseMastersCost B p u l target s t a b+(50*B+51) ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        ((392*B+396)+3*(inverseScalarAtoms p s t u a b*tblC B 0+
          inverseMasterCopyCost B (inverseMasterValues p u l target s t a b)))) depth
        (restoredSupplierMasters rg source ports word saved tmp queue carry) (Host.mk v S) n (Host.mk v' F) ∧
      (∀ i, F.R (ports i) = List.replicate ((inverseMasterValues p u l target s t a b) i) Node.tick) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ i, ports i ≠ k) → F.R k = S.R k := by
  obtain ⟨v₁,H,n₁,z,hu₁,hn₁,he₁,hh,hkeep,hacc,hfit,hheads,hI,hO,hL,hframe⟩ :=
    generateInverseMasters_exec (body := body) rg hrg source ports hports hsep word saved tmp queue carry
      hregs hqueueOff hst has hbs hband hbandRoom hgeometryRoom hprecisionRoom hvaluesFit wl hwl v S hvalues hwidth hblank hmasters hscratch depth
  have hnd : (scalarValueRegs rg).Nodup := List.nodup_ofFn_ofInjective (by
    intro i j hij
    exact TblR.v.inj (hrg hij))
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) (scalarValueRegs rg) hnd v₁ H
  have hval (i : Fin 25) : H.R (rg (.v i)) = binSyms B (z.val i) := hh (.v i)
  have hcost : 2*((scalarValueRegs rg).map fun k => (H.R k).length).sum+2*(scalarValueRegs rg).length+1 =
      50*B+51 := by
    simp only [scalarValueRegs,List.map_ofFn,Function.comp_def,hval,length_binSyms,
      List.ofFn_const,List.sum_replicate,smul_eq_mul,List.length_ofFn]
    omega
  rw [hcost] at he₂
  have hw₂ := mn_native_exec_within he₂ 0 (clearWords_native _) depth _ (by
    simpa only [Nat.zero_mul,Nat.add_zero] using he₁.final)
  let F : Stacks T A := {H with R := fun k => if k ∈ scalarValueRegs rg then [] else H.R k}
  have hmem (k : Fin T) : k ∈ scalarValueRegs rg ↔ ∃ i, rg (.v i) = k := List.mem_ofFn
  have hportOff (i : Fin 10) : ports i ∉ scalarValueRegs rg := by
    intro hm
    obtain ⟨j,hj⟩ := (hmem _).mp hm
    exact hsep i (.v j) hj
  refine ⟨v₂,F,n₁+(50*B+51),hu₂.trans hu₁,Nat.add_le_add_right hn₁ _,
    ExecWithin.seq he₁ hw₂,?_,hI,hO,hL,?_⟩
  · intro i
    simpa only [F,ite_eq_right (hportOff i)] using hheads i
  · intro k hp
    by_cases ht : ∃ j, rg j = k
    · obtain ⟨j,rfl⟩ := ht
      cases j with
      | v i => simp only [F,ite_eq_left ((hmem _).mpr ⟨i,rfl⟩)]; exact (hblank (.v i) (by simp)).symm
      | wr =>
        have hoff : rg .wr ∉ scalarValueRegs rg := by
          intro hm
          obtain ⟨i,hi⟩ := (hmem _).mp hm
          have := hrg hi
          cases this
        simp only [F,ite_eq_right hoff]
        exact (hh .wr).trans hwidth.symm
      | wn =>
        have hoff : rg .wn ∉ scalarValueRegs rg := by
          intro hm
          obtain ⟨i,hi⟩ := (hmem _).mp hm
          have := hrg hi
          cases this
        simp only [F,ite_eq_right hoff]
        exact (hh .wn).trans (hblank .wn (by simp)).symm
      | acc =>
        have hoff : rg .acc ∉ scalarValueRegs rg := by
          intro hm
          obtain ⟨i,hi⟩ := (hmem _).mp hm
          have := hrg hi
          cases this
        simp only [F,ite_eq_right hoff]
        exact (hh .acc).trans (hacc.trans (hblank .acc (by simp)).symm)
      | z i =>
        have hoff : rg (.z i) ∉ scalarValueRegs rg := by
          intro hm
          obtain ⟨j,hj⟩ := (hmem _).mp hm
          have := hrg hj
          cases this
        simp only [F,ite_eq_right hoff]
        exact (hh (.z i)).trans (hblank (.z i) (by simp)).symm
    · have hoff : k ∉ scalarValueRegs rg := by
        intro hm
        obtain ⟨i,hi⟩ := (hmem _).mp hm
        exact ht ⟨.v i,hi⟩
      simp only [F,ite_eq_right hoff]
      exact hframe k (fun j hj => ht ⟨j,hj⟩) hp
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
