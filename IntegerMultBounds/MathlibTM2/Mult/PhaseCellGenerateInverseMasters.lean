module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateInverseScalarBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallInverseHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseInputScalarFits
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopiesStock
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush

/-! Generate inverse master headers from eight ordinary parameters. The theorem
is independent of publication jobs and is reused by raw recovery suppliers. -/
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

def generateSupplierMasters (rg : TblR 25 → Fin T) (source : Fin 8 → Fin T)
    (ports : Fin 10 → Fin T) (word saved tmp queue carry : Fin T) : Pr P T Q A U :=
  .seq (generateInverseScalarBank rg source word saved tmp queue carry) (installInverseHeaders rg ports)

theorem installInverseHeaders_native (rg : TblR 25 → Fin T) (ports : Fin 10 → Fin T) :
    mnNativePushBound 3 (installInverseHeaders (P := P) (Q := Q) (A := A) (U := U) rg ports) :=
  ⟨tblCompile_native _ _,tblUnaryCopies_native _ _⟩

noncomputable def generateInverseMastersCost (B p u l target s t a b : ℕ) [NeZero s] : ℕ :=
  ((p+u+l+target+s+t+a+b)*(4*B+10)+228*B+263)+
    (inverseScalarAtoms p s t u a b*tblC B 0+
      inverseMasterCopyCost B (inverseMasterValues p u l target s t a b))

theorem generateInverseMasters_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
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
    ∃ v' F n z, v'.user = v.user ∧ n ≤ generateInverseMastersCost B p u l target s t a b ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        ((392*B+396)+3*(inverseScalarAtoms p s t u a b*tblC B 0+
          inverseMasterCopyCost B (inverseMasterValues p u l target s t a b)))) depth
        (generateSupplierMasters rg source ports word saved tmp queue carry) (Host.mk v S) n (Host.mk v' F) ∧
      tblHolds rg F (tblRho B wl [] z) ∧
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ =
        (inverseInputScalars (A := A) p u l target s t a b).val ⟨i.val,by omega⟩) ∧
      z.acc = [] ∧ (∀ i, z.val i < 2^B) ∧
      (∀ i, F.R (ports i) = List.replicate ((inverseMasterValues p u l target s t a b) i) Node.tick) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ j, rg j ≠ k) → (∀ i, ports i ≠ k) → F.R k = S.R k := by
  obtain ⟨v₁,n₁,H,hu₁,hn₁,hh₁,hfr₁,he₁⟩ := generateInverseScalarBank_exec (body := body)
    rg hrg source word saved tmp queue carry hregs hqueueOff
    p u l target s t a b B hvaluesFit wl hwl v S hvalues hwidth hblank hscratch depth
  have hHports (i : Fin 10) : H.R (ports i) = [] := (hfr₁.2.2.2 _ (hsep i)).trans (hmasters i)
  have hfit := inverseInputScalars_fit (A := A) hst has hbs
    hbandRoom hgeometryRoom hprecisionRoom
  obtain ⟨v₂,F,n₂,z,hu₂,hn₂,he₂,hh₂,hkeep,hacc,hfit₂,hI,hO,hL,hheads,hframe⟩ :=
    installInverseHeaders_exec (body := body) (p := p) (u := u) (l := l) (target := target)
      (s := s) (t := t) (a := a) (b := b) rg hrg ports hports hsep wl hwl
      (inverseInputScalars p u l target s t a b)
      rfl rfl rfl rfl rfl rfl rfl rfl hst has hbs hband
      hbandRoom hgeometryRoom hprecisionRoom hfit v₁ H hh₁
  have hw₂ := mn_native_exec_within he₂ 3 (installInverseHeaders_native _ _) depth
    (mnSize (Host.mk v₁ H)+depth+3*(inverseScalarAtoms p s t u a b*tblC B 0+
      inverseMasterCopyCost B (inverseMasterValues p u l target s t a b))) (by omega)
  refine ⟨v₂,F,n₁+n₂,z,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,mn_seq_within_add he₁ hw₂,hh₂,hkeep,hacc,hfit₂,?_,
    hI.trans hfr₁.1,hO.trans hfr₁.2.1,hL.trans hfr₁.2.2.1,?_⟩
  · intro i
    simpa only [hHports,List.append_nil] using hheads i
  · intro k hk hp
    exact (hframe k hk hp).trans (hfr₁.2.2.2 k hk)
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
