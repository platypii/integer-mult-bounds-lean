module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallUnaryScalarInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedRoundScalars
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverRoundPrecision

/-! Produce the normalization scalar view from the retained kernel-length and precision masters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def installRetainedRoundScalars (rg : TblR 25 → Fin T)
    (header word saved tmp carry pSrc qSrc : Fin T) : Pr P T Q A U :=
  .seq (installUnaryScalarInputs rg header word saved tmp carry [(0,pSrc),(18,qSrc)])
    (.seq (tblCompile rg tblRecoverRoundPrecision) (tblCompile rg tblPrepareRetainedRound))

theorem installRetainedRoundScalars_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (header word saved tmp carry pSrc qSrc : Fin T) (hheader : ∀ r, rg r ≠ header)
    (hregs : ∀ src ∈ [pSrc,qSrc], [src,rg .wr,word,saved,tmp,header].Nodup)
    (B p q : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (hPRoom : 2^15*p < 2^B) (hselectionRoom : 8*(p+2) < 2^B) (hwidthRoom : 2*q+8 < 2^B)
    (v : HS T Q A U) (S : Stacks T A) (hwidth : S.R (rg .wr) = wl)
    (hp : (S.R pSrc).length = 2^15*p) (hq : (S.R qSrc).length = q)
    (hblank : ∀ r : TblR 25, r ≠ .wr → S.R (rg r) = [])
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = []) :
    ∃ v' F m z, v'.user = v.user ∧
      m ≤ binaryHeaderQueueCost S.R B [pSrc,qSrc]+25*(4*B+4)+2*(8*B+8)+2+
        (18+(4*Nat.size (4*p)+31))*tblC B 0 ∧
      Exec body (installRetainedRoundScalars rg header word saved tmp carry pSrc qSrc)
        (mk v S) m (mk v' F) ∧
      tblHolds rg F (tblRho B wl [] z) ∧
      tblHolds (rg ∘ TblR.rename inverseRoundVariables) F
        (tblRho B wl [] (z.restrict inverseRoundVariables)) ∧
      (z.restrict inverseRoundVariables).val = ![2*q+8,q,p,inverseNormalizationShift p,p+8,0,0,0] ∧
      (∀ i, z.val i < 2^B) ∧ z.acc = [] ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ i, (∀ r, rg r ≠ i) → F.R i = S.R i) := by
  obtain ⟨v₁,F₁,m₁,hu₁,hm₁,he₁,hh₁,hin₁,hout₁,hL₁,hframe₁⟩ :=
    installUnaryScalarInputs_exec (body := body) rg hrg header word saved tmp carry hheader
      [(0,pSrc),(18,qSrc)] (by simpa using hregs) B wl hwl v S hwidth hblank hwork
  let st : TblSt 25 A := loadedBinaryState [(0,2^15*p),(18,q)] ⟨fun _ => 0,[]⟩
  have hh : tblHolds rg F₁ (tblRho B wl [] st) := by
    simpa only [List.map_cons,List.map_nil,hp,hq] using hh₁
  have hfit : ∀ i, st.val i < 2^B := by
    intro i
    by_cases h0 : i = 0 <;> by_cases h18 : i = 18 <;>
      simp [st,loadedBinaryState,h0,h18] <;> omega
  have hc := tblRecoverRoundPrecision_do (e := 0) (p := p) st
    (by simp [st,loadedBinaryState]) (by omega) hfit
  obtain ⟨zR,⟨hpR,hqR,haccR,hfitR⟩,hrun⟩ :=
    hc.host (body := body) hrg wl [] hwl rfl (Nat.zero_le B) hfit
  obtain ⟨vR,FR,mR,huR,hmR,heR,hhR,hinR,houtR,hLR,hframeR⟩ := hrun v₁ F₁ hh
  have hqR' : zR.val 18 = q := by simpa [st,loadedBinaryState] using hqR
  obtain ⟨v₂,F₂,m₂,z,hu₂,hm₂,he₂,hh₂,hview,hval,hkeep,hacc,hfitZ,hin₂,hout₂,hL₂,hframe₂⟩ :=
    prepareRetainedRoundScalars_exec (body := body) rg hrg wl hwl zR hpR hqR'
      hselectionRoom hwidthRoom hfitR vR FR hhR
  refine ⟨v₂,F₂,m₁+(mR+m₂),z,hu₂.trans (huR.trans hu₁),?_,Exec.seq he₁ (Exec.seq heR he₂),hh₂,hview,hval,hfitZ,by simpa [st,loadedBinaryState] using hacc.trans haccR,
    hin₂.trans (hinR.trans hin₁),hout₂.trans (houtR.trans hout₁),hL₂.trans (hLR.trans hL₁),?_⟩
  · simp only [List.map_cons,List.map_nil,List.length_cons,List.length_nil] at hm₁
    simp only [List.length_nil] at hmR
    rw [Nat.add_mul]
    omega
  · intro i hoff
    exact (hframe₂ i hoff).trans ((hframeR i hoff).trans (hframe₁ i hoff))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
