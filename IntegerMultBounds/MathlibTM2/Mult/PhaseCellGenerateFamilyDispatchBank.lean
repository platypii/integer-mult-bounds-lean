module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateInverseScalarBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairBitPlanes

/-! Assemble a complete family-dispatch bank from ordinary scalar headers,
a retained ambient source and a retained replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def generateFamilyDispatchBank (work : Fin 303 → Fin T) (source : Fin 8 → Fin T)
    (word saved tmp queue carry ambient count : Fin T) : Pr P T Q A U :=
  .seq (generateInverseScalarBank (work ∘ familyInverseScalarReg) source word saved tmp queue carry)
    (.seq (copyMappedWords ambient (work 110) tmp saved id) (ucopy count (work (familyInverseCoreReg 246)) saved))

theorem generateFamilyDispatchBank_exec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (source : Fin 8 → Fin T) (word saved tmp queue carry ambient count : Fin T)
    (hparams : ∀ i, [source i,work (familyInverseScalarReg .wr),word,saved,tmp,queue].Nodup)
    (hcopy : [ambient,work 110,tmp,saved].Nodup)
    (hcount : [count,work (familyInverseCoreReg 246),saved].Nodup)
    (hambientOff : ∀ i, ambient ≠ work i) (hcountOff : ∀ i, count ≠ work i)
    (hscratchOff : ∀ i ∈ [word,saved,tmp,queue], ∀ j, i ≠ work j)
    (p u l target s t a b B N : ℕ) (hfit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,b] i < 2^B)
    (wl xs : List (Fin (A+4))) (hwl : wl.length = B) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = ![p,u,l,target,s,t,a,b] i)
    (hwidth : S.R (work (familyInverseScalarReg .wr)) = wl)
    (hblank : ∀ i, i ≠ familyInverseScalarReg .wr → S.R (work i) = [])
    (hleft : ∀ i, S.L (work i) = [])
    (hscratch : ∀ i ∈ [word,saved,tmp,queue], S.R i = [])
    (hambient : S.R ambient = xs) (hN : (S.R count).length = N) (depth : ℕ) :
    ∃ v' n F, v'.user = v.user ∧
      n ≤ ((p+u+l+target+s+t+a+b)*(4*B+10)+228*B+263)+(6*xs.length+6)+(4*N+4) ∧
      embStk work F = familyDispatchBank (embStk work S) B wl (inverseInputScalars p u l target s t a b) N xs ∧
      (∀ i, (∀ j, i ≠ work j) → F.R i = S.R i) ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        ((392*B+396)+(2*(6*xs.length+6)+2*(4*N+4)))) depth
        (generateFamilyDispatchBank work source word saved tmp queue carry ambient count) (mk v S) n (mk v' F) := by
  let rg := work ∘ familyInverseScalarReg
  have hrg : Function.Injective rg := hwork.comp familyInverseScalarReg_injective
  have hcoreOff (i : Fin 263) (r : TblR 25) : rg r ≠ work (familyInverseCoreReg i) :=
    fun he => familyInverseScalarReg_core r i (hwork he)
  obtain ⟨v₁,n₁,H,hu₁,hn₁,hscalar,hfr,he₁⟩ := generateInverseScalarBank_exec (body := body)
    rg hrg source word saved tmp queue carry hparams (fun r => (hscratchOff queue (by simp) _).symm)
    p u l target s t a b B hfit wl hwl v S hvalues hwidth
    (by intro r hr; exact hblank _ (familyInverseScalarReg_injective.ne hr)) hscratch depth
  obtain ⟨hI,hO,hL,hframe⟩ := hfr
  have hcoreBlank (i : Fin 263) : H.R (work (familyInverseCoreReg i)) = [] := by
    rw [hframe _ (hcoreOff i)]
    exact hblank _ (familyInverseScalarReg_core .wr i).symm
  have h110 : familyInverseCoreReg 110 = 110 := by decide
  have hs : H.R (work 110) = [] := by simpa only [h110] using hcoreBlank 110
  have hborrow (i : Fin T) (hi : ∀ j, i ≠ work j) : H.R i = S.R i :=
    hframe i (fun r => (hi _).symm)
  obtain ⟨v₂,hu₂,he₂⟩ := copyMappedWords_exec (body := body) ambient (work 110) tmp saved hcopy id v₁ H
    (by rw [hborrow tmp (hscratchOff tmp (by simp))]; exact hscratch tmp (by simp))
    (by rw [hborrow saved (hscratchOff saved (by simp))]; exact hscratch saved (by simp))
  rw [hborrow ambient hambientOff,hambient,List.map_id,hs,List.append_nil] at he₂
  let H₂ : Stacks T A := {H with R := Function.update H.R (work 110) xs}
  have hcountSource : H₂.R count = S.R count := by
    rw [show H₂.R count = H.R count from Function.update_of_ne (hcountOff 110) _ _,hborrow count hcountOff]
  have hc110 : familyInverseCoreReg 246 ≠ (110 : Fin 303) := by decide
  have hcountBlank : H₂.R (work (familyInverseCoreReg 246)) = [] := by
    rw [show H₂.R (work (familyInverseCoreReg 246)) = H.R (work (familyInverseCoreReg 246)) from
      Function.update_of_ne (hwork.ne hc110) _ _,hcoreBlank]
  have hr := hcount
  regs_ne hr
  obtain ⟨v₃,hu₃,he₃⟩ := ucopy_exec (body := body) (a := count) (b := work (familyInverseCoreReg 246)) (t := saved)
    ‹count ≠ work (familyInverseCoreReg 246)› ‹count ≠ saved› ‹work (familyInverseCoreReg 246) ≠ saved› v₂ H₂ (by
      change Function.update H.R (work 110) xs saved = []
      rw [Function.update_of_ne (hscratchOff saved (by simp) 110),hborrow saved (hscratchOff saved (by simp))]
      exact hscratch saved (by simp))
  rw [hcountSource,hN,hcountBlank,List.append_nil] at he₃
  let F : Stacks T A := {H₂ with R := Function.update H₂.R (work (familyInverseCoreReg 246)) (List.replicate N tick)}
  have hscalarF : tblHolds rg F (tblRho B wl [] (inverseInputScalars p u l target s t a b)) := by
    intro r
    change Function.update (Function.update H.R (work 110) xs) (work (familyInverseCoreReg 246)) _ (rg r) = _
    rw [Function.update_of_ne (hcoreOff 246 r),
      Function.update_of_ne (by simpa only [h110] using hcoreOff 110 r)]
    exact hscalar r
  have hcoreF (i : Fin 263) : F.R (work (familyInverseCoreReg i)) =
      if i = 246 then List.replicate N tick else if i = 110 then xs else [] := by
    by_cases hc : i = 246
    · subst i; simp [F]
    by_cases hs : i = 110
    · subst i; simp [F,H₂,h110,hwork.ne (by decide : (110 : Fin 303) ≠ familyInverseCoreReg 246)]
    change Function.update (Function.update H.R (work 110) xs) (work (familyInverseCoreReg 246)) _
      (work (familyInverseCoreReg i)) = _
    rw [Function.update_of_ne (hwork.ne (familyInverseCoreReg_injective.ne hc)),
      Function.update_of_ne (hwork.ne (by simpa only [← h110] using familyInverseCoreReg_injective.ne hs)),hcoreBlank]
    simp only [hc,hs,ite_false]
  have hw₂ := mn_native_exec_within he₂ 2 (by
    simp [copyMappedWords,copyR,copyStep,moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]) depth _ (le_refl _)
  have hw₃ := mn_native_exec_within he₃ 2 (by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,whileR,moveStep,peekR,
      mnNativePushBound,mnActPush]) depth _ (le_refl _)
  have hwhole := mn_seq_within_add he₁ (mn_seq_within_add hw₂ hw₃)
  refine ⟨v₃,n₁+((6*xs.length+6)+(4*N+4)),F,hu₃.trans (hu₂.trans hu₁),?_,?_,?_,hI,hO,hL,hwhole⟩
  · simpa only [Nat.add_assoc] using Nat.add_le_add_right hn₁ ((6*xs.length+6)+(4*N+4))
  · refine Stacks.ext hI hO ?_ ?_
    · funext i; change H.L (work i) = []; rw [hL]; exact hleft i
    · funext i
      rcases familyInverseCallerReg_cover i with ⟨j,rfl⟩ | ⟨r,rfl⟩
      · exact (hcoreF j).trans (familyDispatchBank_core _ B wl _ N xs j).symm
      · exact (hscalarF r).trans (familyDispatchBank_scalars _ B wl _ N xs r).symm
  · intro i hi
    change Function.update (Function.update H.R (work 110) xs) (work (familyInverseCoreReg 246)) _ i = _
    rw [Function.update_of_ne (hi _),Function.update_of_ne (hi 110)]
    exact hborrow i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
