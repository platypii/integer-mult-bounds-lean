module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateInverseParameters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedDescriptorWords
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Generate the outer normalization frame around an existing numerical bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

private theorem normalizedInput_updates (M : Stacks 276 A) (B L : ℕ)
    (wl parameters : List (Fin (A+4))) :
    packedNormalizedInputBank M B L wl parameters =
      let E := extendStacks (by decide : 276 ≤ 325) M
      {E with R := (Function.update (Function.update (Function.update E.R
        (packedNormalizedScalarReg .wr) wl) 277 (binSyms B L)) 324 parameters)} := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    simp only [packedNormalizedInputBank,complexBatchInputBank,extendStacks]
    split_ifs <;> first | rfl | omega
  · funext i
    have hwr := (packedNormalizedScalarReg_bounds .wr).1
    by_cases h324 : i = 324
    · subst i; simp [packedNormalizedInputBank]
    by_cases h277 : i = 277
    · subst i
      have hn : (277 : Fin 325) ≠ packedNormalizedScalarReg .wr := by
        intro he; have := congrArg Fin.val he; omega
      simp [packedNormalizedInputBank,complexBatchInputBank,extendStacks,hn]
    by_cases hw : i = packedNormalizedScalarReg .wr
    · subst i
      have hn : packedNormalizedScalarReg .wr ≠ (277 : Fin 325) := by
        intro he; have := congrArg Fin.val he; omega
      simp [packedNormalizedInputBank,packedNormalizedScalarReg_header,hn]
    have h277' : ∀ (hi : i.val < 280), (⟨i.val,hi⟩ : Fin 280) ≠ 277 := by
      intro hi he; apply h277; exact Fin.ext (congrArg (fun x : Fin 280 => x.val) he)
    simp only [packedNormalizedInputBank,Function.update_of_ne h324,Function.update_of_ne hw,
      Function.update_of_ne h277,complexBatchInputBank,extendStacks]
    split_ifs <;> simp_all <;> omega

def generateNormalizedFrame (work : Fin 325 → Fin T) (source : Fin 8 → Fin T)
    (width core word saved tmp carry : Fin T) : Pr P T Q A U :=
  .seq (ucopy width (work (packedNormalizedScalarReg .wr)) saved)
    (.seq (toBinary core width (work 277) saved tmp carry)
      (generateInverseParameters source width word saved tmp (work 324) carry))


theorem generateNormalizedFrame_exec (work : Fin 325 → Fin T) (hwork : Function.Injective work)
    (source : Fin 8 → Fin T) (width core word saved tmp carry : Fin T)
    (hborrow : ∀ i ∈ width::core::word::saved::tmp::List.ofFn source, ∀ j, i ≠ work j)
    (hcore : [core,width,work 277,saved,tmp].Nodup)
    (hparams : ∀ i, [source i,width,word,saved,tmp,work 324].Nodup)
    (p u l target s t a b B L : ℕ) (v : HS T Q A U) (S : Stacks T A) (M : Stacks 276 A)
    (hview : embStk work S = extendStacks (by decide : 276 ≤ 325) M)
    (hvalues : ∀ i, (S.R (source i)).length = ![p,u,l,target,s,t,a,b] i)
    (hwidth : (S.R width).length = B) (hlen : (S.R core).length = L)
    (hblank : ∀ i ∈ [word,saved,tmp], S.R i = []) (depth : ℕ) :
    let parameters := (inverseParameterWords p u l target s t a b).flatMap (fun r => binSyms B r.2)
    let F := {S with R := (Function.update (Function.update (Function.update S.R
      (work (packedNormalizedScalarReg .wr)) (List.replicate B tick)) (work 277) (binSyms B L))
      (work 324) parameters)}
    ∃ v' n, v'.user = v.user ∧
      n ≤ (L+p+u+l+target+s+t+a+b)*(4*B+10)+72*B+109 ∧
      embStk work F = packedNormalizedInputBank M B L (List.replicate B tick) parameters ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+10*(2*(4*B+4))) depth
        (generateNormalizedFrame work source width core word saved tmp carry) (mk v S) n (mk v' F) := by
  dsimp only
  have hr := hcore
  regs_ne hr
  have hoff (i : Fin T) (hi : i ∈ width::core::word::saved::tmp::List.ofFn source) (j : Fin 325) :
      i ≠ work j := hborrow i hi j
  have hfresh (i : Fin 325) (hi : 276 ≤ i.val) : S.R (work i) = [] := by
    have h := congrArg (fun C : Stacks 325 A => C.R i) hview
    exact h.trans (extendStacks_fresh (by decide : 276 ≤ 325) M i hi).2
  have hwr : S.R (work (packedNormalizedScalarReg .wr)) = [] :=
    hfresh _ (by have := (packedNormalizedScalarReg_bounds .wr).1; omega)
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := width) (b := work (packedNormalizedScalarReg .wr))
    (t := saved) (hoff width (by simp) _) ‹width ≠ saved›
    (hoff saved (by simp) _).symm v S (hblank saved (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R (work (packedNormalizedScalarReg .wr)) (List.replicate B tick)}
  have he₁' : Exec body (ucopy width (work (packedNormalizedScalarReg .wr)) saved)
      (mk v S) (4*B+4) (mk v₁ S₁) := by
    simpa only [hwidth,hwr,List.append_nil,S₁] using he₁
  have hframe₁ (i : Fin T) (hi : i ∈ width::core::word::saved::tmp::List.ofFn source) : S₁.R i = S.R i :=
    Function.update_of_ne (hoff i hi _) _ _
  have h277 : (277 : Fin 325) ≠ packedNormalizedScalarReg .wr := by
    intro he; have := congrArg Fin.val he
    have := (packedNormalizedScalarReg_bounds .wr).1
    omega
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := toBinary_exec_within (body := body)
    (u := core) (wR := width) (c := work 277) (saved := saved) (tmp := tmp) hcore carry v₁ S₁
    (by simp [S₁,hwork.ne h277,hfresh 277 (by decide)])
    (by rw [hframe₁ saved (by simp)]; exact hblank saved (by simp))
    (by rw [hframe₁ tmp (by simp)]; exact hblank tmp (by simp)) depth
  rw [hframe₁ width (by simp),hframe₁ core (by simp),hwidth,hlen] at hn₂ he₂
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R (work 277) (binSyms B L)}
  have hframe₂ (i : Fin T) (hi : i ∈ width::core::word::saved::tmp::List.ofFn source) : S₂.R i = S.R i := by
    rw [show S₂.R i = S₁.R i from Function.update_of_ne (hoff i hi _) _ _,hframe₁ i hi]
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := generateInverseParameters_exec (body := body)
    source width word saved tmp (work 324) carry hparams p u l target s t a b B v₂ S₂
    (by
      intro i
      have hs : source i ∈ List.ofFn source := List.mem_ofFn.mpr ⟨i,rfl⟩
      rw [hframe₂ (source i) (List.mem_append_right [width,core,word,saved,tmp] hs)]
      exact hvalues i)
    (by rw [hframe₂ width (by simp)]; exact hwidth)
    (by
      intro i hi
      have hi' := List.mem_cons_of_mem width (List.mem_cons_of_mem core (List.mem_append_left (List.ofFn source) hi))
      rw [hframe₂ i hi']
      exact hblank i hi) depth
  have h324 : S₂.R (work 324) = [] := by
    have hn : (324 : Fin 325) ≠ packedNormalizedScalarReg .wr := (packedNormalizedScalarReg_header .wr).symm
    simp [S₂,S₁,hwork.ne hn,hwork.ne (by decide : (324 : Fin 325) ≠ 277),hfresh 324 (by decide)]
  rw [h324,List.append_nil] at he₃
  have hw₁ := mn_native_exec_within he₁' 2 (by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,whileR,moveStep,peekR,
      mnNativePushBound,mnActPush]) depth _ (le_refl _)
  have hwhole := mn_seq_within_add hw₁ (mn_seq_within_add he₂ he₃)
  refine ⟨v₃,(4*B+4)+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),by nlinarith only [hn₂,hn₃],?_,hwhole.mono ?_⟩
  · change embStk work {S₂ with R := (Function.update S₂.R (work 324)
        ((inverseParameterWords p u l target s t a b).flatMap (fun r => binSyms B r.2)))} = _
    rw [embStk_updateR hwork]
    have h₂ : embStk work S₂ = {embStk work S₁ with R :=
        (Function.update (embStk work S₁).R 277 (binSyms B L))} := embStk_updateR hwork S₁ 277 _
    have h₁ : embStk work S₁ = {embStk work S with R :=
        (Function.update (embStk work S).R (packedNormalizedScalarReg .wr) (List.replicate B tick))} :=
      embStk_updateR hwork S _ _
    rw [h₂,h₁,hview]
    exact (normalizedInput_updates M B L _ _).symm
  · intro d z hz
    convert hz using 1 <;> ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
