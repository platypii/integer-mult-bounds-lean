module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComponentSolutions

/-! Generate core dimensions, assemble native scalar output, and release owned controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def finishComponentBatch (coreWord precision rows width hold replicas nativeCount count src buf saved tmp : Fin T) : Pr P T Q A U :=
  .seq (preparePackedCoreRows coreWord precision rows width buf saved tmp)
    (.seq (packedComplexBatchFinish hold replicas nativeCount width count src buf saved tmp)
      (releasePackedCoreRows rows width))

/-- Consume the native scalar certificate directly. Row dimensions are computed
from the retained binary core length; pairing restores the original replica
symbols and all owned dimensions and counters return to blank storage. -/
theorem finishComponentBatch_exec
    {coreWord precision rows width hold replicas nativeCount count src buf saved tmp : Fin T}
    (hreg : [coreWord,precision,rows,width,hold,replicas,nativeCount,count,src,buf,saved,tmp].Nodup)
    (hA : 4 ≤ A) {s : ℕ} [NeZero s] (B q d a L : ℕ) (hL : L < 2^B)
    (active : Finset (ZMod s)) (hfit : a+L ≤ s)
    (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (Fs : List (ZMod s → GaussianInt)) (y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (Ds : List (ZMod s → GaussianInt)) (e : ℝ)
    (scalarTail tail original : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun (x : (ZMod s → GaussianInt) × (ZMod s → ℝ)) D =>
      PhaseCellInterface.ErrorOn active
        (fun i => (packedIntervalRead q (2*q+8) a
          (cstream A (2*q+8) (packedInterval a L D)++scalarTail) i).re) x.2 e)
      ((complexComponentFields Fs).map (fun F => ((fun i => (2 : GaussianInt)^d*F i),y F))) Ds)
    (v : HS T Q A U) (S : Stacks T A)
    (hword : S.R coreWord = binSyms B L) (hq : (S.R precision).length = q)
    (hhold : (S.R hold).length = Fs.length)
    (hreplicas : S.R replicas = List.replicate Fs.length tick++original)
    (hnative : (S.R nativeCount).length = 2*Fs.length)
    (hsrc : S.R src = (Ds.map (fun D => cstream A (2*q+8) (packedInterval a L D))).flatten++tail)
    (hblank : ∀ i ∈ [rows,width,count,buf,saved,tmp], S.R i = []) :
    let Gs := pairedComponentFields (Ds.take Fs.length) (Ds.drop Fs.length)
    Gs.length = Fs.length ∧
    ∃ v' n, v'.user = v.user ∧
      n ≤ preparePackedCoreRowsCost B q L+Fs.length*(16*(L*(2*q+8))+19)+22+
        (2*L*((2*q+8)+1)+4) ∧
      Exec body (finishComponentBatch coreWord precision rows width hold replicas nativeCount count src buf saved tmp)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update (Function.update
          (Function.update S.R src ((Gs.map (fun D => cstream A (2*q+8) (packedInterval a L D))).flatten++tail))
            replicas original) nativeCount []) hold [])}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead q (2*q+8) a (cstream A (2*q+8) (packedInterval a L D)++tail)) z (e+e))
        (Fs.map (componentSolution y)) Gs := by
  have hr := hreg
  regs_ne hr
  let Zs := Fs.map (componentSolution y)
  have hc := packedComponentSolutions_certificate q (2*q+8) d a L active Fs y Ds e scalarTail hgood
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := preparePackedCoreRows_exec (body := body)
    (show [coreWord,precision,rows,width,buf,saved,tmp].Nodup by regs_nodup)
    B q L hL v S hword hq (by intro i hi; exact hblank i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R rows
    (List.replicate L tick)) width (List.replicate (L*(2*q+8)) tick))}
  obtain ⟨hlen,v₂,n₂,hu₂,hn₂,he₂,haccuracy⟩ := packedComplexBatchFinish_exec (body := body)
    (show [hold,replicas,nativeCount,width,count,src,buf,saved,tmp].Nodup by regs_nodup)
    hA q (2*q+8) a L active hfit hactive Zs Ds e scalarTail tail original hc v₁ S₁
    (by simpa [S₁,Zs,‹rows ≠ hold›.symm,‹width ≠ hold›.symm] using hhold)
    (by simp [S₁])
    (by simpa [S₁,Zs,‹rows ≠ replicas›.symm,‹width ≠ replicas›.symm] using hreplicas)
    (by simpa [S₁,Zs,‹rows ≠ nativeCount›.symm,‹width ≠ nativeCount›.symm] using hnative)
    (by simpa [S₁,‹rows ≠ src›.symm,‹width ≠ src›.symm] using hsrc)
    (by simpa [S₁,‹rows ≠ count›.symm,‹width ≠ count›.symm] using hblank count (by simp))
    (by simpa [S₁,‹rows ≠ buf›.symm,‹width ≠ buf›.symm] using hblank buf (by simp))
    (by simpa [S₁,‹rows ≠ saved›.symm,‹width ≠ saved›.symm] using hblank saved (by simp))
    (by simpa [S₁,‹rows ≠ tmp›.symm,‹width ≠ tmp›.symm] using hblank tmp (by simp))
  let Gs := pairedComponentFields (Ds.take Fs.length) (Ds.drop Fs.length)
  let S₂ : Stacks T A := {S₁ with R := (Function.update (Function.update (Function.update
    (Function.update S₁.R src ((Gs.map (fun D => cstream A (2*q+8) (packedInterval a L D))).flatten++tail))
      replicas original) nativeCount []) hold [])}
  have he₂' : Exec body (packedComplexBatchFinish hold replicas nativeCount width count src buf saved tmp)
      (mk v₁ S₁) n₂ (mk v₂ S₂) := by simpa only [Zs,List.length_map] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := releasePackedCoreRows_exec (body := body) ‹rows ≠ width› L (2*q+8) v₂ S₂
    (by simp [S₂,S₁,‹rows ≠ width›,‹rows ≠ hold›,‹rows ≠ nativeCount›,‹rows ≠ replicas›,‹rows ≠ src›])
    (by simp [S₂,S₁,‹width ≠ hold›,‹width ≠ nativeCount›,‹width ≠ replicas›,‹width ≠ src›])
  refine ⟨by simpa only [Zs,List.length_map] using hlen,v₃,n₁+n₂+(2*L*((2*q+8)+1)+4),
    hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ (Exec.seq he₂' he₃)).cast (by omega) ?_,?_⟩
  · dsimp only [Zs] at hn₂
    simp only [List.length_map] at hn₂
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hr : i = rows
    · subst i; simp [S₂,S₁, *]
    by_cases hw : i = width
    · subst i; simp [S₂,S₁, *, Ne.symm]
    · simp [S₂,S₁,Gs,Function.update_apply,hr,hw]
  · simpa only [Zs,List.length_map] using haccuracy

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
