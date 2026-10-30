module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairPackedBatches

/-! Assemble the actual ordered real solver certificate and its physical output. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def complexComponentTargets {s : ℕ} (Zs : List (ZMod s → ℂ)) : List (ZMod s → ℝ) :=
  Zs.map (fun z i => (z i).re)++Zs.map (fun z i => (z i).im)

@[simp] theorem complexComponentTargets_length {s : ℕ} (Zs : List (ZMod s → ℂ)) :
    (complexComponentTargets Zs).length = 2*Zs.length := by
  simp [complexComponentTargets,two_mul]

/-- Split the one ordered scalar certificate at the original replica count.
The complex result refers to the same two halves used by executed pairing. -/
theorem packedBatchHalves_accuracy {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (q w a L : ℕ) (active : Finset (ZMod s)) (hfit : a+L ≤ s)
    (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt))
    (e : ℝ) (scalarTail tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun y D => PhaseCellInterface.ErrorOn active
      (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a L D)++scalarTail) i).re)
      y e) (complexComponentTargets Zs) Ds) :
    List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w a (cstream A w (packedInterval a L D)++tail)) z (e+e))
      Zs (pairedComponentFields (Ds.take Zs.length) (Ds.drop Zs.length)) := by
  have hx := List.forall₂_take Zs.length hgood
  have hy := List.forall₂_drop Zs.length hgood
  simp only [complexComponentTargets,List.take_append,List.length_map,← List.map_take,List.take_length,
    Nat.sub_self,List.take_zero,List.map_nil,List.append_nil,List.forall₂_map_left_iff] at hx
  simp only [complexComponentTargets,List.drop_append,List.length_map,← List.map_drop,List.drop_length,
    Nat.sub_self,List.drop_zero,List.map_nil,List.nil_append,List.forall₂_map_left_iff] at hy
  exact pairedComponentFields_accuracy hA q w a L active hfit hactive Zs _ _ e e
    scalarTail scalarTail tail hx hy

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- From a single real batch's physical output and scalar certificate, execute
pairing and prove complex accuracy of the returned packets. No separate halves,
integer fits, transformed output, or complex accuracy witness is supplied. -/
theorem packedComplexBatchAssembly_exec {replicas width count src buf saved tmp : Fin T}
    (hreg : [replicas,width,count,src,buf,saved,tmp].Nodup) (hA : 4 ≤ A)
    {s : ℕ} [NeZero s] (q w a L : ℕ) (active : Finset (ZMod s)) (hfit : a+L ≤ s)
    (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt))
    (e : ℝ) (scalarTail tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun y D => PhaseCellInterface.ErrorOn active
      (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a L D)++scalarTail) i).re)
      y e) (complexComponentTargets Zs) Ds)
    (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = Zs.length) (hwidth : (S.R width).length = L*w)
    (hsrc : S.R src = (Ds.map (fun D => cstream A w (packedInterval a L D))).flatten++tail)
    (hcount : S.R count = []) (hbuf : S.R buf = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    let Gs := pairedComponentFields (Ds.take Zs.length) (Ds.drop Zs.length)
    Gs.length = Zs.length ∧
    ∃ v' n, v'.user = v.user ∧ n ≤ Zs.length*(16*(L*w)+9)+14 ∧
      Exec body (pairComplexKey replicas width count src buf saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          ((Gs.map (fun D => cstream A w (packedInterval a L D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead q w a (cstream A w (packedInterval a L D)++tail)) z (e+e)) Zs Gs := by
  have hDs : Ds.length = 2*Zs.length := by simpa only [complexComponentTargets_length] using hgood.length_eq.symm
  obtain ⟨hlen,v',n,hu,hn,he⟩ := pairPackedBatchHalves_exec (body := body) hreg hA a L w Zs.length hfit
    Ds hDs tail v S hreplicas hwidth hsrc hcount hbuf hsaved htmp
  exact ⟨hlen,v',n,hu,hn,he,packedBatchHalves_accuracy hA q w a L active hfit hactive Zs Ds e scalarTail tail hgood⟩

def packedComplexBatchFinish (hold replicas nativeCount width count src buf saved tmp : Fin T) : Pr P T Q A U :=
  .seq (pairComplexKey hold width count src buf saved tmp) (releaseComplexCounts hold replicas nativeCount tmp)

/-- Assemble the complex output and restore the replica header in one actual
execution. All other stacks except the two owned counters are preserved. -/
theorem packedComplexBatchFinish_exec {hold replicas nativeCount width count src buf saved tmp : Fin T}
    (hreg : [hold,replicas,nativeCount,width,count,src,buf,saved,tmp].Nodup) (hA : 4 ≤ A)
    {s : ℕ} [NeZero s] (q w a L : ℕ) (active : Finset (ZMod s)) (hfit : a+L ≤ s)
    (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt))
    (e : ℝ) (scalarTail tail original : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun y D => PhaseCellInterface.ErrorOn active
      (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a L D)++scalarTail) i).re)
      y e) (complexComponentTargets Zs) Ds)
    (v : HS T Q A U) (S : Stacks T A)
    (hhold : (S.R hold).length = Zs.length) (hwidth : (S.R width).length = L*w)
    (hreplicas : S.R replicas = List.replicate Zs.length tick++original)
    (hnative : (S.R nativeCount).length = 2*Zs.length)
    (hsrc : S.R src = (Ds.map (fun D => cstream A w (packedInterval a L D))).flatten++tail)
    (hcount : S.R count = []) (hbuf : S.R buf = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    let Gs := pairedComponentFields (Ds.take Zs.length) (Ds.drop Zs.length)
    Gs.length = Zs.length ∧
    ∃ v' n, v'.user = v.user ∧ n ≤ Zs.length*(16*(L*w)+19)+22 ∧
      Exec body (packedComplexBatchFinish hold replicas nativeCount width count src buf saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R src
          ((Gs.map (fun D => cstream A w (packedInterval a L D))).flatten++tail)) replicas original)
            nativeCount []) hold [])}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead q w a (cstream A w (packedInterval a L D)++tail)) z (e+e)) Zs Gs := by
  have hr := hreg
  regs_ne hr
  obtain ⟨hlen,v₁,n₁,hu₁,hn₁,he₁,haccuracy⟩ := packedComplexBatchAssembly_exec (body := body)
    (show [hold,width,count,src,buf,saved,tmp].Nodup by regs_nodup) hA q w a L active hfit hactive Zs Ds
    e scalarTail tail hgood v S hhold hwidth hsrc hcount hbuf hsaved htmp
  let Gs := pairedComponentFields (Ds.take Zs.length) (Ds.drop Zs.length)
  let S₁ : Stacks T A := {S with R := (Function.update S.R src
    ((Gs.map (fun D => cstream A w (packedInterval a L D))).flatten++tail))}
  obtain ⟨v₂,hu₂,he₂⟩ := releaseComplexCounts_exec (body := body)
    (show [hold,replicas,nativeCount,tmp].Nodup by regs_nodup) Zs.length original v₁ S₁
    (by simpa [S₁,‹hold ≠ src›] using hhold)
    (by simpa [S₁,‹replicas ≠ src›] using hreplicas)
    (by simpa [S₁,‹nativeCount ≠ src›] using hnative)
    (by simpa [S₁,‹src ≠ tmp›.symm] using htmp)
  refine ⟨hlen,v₂,n₁+(10*Zs.length+8),hu₂.trans hu₁,?_,Exec.seq he₁ he₂,haccuracy⟩
  have hc : Zs.length*(16*(L*w)+19) = Zs.length*(16*(L*w)+9)+10*Zs.length := by ring
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
