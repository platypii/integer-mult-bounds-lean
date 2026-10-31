module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedProducerDescriptorRelease

/-! A packed producer call owns its descriptor lifecycle. Preparation derives
readiness, the numerical call retains its certificates, and release restores
the caller's queue and clock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedProducerPlan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

private theorem setup_budget (s d k w x : ℕ) (h : x ≤ s+d+22*k+4) : x ≤ s+d+31*k+9+w := by omega
private theorem body_budget (s m d k w x : ℕ) (hm : m+d ≤ s+d+22*k+4) (h : x ≤ m+d+w) :
    x ≤ s+d+22*k+4+w := by omega
private theorem widen_body (s d k w x : ℕ) (h : x ≤ s+d+22*k+4+w) : x ≤ s+d+31*k+9+w := by omega
private theorem release_budget (s f d k w x : ℕ) (hf : f+d ≤ s+d+22*k+4+w) (h : x ≤ f+d+9*k+5) :
    x ≤ s+d+31*k+9+w := by omega

noncomputable def fromLiveBank (plan : PackedProducerPlan T Q) (source : Fin 325 → Fin T) : Pr P T Q A U :=
  .seq (plan.prepareDescriptor source) (.seq plan.program plan.releaseDescriptor)

theorem fromLiveBank_exec (plan : PackedProducerPlan T Q) (r : PackedNormalizedJob A s)
    (source : Fin 325 → Fin T) (hsourceReg : ∀ i, [source i,plan.src,plan.tmp,plan.saved].Nodup)
    (hA : 96 ≤ A) (t B L : ℕ) [NeZero t] (ht : r.t = t) (hp : 4 ≤ r.p)
    (htarget : r.p+2 ≤ r.targetOut) (hlocal : r.localityTarget = r.targetOut)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t r.α = 1)
    (hreplicas : r.Fs.length = B) (hcore : IntegerMultBounds.NLogN.PhaseCellMatrix.coreLength s r.coreWidth r.k = L)
    (v : HS T Q A U) (S : Stacks T A) (hwords : ∀ i, S.R (source i) = r.words i)
    (hblank : ∀ i, S.R (plan.work i) = []) (hleft : ∀ i, S.L (plan.work i) = [])
    (hscratch : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = [])
    (hclock : S.R plan.clock = []) (hsaved : S.R plan.saved = []) (hsavedClock : S.R plan.savedClock = [])
    (C depth : ℕ) (hpush : mnProgPush (plan.program (P := P) (U := U) (A := A)) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) :
    let tape := descriptorScheduleTape plan.work PackedNormalizedJob.words [r]
    ∃ v' n, ∃ rows : Fin 1 → Fin B → List GaussianInt,
      v'.user = v.user ∧ n ≤ plan.timeCost (U := U) [r]+20*tape.length+7 ∧
      (∀ i j, (rows i j).length = L) ∧
      (∀ i : Fin 1, r.ExactRowOutput J (List.ofFn (rows i))) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        31*tape.length+9+(C+1)*plan.workspace (U := U) [r]) depth (plan.fromLiveBank source) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R plan.result
          ((List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten++S.R plan.result))}) := by
  dsimp only
  have hr := plan.hreg
  regs_ne hr
  let tape := descriptorScheduleTape plan.work PackedNormalizedJob.words [r]
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R plan.src (tape++S.R plan.src)) plan.clock [tick])}
  obtain ⟨v₁,hu₁,hready,he₁⟩ := plan.prepareDescriptor_exec (body := body) r source hsourceReg v S hwords hblank hleft hscratch
    hclock hsaved hsavedClock depth
  change plan.Ready [r] (S.R plan.src) M at hready
  obtain ⟨v₂,n₂,rows,hu₂,hn₂,he₂,hlen,hcert,hstock⟩ := plan.exec (body := body) hA [r] r.W (by simp)
    t (by simpa using ht) (by simpa using hp) (by simpa using htarget) (by simpa using hlocal)
    (fun _ => J) (by simpa using hJ) B L (by simpa using hreplicas) (by simpa using hcore)
    (S.R plan.src) v₁ M hready
  let output := (List.ofFn fun i => (List.ofFn fun j => cstream A r.W (rows i j)).flatten).flatten
  let F : Stacks T A := {M with R := Function.update M.R plan.result (output++M.R plan.result)}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := plan.releaseDescriptor_exec (body := body) r (S.R plan.src) v₂ F
    (by simpa only [F,Function.update_of_ne ‹plan.src ≠ plan.result›,List.reverse_cons,List.reverse_nil,List.nil_append] using hready.hsource)
    (by simpa only [F,Function.update_of_ne ‹plan.count ≠ plan.result›] using hready.hscratch plan.count (by simp))
    (by simpa only [F,Function.update_of_ne ‹plan.tmp ≠ plan.result›] using hready.hscratch plan.tmp (by simp))
    (by simpa only [F,Function.update_of_ne ‹plan.result ≠ plan.clock›.symm,List.length_cons,List.length_nil] using hready.hclock) depth
  have htape : descriptorBankTape ((List.ofFn source).map (fun i => (i,S.R i))) = tape := by
    simp only [tape,descriptorScheduleTape,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
      placedDescriptorFields,descriptorBankTape,List.flatMap_def,List.map_ofFn,Function.comp_def,hwords]
  have hsetupTime := emitDescriptorBankCost_le S.R (List.ofFn source)
  rw [htape] at hsetupTime
  let w := (C+1)*plan.workspace (U := U) [r]
  let bound := mnSize (Host.mk v S)+depth+31*tape.length+9+w
  have hsetup := he₁.final
  change mnSize (Host.mk v₁ M)+depth ≤ mnSize (Host.mk v S)+depth+22*tape.length+4 at hsetup
  have hw₁ := he₁.mono (J := fun z state => mnSize state+z ≤ bound) (by
    intro z state hs
    exact setup_budget _ _ _ _ _ hs)
  have hw₂ := (hstock C hpush hbody depth).mono (J := fun z state =>
    mnSize state+z ≤ mnSize (Host.mk v S)+depth+22*tape.length+4+w) (by
      intro z state hs
      exact body_budget _ _ _ _ _ _ hsetup hs)
  have hrun := hw₂.final
  change mnSize (Host.mk v₂ F)+depth ≤ mnSize (Host.mk v S)+depth+22*tape.length+4+w at hrun
  have hw₂' := hw₂.mono (J := fun z state => mnSize state+z ≤ bound) (by
    intro z state hs
    exact widen_body _ _ _ _ _ hs)
  have hw₃ := he₃.mono (J := fun z state => mnSize state+z ≤ bound) (by
    intro z state hs
    change mnSize state+z ≤ mnSize (Host.mk v₂ F)+depth+9*tape.length+5 at hs
    exact release_budget _ _ _ _ _ _ hrun hs)
  have he := ExecWithin.seq hw₁ (ExecWithin.seq hw₂' hw₃)
  have hout : Host.mk v₃ {F with R := (Function.update (Function.update F.R plan.src (S.R plan.src)) plan.clock [])} =
      Host.mk v₃ {S with R := Function.update S.R plan.result (output++S.R plan.result)} := by
    apply congrArg (Host.mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = plan.clock
    · subst i
      simp only [Function.update_self,Function.update_of_ne ‹plan.result ≠ plan.clock›.symm,hclock]
    by_cases his : i = plan.src
    · subst i
      simp only [Function.update_of_ne hic,Function.update_self,Function.update_of_ne ‹plan.src ≠ plan.result›]
    by_cases hir : i = plan.result
    · subst i
      simp only [F,M,Function.update_of_ne hic,Function.update_of_ne his,Function.update_self]
    · simp only [F,M,Function.update_of_ne hic,Function.update_of_ne his,Function.update_of_ne hir]
  refine ⟨v₃,emitDescriptorBankCost S.R (List.ofFn source)+1+(n₂+n₃),rows,hu₃.trans (hu₂.trans hu₁),?_,hlen,?_,?_⟩
  · dsimp only [tape] at hsetupTime ⊢
    omega
  · intro i
    simpa using hcert i
  · exact (congrArg (fun f => ExecWithin body (fun z state => mnSize state+z ≤ bound) depth
      (plan.fromLiveBank source) (Host.mk v S) (emitDescriptorBankCost S.R (List.ofFn source)+1+(n₂+n₃)) f) hout).mp he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedProducerPlan
