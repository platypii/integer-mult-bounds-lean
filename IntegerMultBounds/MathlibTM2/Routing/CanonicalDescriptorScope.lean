module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorInstall

/-! Borrow the generated descriptor scalar bank around an executed call, then
erase the installed fields and all generated setup words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def canonicalDescriptorScope (rg : Fin 101 → Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  canonicalDescriptorScalarScope (rg ∘ canonicalDescriptorInstallCore)
    (binaryResizeBatchScope (fun q => rg ∘ descriptorScalarInstallSlot q) descriptorScalarJobs call)

theorem canonicalDescriptorScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 101 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 101, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = [])
    (dst : Fin T)
    (hscalar : dst ∉ canonicalDescriptorScalarTargets (rg ∘ canonicalDescriptorInstallCore))
    (hfields : ∀ q, dst ≠ rg (descriptorScalarDestination q))
    (output : List (Fin (A + 4))) (call : Pr P T Q A U) (price : ℕ)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := canonicalDescriptorInstalledBank S.R rg L n r.val }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R dst output })) :
    let W := (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r.val)).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ price + 96 * L * L + 676 * L + 922 + 10 * L * (4 * W + 11) + 246 * W +
        55 * (2 * L * (4 * W + 11) + 38 * W + 42) + 55 * (2 * W + 2) + 2 ∧
      Exec body (canonicalDescriptorScope rg call) (mk v S) m
        (mk v' { S with R := Function.update S.R dst output }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let core := rg ∘ canonicalDescriptorInstallCore
  let batchPrice := 55 * (2 * L * (4 * W + 11) + 38 * W + 42) + 55 * (2 * W + 2) + 2
  have hc : Function.Injective core := hrg.comp canonicalDescriptorInstallCore_injective
  have cb : ∀ i : Fin 46, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (core i) = [] := by
    intro i h0 h9 h18
    exact hblank _ (fun he => h0 (Fin.ext (congrArg (fun x : Fin 101 => x.val) he)))
      (fun he => h9 (Fin.ext (congrArg (fun x : Fin 101 => x.val) he)))
      (fun he => h18 (Fin.ext (congrArg (fun x : Fin 101 => x.val) he)))
  have inner (u : HS T Q A U) :
      let C : Stacks T A := { S with R := canonicalDescriptorScalarBank S.R core L n r.val }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price + batchPrice ∧
        Exec body (binaryResizeBatchScope (fun q => rg ∘ descriptorScalarInstallSlot q)
          descriptorScalarJobs call) (mk u C) m
          (mk u' { C with R := Function.update C.R dst output }) := by
    let C : Stacks T A := { S with R := canonicalDescriptorScalarBank S.R core L n r.val }
    have blank (i : Fin 101) (hi : 39 ≤ i.val) (h44 : i ≠ 44) : C.R (rg i) = [] := by
      apply canonicalDescriptorInstall_blank S.R rg hrg L n r.val
      · intro k hk
        apply hblank <;> intro he <;> subst k <;> norm_num at hk
      · exact hi
      · exact h44
    have hdst : (descriptorScalarJobs.map (fun q => (rg ∘ descriptorScalarInstallSlot q) 3)).Nodup :=
      descriptorScalarJobs_nodup.map (hrg.comp descriptorScalarDestination_injective)
    obtain ⟨u',m,hu,hm,he⟩ := binaryResizeBatchScope_exec body
      (fun q => rg ∘ descriptorScalarInstallSlot q)
      (fun q => hrg.comp (descriptorScalarInstallSlot_injective q))
      (fun _ => L) (fun _ => W) (fun q => repairDescriptorScalarWidth (canonicalStageWidths p) q.2)
      (fun q => repairDescriptorScalarPalette p (repairDescriptorScalarSlot q.1 q.2))
      (fun q => (canonicalDescriptorInstall_width_le p q.2).trans_lt
        (canonicalDescriptorInstall_width_fit L n hn hlarge r))
      (fun q => repairDescriptorScalarPalette_fit p r.isLt _) descriptorScalarJobs hdst
      (fun q i hi k => hrg.ne (descriptorScalarInstallSlot_separate q i hi k))
      W (fun q _ => canonicalDescriptorInstall_width_le p q.2) u C
      (canonicalDescriptorInstall_widths S.R rg hrg L n hlarge r hresidue)
      (by intro q; exact canonicalDescriptorInstall_palette S.R rg hrg L n r.val _)
      (by
        intro q _
        change C.R (rg (descriptorScalarDestination q)) = []
        apply blank
        · change 39 ≤ 46 + 5 * q.1.val + q.2.val
          omega
        · intro h
          have hv := congrArg (fun x : Fin 101 => x.val) h
          change 46 + 5 * q.1.val + q.2.val = 44 at hv
          omega)
      (by
        intro q i h0 h1 h3
        apply blank
        · fin_cases i <;> simp_all [descriptorScalarInstallSlot]
        · fin_cases i <;> simp_all [descriptorScalarInstallSlot])
      dst (by
        intro hm
        obtain ⟨q,_,he⟩ := List.mem_map.mp hm
        exact hfields q he.symm) output call price (by intro u; exact hcall u)
    have hcost := descriptorScalarInstallCost_le L W W (canonicalStageWidths p)
      (canonicalDescriptorInstall_width_le p)
    have hl : descriptorScalarJobs.length = 55 := by decide +kernel
    rw [hl] at hm
    refine ⟨u',m,hu,?_,he⟩
    dsimp only [batchPrice]
    nlinarith only [hm,hcost]
  obtain ⟨v',m,hu,hm,he⟩ := canonicalDescriptorScalarScope_exec body core hc L n hn hlarge
    hdivisor r v S hdimension hresidue cb dst hscalar output
    (binaryResizeBatchScope (fun q => rg ∘ descriptorScalarInstallSlot q) descriptorScalarJobs call)
    (price + batchPrice) inner
  refine ⟨v',m,hu,?_,he⟩
  dsimp only [batchPrice] at hm
  nlinarith only [hm]

end IntegerMultBounds.MathlibTM2.Routing
