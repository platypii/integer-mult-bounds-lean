module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorInstallReady

/-! Generate and install all 55 descriptor scalar operands from binary dimension
and residue, with no supplied palette or width words. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def canonicalDescriptorInstallProgram (rg : Fin 101 → Fin T) : Pr P T Q A U :=
  .seq (canonicalDescriptorScalarGenerateProgram (rg ∘ canonicalDescriptorInstallCore))
    (descriptorScalarInstallProgram rg)

def canonicalDescriptorInstalledBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 101 → Fin T) (L n r : ℕ) :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  descriptorScalarInstalledBank
    (canonicalDescriptorScalarBank R (rg ∘ canonicalDescriptorInstallCore) L n r)
    rg p (canonicalStageWidths p)

theorem canonicalDescriptorInstall_exec (body : P → Pr P T Q A U)
    (rg : Fin 101 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 101, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let W := (canonicalStageWidths p).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 96 * L * L + 652 * L + 875 + 10 * L * (4 * W + 11) + 224 * W +
        (55 * (2 * L * (4 * W + 11) + 38 * W + 42) + 1) ∧
      Exec body (canonicalDescriptorInstallProgram rg) (mk v S) m
        (mk v' { S with R := canonicalDescriptorInstalledBank S.R rg L n r.val }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let core := rg ∘ canonicalDescriptorInstallCore
  have hc : Function.Injective core := hrg.comp canonicalDescriptorInstallCore_injective
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalDescriptorScalarGenerate_exec body core hc L n
    hn hlarge hdivisor r v S hdimension hresidue (by
      intro i h0 h9 h18
      exact hblank _ (fun he => h0 (Fin.ext (congrArg (fun x : Fin 101 => x.val) he)))
        (fun he => h9 (Fin.ext (congrArg (fun x : Fin 101 => x.val) he)))
        (fun he => h18 (Fin.ext (congrArg (fun x : Fin 101 => x.val) he))))
  let C : Stacks T A := { S with R := canonicalDescriptorScalarBank S.R core L n r.val }
  have hB := canonicalDescriptorInstall_width_le p
  have hW := canonicalDescriptorInstall_width_fit L n hn hlarge r
  have blank (i : Fin 101) (hi : 39 ≤ i.val) (h44 : i ≠ 44) : C.R (rg i) = [] := by
    apply canonicalDescriptorInstall_blank S.R rg hrg L n r.val
    · intro k hk
      apply hblank <;> intro he <;> subst k <;> norm_num at hk
    · exact hi
    · exact h44
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := descriptorScalarInstall_exec body rg hrg L W p
    (canonicalStageWidths p) (fun f => (hB f).trans_lt hW)
    (repairDescriptorScalarPalette_fit p r.isLt) v₁ C
    (canonicalDescriptorInstall_widths S.R rg hrg L n hlarge r hresidue)
    (canonicalDescriptorInstall_palette S.R rg hrg L n r.val)
    (by intro q; apply blank <;> simp [descriptorScalarDestination, Fin.ext_iff] <;> omega)
    (by intro i hi; apply blank <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
        all_goals rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hcost := descriptorScalarInstallCost_le L W W (canonicalStageWidths p) hB
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁, ?_, Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂,hcost]

end IntegerMultBounds.MathlibTM2.Routing
