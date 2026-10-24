module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorSharedGenerate

/-! All 61 nonempty canonical descriptor operands are generated together.
Shared installation leaves the original 101-register scalar scope unchanged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def canonicalDescriptorFieldCore : Fin 101 → Fin 108 := Fin.castLE (by decide)
theorem canonicalDescriptorFieldCore_injective : Function.Injective canonicalDescriptorFieldCore := by
  decide +kernel

def canonicalDescriptorGenerateProgram (rg : Fin 108 → Fin T) : Pr P T Q A U :=
  .seq (canonicalDescriptorSharedGenerateProgram rg)
    (descriptorScalarInstallProgram (rg ∘ canonicalDescriptorFieldCore))

def canonicalDescriptorGeneratedBank (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (L n r : ℕ) :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
  descriptorScalarInstalledBank (canonicalDescriptorSharedGeneratedBank R rg L n r)
    (rg ∘ canonicalDescriptorFieldCore) p (canonicalStageWidths p)

theorem canonicalDescriptorGeneratedBank_outside (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (L n r : ℕ) (k : Fin T) (hoff : ∀ i, rg i ≠ k) :
    canonicalDescriptorGeneratedBank R rg L n r k = R k := by
  unfold canonicalDescriptorGeneratedBank descriptorScalarInstalledBank
  rw [binaryResizeBatchBank_keep]
  · unfold canonicalDescriptorSharedGeneratedBank
    rw [descriptorSharedGeneratedBank_keep]
    · apply canonicalDescriptorScalarBank_keep
      have hn (i : Fin 108) : k ≠ rg i := (hoff i).symm
      simp [canonicalDescriptorScalarTargets,Function.comp_apply,hn]
    · intro hm
      rcases List.mem_cons.mp hm with he | hm
      · exact hoff 101 he.symm
      · obtain ⟨i,_,he⟩ := List.mem_map.mp hm
        exact hoff _ he
  · intro hm
    obtain ⟨q,_,he⟩ := List.mem_map.mp hm
    exact hoff _ he

theorem canonicalDescriptorGeneratedBank_field (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ) (q : Fin 11 × Fin 5) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
    canonicalDescriptorGeneratedBank R rg L n r
      (rg (canonicalDescriptorFieldCore (descriptorScalarDestination q))) =
        binSyms (repairDescriptorScalarWidth (canonicalStageWidths p) q.2)
          (repairDescriptorScalarValues p q.1 q.2) := by
  exact descriptorScalarInstalledBank_at _ (rg ∘ canonicalDescriptorFieldCore)
    (hrg.comp canonicalDescriptorFieldCore_injective) _ _ q

theorem canonicalDescriptorGeneratedBank_shared (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ) (i : Fin 6) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
    canonicalDescriptorGeneratedBank R rg L n r (rg (descriptorSharedDestination i)) =
      binSyms (descriptorSharedWidth (canonicalStageWidths p) i)
        (descriptorSharedValue p (canonicalStageWidths p) i) := by
  unfold canonicalDescriptorGeneratedBank descriptorScalarInstalledBank
  rw [binaryResizeBatchBank_keep]
  · exact descriptorSharedGeneratedBank_at _ rg hrg _ _ _ i
  · intro hm
    obtain ⟨q,_,he⟩ := List.mem_map.mp hm
    have hv := congrArg (fun x : Fin 108 => x.val) (hrg he)
    change (descriptorScalarDestination q).val = 102 + i.val at hv
    have hl := (descriptorScalarDestination q).isLt
    omega

theorem canonicalDescriptorGeneratedBank_scratch (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hblank : ∀ i : Fin 108, 39 ≤ i.val → R (rg i) = [])
    (i : Fin 108) (hlo : 39 ≤ i.val) (hhi : i.val < 46) (h44 : i ≠ 44) :
    canonicalDescriptorGeneratedBank R rg L n r (rg i) = [] := by
  unfold canonicalDescriptorGeneratedBank descriptorScalarInstalledBank
  rw [binaryResizeBatchBank_keep]
  · rw [show canonicalDescriptorSharedGeneratedBank R rg L n r (rg i) =
        canonicalDescriptorScalarBank R (rg ∘ canonicalDescriptorSharedCore) L n r (rg i) from
        descriptorSharedGeneratedBank_low _ rg hrg _ _ _ i (by omega)]
    exact canonicalDescriptorShared_blank R rg hrg L n r hblank i hlo h44
  · intro hm
    obtain ⟨q,_,he⟩ := List.mem_map.mp hm
    have hv := congrArg (fun x : Fin 108 => x.val) (hrg he)
    change 46 + 5 * q.1.val + q.2.val = i.val at hv
    omega

theorem canonicalDescriptorGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 108 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 108, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = []) :
    let W := (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n)
      (canonicalRouterGap n) r.val)).coordinateBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 96 * L * L + 652 * L + 875 + 10 * L * (4 * W + 11) + 224 * W +
        (8 * W + 9) + 6 * (2 * L * (4 * W + 11) + 12 * (L + W) + 26 * W + 42) + 1 +
        (55 * (2 * L * (4 * W + 11) + 38 * W + 42) + 1) ∧
      Exec body (canonicalDescriptorGenerateProgram rg) (mk v S) m
        (mk v' { S with R := canonicalDescriptorGeneratedBank S.R rg L n r.val }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let W := (canonicalStageWidths p).coordinateBits
  let fields := rg ∘ canonicalDescriptorFieldCore
  have hf : Function.Injective fields := hrg.comp canonicalDescriptorFieldCore_injective
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalDescriptorSharedGenerate_exec body rg hrg L n hn hlarge
    hdivisor r v S hdimension hresidue hblank
  let C : Stacks T A := { S with R := canonicalDescriptorSharedGeneratedBank S.R rg L n r.val }
  let D : Stacks T A := { S with R := (canonicalDescriptorScalarBank S.R
    (rg ∘ canonicalDescriptorSharedCore) L n r.val) }
  have keep (i : Fin 101) : C.R (fields i) = D.R (fields i) :=
    descriptorSharedGeneratedBank_low _ rg hrg W p (canonicalStageWidths p)
      (canonicalDescriptorFieldCore i) i.isLt
  have blank (i : Fin 101) (hi : 39 ≤ i.val) (h44 : i ≠ 44) : C.R (fields i) = [] := by
    rw [keep]
    apply canonicalDescriptorShared_blank S.R rg hrg L n r.val
    · intro k hk
      apply hblank <;> intro he <;> subst k <;> norm_num at hk
    · exact hi
    · intro he
      exact h44 (Fin.ext (congrArg (fun x : Fin 108 => x.val) he))
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := descriptorScalarInstall_exec body fields hf L W p
    (canonicalStageWidths p)
    (fun f => (canonicalDescriptorInstall_width_le p f).trans_lt
      (canonicalDescriptorInstall_width_fit L n hn hlarge r))
    (repairDescriptorScalarPalette_fit p r.isLt) v₁ C
    (by intro q; rw [keep]; exact canonicalDescriptorInstall_widths S.R fields hf L n hlarge r hresidue q)
    (by intro j; rw [keep]; exact canonicalDescriptorInstall_palette S.R fields hf L n r.val j)
    (by intro q; apply blank <;> simp [descriptorScalarDestination,Fin.ext_iff] <;> omega)
    (by
      intro i hi
      apply blank
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hcost := descriptorScalarInstallCost_le L W W (canonicalStageWidths p)
    (canonicalDescriptorInstall_width_le p)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂,hcost]

end IntegerMultBounds.MathlibTM2.Routing
