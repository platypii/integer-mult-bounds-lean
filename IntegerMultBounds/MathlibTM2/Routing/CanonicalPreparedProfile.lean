module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalProfileProductionBank
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalProfileFits
public import IntegerMultBounds.MathlibTM2.Routing.MatchingResizedProfile

/-! The canonical setup bank supplies the fixed executed profile compiler, with
all readiness and numeric fits derived from generated geometry and widths. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {N Q A : ℕ} {P U : Type}

def canonicalProfileControlInput : Fin 3 → Fin 28 := ![1,18,21]
def canonicalProfileCountInput : Fin 3 → Fin 28 := ![11,1,26]
theorem canonicalProfileControlInput_injective : Function.Injective canonicalProfileControlInput := by decide +kernel
theorem canonicalProfileCountInput_injective : Function.Injective canonicalProfileCountInput := by decide +kernel

def canonicalProfileResizeInput (rg : Fin 28 → Fin N) (src : Fin N) : Fin 2 → Fin N := ![rg 26,src]

theorem canonicalProfileResizeInput_injective (rg : Fin 28 → Fin N) (src : Fin N)
    (hoff : src ∉ canonicalProfileTargets rg) : Function.Injective (canonicalProfileResizeInput rg src) := by
  have hne : src ≠ rg 26 := by intro h; apply hoff; simp [canonicalProfileTargets, h]
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [canonicalProfileResizeInput]

theorem canonicalPreparedProfile_exec (body : P → Pr P (N + 36) Q A U)
    (L n : ℕ) (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (r : Fin (canonicalRouterStride n)) (p : Par)
    (hp : p = routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
    (mate : Fin p.wy → Fin p.wy) (hinv : Function.Involutive mate) (reverse : Bool)
    (rg : Fin 28 → Fin N) (hrg : Function.Injective rg)
    (coreWords : Fin N → List (Fin (A + 4)))
    (hresidue : coreWords (rg 18) = binSyms L r.val)
    (src : Fin N) (hsrc : src ∉ canonicalProfileTargets rg)
    (htable : coreWords src = matchingEntryWords L (matchingTableEntries p.wy (matchingMateCoordinate mate)))
    (dst : Fin N) (v : HS (N + 36) Q A U) (S : Stacks (N + 36) A)
    (hR : S.R = matchingProductionBank (canonicalProfileSetupBank coreWords rg L n r.val) [] [] [] []) :
    let w := canonicalStageWidths p
    ∃ (v' : HS (N + 36) Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ matchingPrefixCountCost L L L + 24 * L + 29 +
        matchingFullProfileProductionCost p (w.indexBits + w.strideBits) w.strideBits (L + L + L) +
        2 * (L + L + L) + 2 + 4 * L * (4 * w.strideBits + 11) + 24 * L + 56 * w.strideBits + 90 +
        p.wy * (4 * L * (4 * (w.indexBits + w.strideBits) + 11) + 40 * L +
          64 * (w.indexBits + w.strideBits) + 122) + 8 ∧
      Exec body (matchingResizedProfileProgram (canonicalProfileResizeInput rg src) (rg ∘ canonicalProfileControlInput)
        (rg ∘ canonicalProfileCountInput) reverse dst) (mk v S) m
        (mk v' { S with R := (Function.update S.R (matchingCoreEmbed N dst)
          (sourceCoordinateInputWords w.indexBits w.strideBits
            (profileCoordinateInputs p (by subst p; exact (canonicalProfileFits L n hn hlarge r).1)
              (matchingDirectionTargets mate reverse) mate) ++ S.R (matchingCoreEmbed N dst))) }) := by
  subst p
  dsimp only
  obtain ⟨hK, hsource, hk, hrows, hentry, hwidth, hstride⟩ := canonicalProfileFits L n hn hlarge r
  obtain ⟨hKword, hrword, hnword, hwWord, heWord⟩ :=
    canonicalProfileSetup_parameters coreWords rg hrg L n hlarge r hresidue
  have hrawFit : (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val).wy < 2 ^ L := by
    rw [routerProfileParameters_width n _ _ hlarge r]
    exact (Nat.sub_le _ _).trans_lt hn
  have htargetFit : (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)).indexBits +
      (canonicalStageWidths (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)).strideBits < 2 ^ L := by omega
  have hraw := (canonicalProfileSetupBank_keep coreWords rg L n r.val src hsrc).trans htable
  exact matchingResizedProfile_exec body _ mate hK r.isLt hinv reverse _ _ L L L L
    hsource hk hrows hentry hwidth hstride
    (rg ∘ canonicalProfileControlInput) (rg ∘ canonicalProfileCountInput)
    (hrg.comp canonicalProfileControlInput_injective) (hrg.comp canonicalProfileCountInput_injective)
    (canonicalProfileSetupBank coreWords rg L n r.val)
    hKword hrword hwWord hnword hKword heWord
    (canonicalProfileResizeInput rg src) (canonicalProfileResizeInput_injective rg src hsrc)
    L L hrawFit htargetFit heWord hraw dst v S hR


def canonicalProfileProgram (rg : Fin 28 → Fin N) (src : Fin N) (reverse : Bool) (dst : Fin N) : Pr P (N + 36) Q A U :=
  canonicalProfileScope (matchingCoreEmbed N ∘ rg)
    (matchingResizedProfileProgram (canonicalProfileResizeInput rg src) (rg ∘ canonicalProfileControlInput) (rg ∘ canonicalProfileCountInput) reverse dst)

theorem canonicalProfile_exec (body : P → Pr P (N + 36) Q A U)
    (L n : ℕ) (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (p : Par)
    (hp : p = routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
    (mate : Fin p.wy → Fin p.wy) (hinv : Function.Involutive mate) (reverse : Bool)
    (rg : Fin 28 → Fin N) (hrg : Function.Injective rg)
    (coreWords : Fin N → List (Fin (A + 4)))
    (hdimension : coreWords (rg 0) = binSyms L n)
    (hresidue : coreWords (rg 18) = binSyms L r.val)
    (hblank : ∀ j : Fin 28, j ≠ 0 → j ≠ 9 → j ≠ 18 → coreWords (rg j) = [])
    (src : Fin N) (hsrc : src ∉ canonicalProfileTargets rg)
    (htable : coreWords src = matchingEntryWords L (matchingTableEntries p.wy (matchingMateCoordinate mate)))
    (dst : Fin N) (hdst : dst ∉ canonicalProfileTargets rg)
    (v : HS (N + 36) Q A U) (S : Stacks (N + 36) A)
    (hR : S.R = matchingProductionBank coreWords [] [] [] []) :
    let w := canonicalStageWidths p
    ∃ (v' : HS (N + 36) Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ matchingPrefixCountCost L L L + 24 * L + 29 +
        matchingFullProfileProductionCost p (w.indexBits + w.strideBits) w.strideBits (L + L + L) +
        2 * (L + L + L) + 2 + 4 * L * (4 * w.strideBits + 11) + 24 * L + 56 * w.strideBits + 90 +
        p.wy * (4 * L * (4 * (w.indexBits + w.strideBits) + 11) + 40 * L +
          64 * (w.indexBits + w.strideBits) + 122) + 8 +
        96 * L * L + 584 * L + 549 ∧
      Exec body (canonicalProfileProgram rg src reverse dst) (mk v S) m
        (mk v' { S with R := (Function.update S.R (matchingCoreEmbed N dst)
          (sourceCoordinateInputWords w.indexBits w.strideBits
            (profileCoordinateInputs p (by subst p; exact (canonicalProfileFits L n hn hlarge r).1)
              (matchingDirectionTargets mate reverse) mate) ++ S.R (matchingCoreEmbed N dst))) }) := by
  dsimp only
  have core (j : Fin N) : S.R (matchingCoreEmbed N j) = coreWords j := by
    rw [hR, matchingProductionBank_core]
  have hdst' : matchingCoreEmbed N dst ∉ canonicalProfileTargets (matchingCoreEmbed N ∘ rg) := by
    simpa [canonicalProfileTargets, (matchingCoreEmbed_injective N).eq_iff] using hdst
  apply canonicalProfileScope_exec body (matchingCoreEmbed N ∘ rg)
    ((matchingCoreEmbed_injective N).comp hrg) L n r.val hn hlarge hdivisor r.isLt v S
    ((core _).trans hdimension) ((core _).trans hresidue)
    (fun j h0 h9 h18 => (core _).trans (hblank j h0 h9 h18))
    (matchingCoreEmbed N dst) hdst' _ _ _ _
  intro u
  let C : Stacks (N + 36) A :=
    { S with R := canonicalProfileSetupBank S.R (matchingCoreEmbed N ∘ rg) L n r.val }
  have hC : C.R = matchingProductionBank (canonicalProfileSetupBank coreWords rg L n r.val) [] [] [] [] := by
    dsimp only [C]
    rw [hR, canonicalProfileSetupBank_production]
  obtain ⟨u', m, hu, hm, hex⟩ := canonicalPreparedProfile_exec body L n hn hlarge r p hp mate hinv reverse
    rg hrg coreWords hresidue src hsrc htable dst u C hC
  have keep : C.R (matchingCoreEmbed N dst) = S.R (matchingCoreEmbed N dst) :=
    canonicalProfileSetupBank_keep S.R (matchingCoreEmbed N ∘ rg) L n r.val _ hdst'
  rw [keep] at hex
  exact ⟨u', m, hu, hm, hex⟩

end
end IntegerMultBounds.MathlibTM2.Routing
