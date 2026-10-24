module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalAuxiliaryClean
public import IntegerMultBounds.MathlibTM2.Routing.RouterAuxiliaryFrame

/-! Generate either remaining auxiliary frame from original binary inputs and
restore every setup tape. The two banks can surround the header frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalAuxiliaryFrameScopeProgram (rg : Fin 49 → Fin T) (dst : Fin T)
    (delimiter : Fin (A+4)) (profile : Bool) : Pr P T Q A U :=
  .seq (canonicalAuxiliaryGenerateProgram rg)
    (.seq (routerAuxiliaryCopyProgram (rg ∘ canonicalAuxiliarySlot) dst delimiter profile)
      (metadataClean (canonicalAuxiliaryTargets.map rg)))

theorem canonicalAuxiliaryFrameScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 49 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A+4)) (profile : Bool) (L n : ℕ)
    (hn : n < 2^L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3*canonicalRouterGap n < 2^L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ i : Fin 49, i ≠ 0 → i ≠ 9 → i ≠ 18 → S.R (rg i) = []) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let I := (canonicalStageWidths p).indexBits
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 96*L*L+592*L+560 + (2*L*(4*I+11)+22*L+26*I+55) +
        (7*(6*(I+canonicalScalarWidth p.wy+1)+7)+1) +
        (24*L+2*I+2*canonicalScalarWidth p.wy+33) ∧
      Exec body (canonicalAuxiliaryFrameScopeProgram rg dst delimiter profile) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (routerAuxiliaryFrame delimiter (rg ∘ canonicalAuxiliarySlot) profile I p.n p.wy ++ S.R dst)) }) := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let I := (canonicalStageWidths p).indexBits
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalAuxiliaryGenerate_exec body rg hrg L n hn hlarge hdivisor r v S
    hdimension hresidue hblank
  let C : Stacks T A := { S with R := canonicalAuxiliaryBank S.R rg L n r.val }
  have keep (i : Fin 49) (hi : i ∉ canonicalAuxiliaryTargets) : C.R (rg i) = S.R (rg i) :=
    canonicalAuxiliaryBank_keep S.R rg L n r.val _ (by simpa [hrg.eq_iff] using hi)
  have empty : C.R (rg 3) = [] :=
    (keep 3 (by decide +kernel)).trans (hblank 3 (by decide) (by decide) (by decide))
  have bank (i : Fin 12) (hi : i ∈ routerAuxiliaryFrameSources profile) :
      C.R ((rg ∘ canonicalAuxiliarySlot) i) = routerAuxiliaryFrameWord I p.n p.wy i := by
    rcases routerAuxiliaryFrameSources_mem profile i hi with rfl | rfl | rfl | rfl
    · simp [C,canonicalAuxiliaryBank,routerAuxiliaryBank,canonicalAuxiliarySlot,
        routerAuxiliaryFrameWord,hrg.eq_iff,p,I]
    · simp [C,canonicalAuxiliaryBank,routerAuxiliaryBank,canonicalAuxiliarySlot,
        routerAuxiliaryFrameWord,hrg.eq_iff,p]
    · simp [C,canonicalAuxiliaryBank,routerAuxiliaryBank,canonicalAuxiliarySlot,
        routerAuxiliaryFrameWord]
    · exact empty
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := routerAuxiliaryCopy_exec body (rg ∘ canonicalAuxiliarySlot)
    (hrg.comp canonicalAuxiliarySlot_injective) dst (fun i => hoff _) delimiter profile I p.n p.wy v₁ C bank
    ((keep 6 (by decide +kernel)).trans (hblank 6 (by decide) (by decide) (by decide)))
    ((keep 7 (by decide +kernel)).trans (hblank 7 (by decide) (by decide) (by decide)))
  have outside : C.R dst = S.R dst := canonicalAuxiliaryBank_keep S.R rg L n r.val _ (by
    intro h; obtain ⟨i,_,he⟩ := List.mem_map.mp h; exact hoff i he)
  rw [outside] at he₂
  obtain ⟨v₃,hu₃,he₃⟩ := canonicalAuxiliaryClean_exec body rg hrg L n r.val v₂ S (by
    have sep : ∀ i ∈ canonicalAuxiliaryTargets, i ≠ 0 ∧ i ≠ 9 ∧ i ≠ 18 := by decide +kernel
    intro i hi
    have h := sep i hi
    exact hblank i h.1 h.2.1 h.2.2) dst hoff
    (routerAuxiliaryFrame delimiter (rg ∘ canonicalAuxiliarySlot) profile I p.n p.wy ++ S.R dst)
  refine ⟨v₃,m₁+(m₂+_),hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  nlinarith only [hm₁,hm₂]

end IntegerMultBounds.MathlibTM2.Routing
