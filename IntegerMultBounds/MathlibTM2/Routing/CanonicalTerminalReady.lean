module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalTerminalBank
public import IntegerMultBounds.MathlibTM2.Routing.ElementarySharedFrame

/-! The constructed terminal bank discharges the router's complete readiness
contract after the existing executed counter generation and metadata setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
noncomputable section

theorem canonicalTerminalRoutingBank_ready {t₀ T A : ℕ}
    (rg : LayReg t₀ → Fin T) (hrg : Function.Injective rg)
    (compiler : ElementaryCompilerReg → Fin T) (input : SharedInputReg → Fin T)
    (hi : Function.Injective input)
    (hcompiler : ∀ c r, compiler c ≠ rg r) (hinput : ∀ i r, input i ≠ rg r)
    (src : Fin T) (hsrc : ∀ r, src ≠ rg r)
    (stream coordinates : List (Fin (A + 4))) (n L Lb B rows : ℕ) (rowBits : List Bool)
    (hrows : Counter.value rowBits = rows) (hB : B < 2 ^ Lb)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) :
    let bank := canonicalTerminalRoutingBank rg compiler input src stream coordinates n L Lb B rowBits
    let generated := sharedInputBank bank input n rows rowBits.length
    ElementaryLoopReady rg hd pay
      (metadataInstalled generated
        (elementarySharedJobs rg (sharedInputConfig input) Lb (n + rowBits.length) B (rows * 2 ^ n))) n rows B := by
  dsimp only
  let bank := canonicalTerminalRoutingBank rg compiler input src stream coordinates n L Lb B rowBits
  let generated := sharedInputBank bank input n rows rowBits.length
  have hblank (r : LayReg t₀) (hr : r ≠ .str) : generated (rg r) = [] := by
    dsimp only [generated]
    rw [sharedInputBank_keep]
    · exact canonicalTerminalRoutingBank_blank rg hrg compiler input hcompiler hinput src hsrc
        stream coordinates n L Lb B rowBits r hr
    · simp only [sharedInputPrivate, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(hinput .records r).symm, (hinput .field r).symm, (hinput .mask r).symm⟩
  have hblock : bank (input .block) = binSyms Lb B :=
    canonicalTerminalBank_input compiler input hi _ n L Lb B rowBits .block
  have data := sharedInputBank_data bank input hi Lb n rows B rowBits hrows hB hblock
  apply elementarySharedSetup_ready rg hrg hd pay (sharedInputConfig input) Lb (n + rowBits.length)
    n rows B generated data
  · intro r _ _ _ _ hr _ _
    exact hblank r hr
  · intro key
    rcases elementaryConfigTarget_role rg hd key with ⟨j, hj⟩ | hj
    · rw [hj]
      exact hblank (.sw j) (by intro h; cases h)
    · rw [hj]
      exact hblank .mB (by intro h; cases h)
  · exact hblank (.sw (reg pay)) (by intro h; cases h)
  · intro j _
    exact hblank (.sw j) (by intro h; cases h)
  · intro i _ _ x hx
    rw [hblank (.sw (reg i)) (by intro h; cases h)] at hx
    exact False.elim (List.not_mem_nil hx)

end
end IntegerMultBounds.MathlibTM2.Routing
