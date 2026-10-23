module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalTerminalLayout
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterTerminal
public import IntegerMultBounds.MathlibTM2.Routing.BinarySharedRouting

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

theorem canonicalTerminalRouting_exec {Q K : ℕ} {P U : Type}
    (body : P → Pr P canonicalTerminalT Q (prime + K) U)
    (n rows B L Lb : ℕ) (hn0 : 0 < n) (hn : n < 2 ^ L) (hBin : B < 2 ^ Lb)
    (hnB : n ≤ B) (hrows : 0 < rows) (hB : 1 ≤ B)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows) (cs : List (ElementaryCoordinate n))
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (v : HS canonicalTerminalT Q (prime + K) U)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rows * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8) :
    let compiler := canonicalTerminalCompiler
    let rg := canonicalTerminalRouter
    let input := canonicalTerminalInput
    let src := canonicalTerminalAux 0
    let archive := canonicalTerminalAux 1
    let saved := canonicalTerminalAux 2
    let work := canonicalTerminalAux 3
    let tmp := canonicalTerminalAux 4
    let ctmp := canonicalTerminalAux 5
    let cfg := sharedInputConfig input
    let hrg := canonicalTerminalRouter_injective
    let hd := selectiveSwapHd
    let pay := selectiveSwapPay
    let hhd := selectiveSwapHd_inj
    let hT := canonicalTerminalT_fit
    let S : Stacks canonicalTerminalT (prime + K) :=
      ⟨[], [], fun _ => [], canonicalTerminalRoutingBank rg compiler input src l.flatten
        (elementaryCoordinateFrames L cs) n L Lb B rowBits⟩
    ∃ (ds : List (ElementaryInstruction n)) (v' : HS canonicalTerminalT Q (prime + K) U) (m : ℕ),
      ds.map (fun d => (d.target, d.source)) = cs.reverse.map ElementaryCoordinate.key ∧ v'.user = v.user ∧
      (m : ℝ) ≤ (L * (4 * n + 11) + 22 * n + 6 * rowBits.length + 46 : ℕ) + ((Lb * (4 * B + 11) + (n + rowBits.length) * (4 * (rows * 2 ^ n) + 11) + 2 * B + 2 * (rows * 2 ^ n) + 10 * n + 24 : ℕ) +
        ((cs.length : ℝ) *
          ((elementaryCompileBase n L Lb rowBits.length + 7 * (rowBits.length + 3 * n + Lb + 11) + 4 * L + 6 : ℕ) +
            elementaryBaseCost rg n rows B S + 2 +
            (12 * swapT 6 + 22 : ℕ) * (rowBits.length + 3 * n + Lb + 11 : ℕ)) + 10) +
        (2 * B + 2 * (rows * 2 ^ n) + 4 * n + 9 : ℕ)) +
        (6 * n + 2 * rowBits.length + 7 : ℕ) ∧
      Exec body (sharedInputRoutingProgram input (elementarySharedProgram rg cfg work tmp ctmp Lb (n + rowBits.length) B (rows * 2 ^ n)
        (compiledElementaryProgram compiler src archive rg hrg hd pay hhd hQ hT saved))) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .str) (moveRecs (elementaryInstructionsRank rows ds) l).flatten }) := by
  dsimp only
  apply binarySharedRouting_exec (body := body)
    (compiler := canonicalTerminalCompiler) (hcompiler := canonicalTerminalCompiler_injective)
    (src := canonicalTerminalAux 0) (archive := canonicalTerminalAux 1)
    (rg := canonicalTerminalRouter) (hrg := canonicalTerminalRouter_injective)
    (hd := selectiveSwapHd) (pay := selectiveSwapPay) (hhd := selectiveSwapHd_inj)
    (hpay := by intro j h; have hv := congrArg Fin.val h; have := j.isLt; change j.val = 5 at hv; omega) (hQ := hQ) (hT := canonicalTerminalT_fit)
    (saved := canonicalTerminalAux 2) (input := canonicalTerminalInput)
    (hinputReg := canonicalTerminalInput_injective)
    (work := canonicalTerminalAux 3) (tmp := canonicalTerminalAux 4) (ctmp := canonicalTerminalAux 5)
    (wb := Lb) (wm := n + rowBits.length) (cfg := sharedInputConfig canonicalTerminalInput)
    (hcfg := rfl) (hregs := canonicalTerminalShared_regs _ _ _ _)
    (hsources := canonicalTerminalShared_sources _ _ _ _)
    (L := L) (Lb := Lb) (hwb := rfl) (hn0 := hn0) (hn := hn) (hBin := hBin)
    (hnB := hnB) (hrows := hrows) (hB := hB) (rowBits := rowBits) (hrow := hrow)
    (hrowNe := hrowNe) (hrowValue := hrowValue) (cs := cs) (v := v)
    (hwm := rfl) (l := l) (hl := hl) (hlB := hlB) (h8 := h8)
  case hcompileReady =>
    apply canonicalTerminalBank_ready _ _ canonicalTerminalCompiler_injective
    intro c r
    simp [canonicalTerminalCompiler, canonicalTerminalInput]
  case hseparate =>
    intro r key
    fin_cases key <;> simp [elementarySharedTarget, canonicalTerminalCompiler, canonicalTerminalRouter]
  case hempty =>
    intro key
    fin_cases key <;> simp [elementarySharedTarget]
    all_goals simp [canonicalTerminalRouter]
  case hblank =>
    intro r _ _ _ _ hr _ _
    dsimp only
    rw [canonicalTerminalBank_fixed_router]
    exact ite_eq_right (canonicalTerminalRouter_injective.ne hr)
  case hmeta =>
    intro key
    dsimp only
    unfold elementaryConfigTarget
    split <;> rw [canonicalTerminalBank_fixed_router] <;> simp [canonicalTerminalRouter]
  all_goals try simp only [canonicalTerminalBank_fixed_input, canonicalTerminalBank_fixed_compiler,
    canonicalTerminalBank_fixed_router, canonicalTerminalBank_fixed_aux, elementaryCompilerInputWords, sharedInputInitialWords]
  all_goals try simp [canonicalTerminalCompiler, canonicalTerminalRouter, canonicalTerminalInput,
    canonicalTerminalAux, sharedInputPrivate]

theorem canonicalRouterTerminal_exec {Q K : ℕ} {P U : Type}
    (body : P → Pr P canonicalTerminalT Q (prime + K) U)
    (n rows B L Lb : ℕ) (hstride : canonicalRouterStride n ≤ n)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate) (k : Fin 3) (reverse : Bool) (hn0 : 0 < n) (hn : n < 2 ^ L) (hBin : B < 2 ^ Lb)
    (hnB : n ≤ B) (hrows : 0 < rows) (hB : 1 ≤ B)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (v : HS canonicalTerminalT Q (prime + K) U)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rows * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8) :
    let cs := canonicalRouterTerminalCoordinates n hstride mate hinv k reverse
    let compiler := canonicalTerminalCompiler
    let rg := canonicalTerminalRouter
    let input := canonicalTerminalInput
    let src := canonicalTerminalAux 0
    let archive := canonicalTerminalAux 1
    let saved := canonicalTerminalAux 2
    let work := canonicalTerminalAux 3
    let tmp := canonicalTerminalAux 4
    let ctmp := canonicalTerminalAux 5
    let cfg := sharedInputConfig input
    let hrg := canonicalTerminalRouter_injective
    let hd := selectiveSwapHd
    let pay := selectiveSwapPay
    let hhd := selectiveSwapHd_inj
    let hT := canonicalTerminalT_fit
    let S : Stacks canonicalTerminalT (prime + K) :=
      ⟨[], [], fun _ => [], canonicalTerminalRoutingBank rg compiler input src l.flatten
        (elementaryCoordinateFrames L cs) n L Lb B rowBits⟩
    ∃ (ds : List (ElementaryInstruction n)) (v' : HS canonicalTerminalT Q (prime + K) U) (m : ℕ),
      ds.map (fun d => (d.target, d.source)) = cs.reverse.map ElementaryCoordinate.key ∧ v'.user = v.user ∧
      (m : ℝ) ≤ (L * (4 * n + 11) + 22 * n + 6 * rowBits.length + 46 : ℕ) + ((Lb * (4 * B + 11) + (n + rowBits.length) * (4 * (rows * 2 ^ n) + 11) + 2 * B + 2 * (rows * 2 ^ n) + 10 * n + 24 : ℕ) +
        ((cs.length : ℝ) *
          ((elementaryCompileBase n L Lb rowBits.length + 7 * (rowBits.length + 3 * n + Lb + 11) + 4 * L + 6 : ℕ) +
            elementaryBaseCost rg n rows B S + 2 +
            (12 * swapT 6 + 22 : ℕ) * (rowBits.length + 3 * n + Lb + 11 : ℕ)) + 10) +
        (2 * B + 2 * (rows * 2 ^ n) + 4 * n + 9 : ℕ)) +
        (6 * n + 2 * rowBits.length + 7 : ℕ) ∧
      Exec body (sharedInputRoutingProgram input (elementarySharedProgram rg cfg work tmp ctmp Lb (n + rowBits.length) B (rows * 2 ^ n)
        (compiledElementaryProgram compiler src archive rg hrg hd pay hhd hQ hT saved))) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg .str) (moveRecs (elementaryInstructionsRank rows ds) l).flatten }) ∧
      ds.length < 131 * canonicalRouterGap n ∧
      ∀ i : Fin (rows * 2 ^ n),
        (fun q : Fin n => (elementaryInstructionsRank rows ds i).val.testBit q.val) =
          shear (canonicalRouterTerminalTargets n hstride mate hinv k reverse)
            (matchingClass (routingReservoir n (routingReservoirWidth n (canonicalRouterGap n))
              (routingReservoir_fit n (canonicalRouterGap n) hstride)) mate k)
            (fun q => i.val.testBit q.val) := by
  dsimp only
  obtain ⟨ds, v', m, hk, hu, hm, he⟩ := canonicalTerminalRouting_exec body n rows B L Lb hn0 hn hBin
    hnB hrows hB rowBits hrow hrowNe hrowValue
    (canonicalRouterTerminalCoordinates n hstride mate hinv k reverse) hQ v l hl hlB h8
  refine ⟨ds, v', m, hk, hu, hm, he, ?_, ?_⟩
  · have hc := congrArg List.length hk
    simp only [List.length_map, List.length_reverse] at hc
    rw [hc]
    exact canonicalRouterTerminalCoordinates_count n hstride mate hinv k reverse
  · exact canonicalRouterTerminalInstructions_bits n hstride mate hinv k reverse rows ds hk

end
end IntegerMultBounds.MathlibTM2.Routing
