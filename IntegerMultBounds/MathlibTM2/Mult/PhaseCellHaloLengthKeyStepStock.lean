module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthKeyStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProcessHaloLengthKeyStock

/-! Count retirement and flag probing add no space to a complete class step. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem haloLengthKeyStep_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp V a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (J R K : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ K)
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed E outputTail keyTail : List (Fin (A+4)))
    (c : Fin (A+4)) (cs : List (Fin (A+4))) (hcount : S.R 127 = c::cs)
    (hkey : L < 2^V) (hV : (S.R 125).length = V) (hkeys : S.R 126 = binSyms V L++keyTail)
    (hE : E.length = s*executionWidth p l target rhsExp) (hdst : S.R 132 = E++outputTail)
    (hmasters : ∀ r ∈ groupHeaderCopies, (S.R r.1).length =
      groupHeaderValue (2^15*p) (executionStagePrecision p l target rhsExp+1)
        (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) 0 r.1)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hleft : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsrc : S.R 110 = cstream A (executionWidth p l target rhsExp) (chirpLine s C) ++ borrowed)
    (h129 : S.R 129 = []) (h133 : S.R 133 = [])
    (hwidth : (S.R 130).length = executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(131 : Fin 144),134,135,136,137,140], S.R k = []) :
    let band := PhaseCellBand.width p u
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, ∃ E' : List (Fin (A+4)), v'.user = v.user ∧ v'.flag = cs.head?.isSome ∧
      n ≤ (6*L+19*V+14)+conditionalHaloClassCost p l L s t u target rhsExp a b+2 ∧
      ExecWithin (embTab groupReg body)
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
          processHaloLengthKeyWorkspace J R K p l L s t u target rhsExp V a b)
        0 (haloLengthKeyStep hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ E'.length = s*w ∧
      S'.R = keyLoopR S.R keyTail cs (E'++outputTail) ∧
      (∀ n : Fin (haloLengthGroup s t band a b L).length,
        PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L n) L)
          (publishedCellRead q w (0 : ZMod s) (S'.R 132)) x (1/(2 : ℝ)^target)) ∧
      (∀ K, K ≠ L → ∀ n : Fin (haloLengthGroup s t band a b K).length, ∀ j ∈ publishedCellCore
        (haloGroupOrigin s t band a b K n) K,
        publishedCellRead q w (0 : ZMod s) (S'.R 132) j = publishedCellRead q w (0 : ZMod s) (S.R 132) j) ∧
      (EncodedRange A w q (interiorOutputExponent p l target rhsExp) E →
        EncodedRange A w q (interiorOutputExponent p l target rhsExp) E') := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band a b L).length
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let S₀ : Stacks 144 A := { S with R := Function.update S.R 127 cs }
  have hpop : (.pop (.rt 127) (fun v : HS 144 Q A U => fun _ => v) .done : Act 144 Q A U).run (mk v S) = mk v S₀ := by
    simp [Action.run,update_rt,hcount,S₀]
  obtain ⟨v₁,S₁,n₁,ys,hu₁,hn₁,he₁,hi₁,ho₁,hl₁,hylen,hframe,herror⟩ :=
    processHaloLengthKey_spec_within (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hband has hbs hL hLs hpad C hC x hx J R K hpushJ hpushR hpushK
      v S₀ borrowed E outputTail keyTail hkey (by simpa [S₀] using hV) (by simpa [S₀] using hkeys)
      hE (by simpa [S₀] using hdst) (by
        intro r hr
        have h127 := (groupHeaderSources_off r hr).2.1
        simpa [S₀,h127] using hmasters r hr) (by simpa [S₀] using haMaster) (by simpa [S₀] using hbMaster) hleft (by
        intro k hk hk93 hk110
        have hk127 : k ≠ 127 := by intro he; subst k; norm_num at hk
        simpa [S₀,hk127] using hblank k hk hk93 hk110)
      (by simpa [S₀] using hsrc) (by simpa [S₀] using h129) (by simpa [S₀] using h133)
      (by simpa [S₀] using hwidth) (by
        intro k hk
        have hk127 : k ≠ 127 := by intro he; subst k; norm_num at hk
        simpa [S₀,hk127] using hfresh k hk)
  have h128 : S.R 128 = [] := by
    have hh := hmasters (128,102) (by simp [groupHeaderCopies])
    exact List.eq_nil_of_length_eq_zero (by simpa [groupHeaderValue] using hh)
  let E' := scatterRows (L*w) E (ys++S.R 93) (haloScatterGaps s t band a b L w)
  have hframe' : S₁.R = keyLoopR S.R keyTail cs (E'++outputTail) := by
    change S₁.R = publishedClassR (Function.update (Function.update S.R 127 cs) 126 keyTail) (E'++outputTail) at hframe
    exact hframe.trans (keyLoopR_step S.R keyTail cs (E'++outputTail) h128 h129 (hfresh 140 (by simp)))
  have hE' : E.length = s*w := hE
  have hys : ys.val.length = B*(L*w) := by simpa only [Nat.mul_assoc] using hylen
  have hX : B*(L*w) ≤ (ys++S.R 93).length := by simp only [List.length_append]; omega
  have hf := haloScatterGaps_fits s t band a b L w E hE'.ge
  have hlen : E'.length = s*w := by
    rw [length_scatterRows (L*w) E (ys++S.R 93) (haloScatterGaps s t band a b L w) hf
      (by simpa only [haloScatterGaps_length] using hX)]
    exact hE'
  have hcount₁ : S₁.R 127 = cs := by simpa [keyLoopR] using congrArg (fun R => R 127) hframe'
  have hp := Exec.act (body := embTab groupReg body) (peekR 127) (mk v₁ S₁)
  rw [peekR_run,hcount₁] at hp
  refine ⟨{ v₁ with flag := cs.head?.isSome },S₁,n₁+2,E',hu₁,rfl,by omega,
    ?_,hi₁,ho₁,hl₁,hlen,hframe',herror,?_,?_⟩
  · have hePop : Exec (embTab groupReg body)
        (.act (.pop (.rt 127) (fun v _ => v) .done)) (mk v S) 1 (mk v S₀) :=
      hpop ▸ Exec.act (body := embTab groupReg body) (.pop (.rt 127) (fun v _ => v) .done) _
    have hpopNative : mnNativePushBound 0
        (.act (.pop (.rt 127) (fun v _ => v) .done) : Pr P₀ 144 Q A U) := Nat.zero_le _
    have hpeekNative : mnNativePushBound 0 (.act (peekR (127 : Fin 144)) : Pr P₀ 144 Q A U) := by
      simp [peekR,mnNativePushBound,mnActPush]
    have htPop := mn_native_exec_within hePop 0 hpopNative 0 _ (Nat.le_refl _)
    have htPeek := mn_native_exec_within hp 0 hpeekNative 0 _ (Nat.le_refl _)
    have ht := mn_seq_within_add htPop (mn_seq_within_add he₁ htPeek)
    have ht' := ht.mono (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        processHaloLengthKeyWorkspace J R K p l L s t u target rhsExp V a b) (by
      intro d z hz
      omega)
    exact ht'.cast (by omega) rfl
  · intro K hKL n j hj
    have h132 : S₁.R 132 = E'++outputTail := by simpa [keyLoopR] using congrArg (fun R => R 132) hframe'
    rw [h132,hdst]
    change publishedCellRead q w (0 : ZMod s)
      (scatterRows (L*w) E (ys++S.R 93) (haloScatterGaps s t band a b L w)++outputTail) j = _
    rw [← scatterRows_append (L*w) (haloScatterGaps s t band a b L w) E (ys++S.R 93) outputTail hf]
    apply haloScatterRows_preserves_class t band a b L K q w hKL.symm (E++outputTail) (ys++S.R 93)
      (by simp only [List.length_append]; omega) hX n j hj

  · intro hBounded
    exact haloScatterRows_range s t band a b L E (S.R 93) ys hBounded hylen

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
