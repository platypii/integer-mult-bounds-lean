module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWeightWidth
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Reuse the existing weight-width generator at arbitrary caller registers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem generateWeightWidth_native :
    mnNativePushBound 18 (generateWeightWidth (P₀ := P) (Q := Q) (A := A) (U := U)) := by
  simp [generateWeightWidth,ucopy,umul,umulSym,unarySize,ldrLoop,ldrStep,ldrHalfFx,ldrBitAct,
    uclear,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

def placedWeightWidth (e : Fin 117 → Fin T) : Pr P T Q A U :=
  embProg e Empty.elim (generateWeightWidth (P₀ := Empty))

theorem placedWeightWidth_exec_within (e : Fin 117 → Fin T) (he : Function.Injective e)
    (precision q w t u : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hP : (S.R (e 114)).length = precision) (hq : (S.R (e 112)).length = q)
    (hw : (S.R (e 94)).length = w) (ht : (S.R (e 98)).length = t) (hu : (S.R (e 99)).length = u)
    (hblank : ∀ k ∈ [(0 : Fin 117),1,2,3,4,104,115], S.R (e k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ weightWidthCost precision q w t u ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        18*weightWidthCost precision q w t u) depth (placedWeightWidth e) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (e 115)
          (List.replicate (weightWorkspaceWidth precision q w t u) tick))}) := by
  obtain ⟨v₁,n,hu₁,hn,he₁⟩ := generateWeightWidth_exec (body := fun f : Empty => nomatch f)
    precision q w t u (embDn e v) (embStk e S) hP hq hw ht hu hblank
  have hw₁ := mn_native_exec_within he₁ 18 generateWeightWidth_native depth
    (mnSize (Host.mk (embDn e v) (embStk e S))+depth+18*weightWidthCost precision q w t u) (by omega)
  obtain ⟨v',_,hu',hex⟩ := exec_emb_ovr_within_stock (e := e) he
    (body' := body) (ι := Empty.elim) (fun f => nomatch f) hw₁ v rfl S rfl
  rw [embOvr_stream e he] at hex
  exact ⟨v',n,hu'.trans hu₁,hn,hex⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
