module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Place the fully generated and retired class sweep in a caller. Its empty
procedure type removes any caller procedure-table compatibility obligation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def placedCoreGather (e : Fin 168 → Fin T) : Pr P T Q A U :=
  embProg e Empty.elim (restoredCoreGather (P := Empty))

theorem placedCoreGather_native (e : Fin 168 → Fin T) :
    mnNativePushBound 3 (placedCoreGather (P := P) (Q := Q) (A := A) (U := U) e) :=
  embProg_native e Empty.elim _ restoredCoreGather_native

theorem placedCoreGather_exec_within (e : Fin 168 → Fin T) (he : Function.Injective e) {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (C : ZMod s → GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (h163 : (S.R (e 163)).length = V) (h115 : S.R (e 115) = []) (h103 : S.R (e 103) = []) (h105 : S.R (e 105) = [])
    (hs : S.R (e 145) = binSyms V s) (hw : S.R (e 150) = binSyms V width)
    (hr : S.R (e 152) = binSyms V radius) (hL : S.R (e 165) = binSyms V L) (hz : S.R (e 154) = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = [])
    (hsource : S.R (e 110) = cstream A w (chirpLine s C))
    (hword : (S.R (e 94)).length = w) (hcontrol : S.R (e 91) = []) (horigin : S.R (e 109) = [])
    (hclean : ∀ k ∈ [(92 : Fin 168),93,95,96,97,98,99,100,101,102], S.R (e k) = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168),89,90], S.R (e k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ restoredCoreGatherCost V s width radius L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*restoredCoreGatherCost V s width radius L w) depth (placedCoreGather e) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (e 108)
          (cstream A w (coreGatherPayload width radius L [C]) ++ S.R (e 108)))}) := by
  obtain ⟨v₁,n,hu,hn,hex⟩ := restoredCoreGather_exec_within
    (body := fun f : Empty => nomatch f) hwidth hwide hLfit hwV hvol hA hVpos hgroup C
    (embDn e v) (embStk e S) h163 h115 h103 h105 hs hw hr hL hz hblank h104 h106 h116
    hsource hword hcontrol horigin hclean hfresh depth
  obtain ⟨v',_,hu',hex'⟩ := exec_emb_ovr_within_stock (e := e) he
    (body' := body) (ι := Empty.elim) (fun f => nomatch f) hex v rfl S rfl
  rw [embOvr_stream e he] at hex'
  exact ⟨v',n,hu'.trans hu,hn,hex'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
