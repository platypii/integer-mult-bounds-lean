module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPayload
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Place the native restoring gather in any caller. The procedure type is
empty, so the caller's procedure table needs no compatibility assumption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def placedReplicaPayload (e : Fin 117 → Fin T) : Pr P T Q A U :=
  embProg e Empty.elim (rawReplicaPayload (P₀ := Empty))

theorem placedReplicaPayload_exec_within (e : Fin 117 → Fin T) (he : Function.Injective e)
    {s : ℕ} (Fs : List (ZMod s → GaussianInt)) (B w p L : ℕ)
    (hcount : Fs.length = B+1) (hwpos : 0 < w) (hLpos : 0 < L) (hfit : p+L ≤ s)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hw : (S.R (e 94)).length = w) (hs : (S.R (e 97)).length = s) (hp : (S.R (e 111)).length = p)
    (hL : (S.R (e 102)).length = L) (hB : (S.R (e 116)).length = Fs.length)
    (hsrc : S.R (e 110) = cstream A w (Fs.flatMap (chirpLine s))++borrowed)
    (hdst : S.R (e 93) = []) (hblank : ∀ k : Fin 117, k.val < 13 → S.R (e k) = [])
    (hfresh : ∀ k ∈ [(91 : Fin 117),92], S.R (e k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rawReplicaPayloadCost w s p L B ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+500*(Fs.length*s*w)) depth
        (placedReplicaPayload e) (mk v S) n (mk v' {S with R := (Function.update S.R (e 93)
          (cstream A w (Fs.map (packedInterval p L)).flatten))}) := by
  obtain ⟨v₁,n,hu,hn,hex⟩ := replicaPayload_exec_within
    (body := fun f : Empty => nomatch f) Fs B w p L hcount hwpos hLpos hfit borrowed
    (embDn e v) (embStk e S) hw hs hp hL hB hsrc hdst hblank hfresh depth
  obtain ⟨v',_,hu',hex'⟩ := exec_emb_ovr_within_stock (e := e) he
    (body' := body) (ι := Empty.elim) (fun f => nomatch f) hex v rfl S rfl
  rw [embOvr_stream e he] at hex'
  exact ⟨v',n,hu'.trans hu,hn,hex'⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
