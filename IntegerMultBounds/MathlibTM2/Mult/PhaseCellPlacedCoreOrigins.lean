module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCoreOrigins
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Place the restoring origin/count pass in the caller bank, including its
exact two-register frame and execution-wide stock bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def placedCoreOrigins (e : Fin 117 → Fin T) : Pr P T Q A U :=
  embProg e Empty.elim (preparedCoreOrigins (P := Empty))

theorem placedCoreOrigins_exec_within (e : Fin 117 → Fin T) (he : Function.Injective e)
    {V s width radius L : ℕ} (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V)
    (hLfit : L < 2^V) (hA : 4 ≤ A) (hV : 0 < V)
    (v : HS T Q A U) (S : Stacks T A) (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V width)
    (hr : S.R (e 34) = binSyms V radius) (hL : S.R (e 35) = binSyms V L) (hz : S.R (e 36) = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedCoreOriginsCost V s width radius L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*preparedCoreOriginsCost V s width radius L) depth (placedCoreOrigins e) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (e 109)
          ((coreGatherIndices s width radius L).flatMap (fun k => binSyms V (coreStart width k-radius))++S.R (e 109)))
          (e 116) (List.replicate (coreGatherIndices s width radius L).length tick))}) := by
  obtain ⟨w,n,hu,hn,hw⟩ := preparedCoreOrigins_exec_within (body := fun f : Empty => nomatch f)
    hwidth hwide hLfit hA hV (embDn e v) (embStk e S) h37 hs hw hr hL hz hblank h104 h106 h116 depth
  obtain ⟨v',_,hu',hex⟩ := exec_emb_ovr_within_stock (e := e) he
    (body' := body) (ι := Empty.elim) (fun f => nomatch f) hw v rfl S rfl
  rw [embOvr_updateR_updateR he] at hex
  exact ⟨v',n,hu'.trans hu,hn,hex⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
