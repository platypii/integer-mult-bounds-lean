module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryAssemblyLoop
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Place the generic assembly loop without charging spectator storage twice. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def placedPackedRecoveryAssembly (e : Fin 12 → Fin T) : Pr P T Q A U :=
  embProg e Empty.elim (replicaRecoveryAssemblyLoop (P := Empty))

theorem placedPackedRecoveryAssembly_exec (e : Fin 12 → Fin T) (he : Function.Injective e)
    (t band a N w : ℕ) (hst : s < t) (hfit : a+N ≤ s)
    (rows : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt)))
    (hA : 4 ≤ A) (tailX tailY : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hmaster : S.R (e 0) = couplingSourceIntervalMaskSymbols true A s t band a (a+N) a N)
    (hwidth : (S.R (e 2)).length = w)
    (hX : S.R (e 4) = rows.flatMap (fun row => cstream A w (packedInterval a N row.1))++tailX)
    (hY : S.R (e 5) = rows.flatMap (fun row => cstream A w (packedInterval a N row.2))++tailY)
    (hfresh : ∀ k ∈ ([1,3,6,8,9,11] : List (Fin 12)), S.R (e k) = [])
    (hcount : (S.R (e 10)).length = rows.length) (depth : ℕ) :
    let outputs := rows.map (fun row => cstream A w (packedInterval a N (publicationField t band a (a+N) row.1 row.2)))
    ∃ v' n, v'.user = v.user ∧ n ≤ rows.length*(retainedPackedPublicationMergeCost N w+5)+4 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*retainedPackedPublicationMergeCost N w) depth (placedPackedRecoveryAssembly e) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R (e 5) tailY)
          (e 4) tailX) (e 7) (outputs.reverse.flatten++S.R (e 7)))}) := by
  dsimp only
  let outputs := rows.map (fun row => cstream A w (packedInterval a N (publicationField t band a (a+N) row.1 row.2)))
  obtain ⟨vi,n,hu,hn,hex⟩ := packedRecoveryAssemblyLoop_exec (body := fun z : Empty => nomatch z)
    t band a N w hst hfit rows hA tailX tailY (embDn e v) (embStk e S)
    hmaster hwidth hX hY hfresh hcount depth
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr_within_stock (body' := body) (e := e) (ι := Empty.elim)
    he (fun z => nomatch z) hex v rfl S rfl
  have hstate : embOvr e {embStk e S with R := (Function.update (Function.update (Function.update (embStk e S).R
        5 tailY) 4 tailX) 7 (outputs.reverse.flatten++(embStk e S).R 7))}.get S =
      {S with R := (Function.update (Function.update (Function.update S.R (e 5) tailY)
        (e 4) tailX) (e 7) (outputs.reverse.flatten++S.R (e 7)))} := by
    let C := embStk e S
    let M : Stacks 12 A := {C with R := Function.update C.R 5 tailY}
    let K : Stacks 12 A := {M with R := Function.update M.R 4 tailX}
    change embOvr e {K with R := Function.update K.R 7 (outputs.reverse.flatten++C.R 7)}.get S = _
    rw [embOvr_updR he]
    dsimp only [K]
    rw [embOvr_updR he]
    dsimp only [M]
    rw [embOvr_updR he,embOvr_stk]
    rfl
  exact ⟨v',n,hu'.trans hu,hn,he'.cast rfl (congrArg (mk v') hstate)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
