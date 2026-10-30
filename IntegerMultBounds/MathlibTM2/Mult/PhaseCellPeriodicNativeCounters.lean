module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace

/-! Generate the retained arithmetic counters inside the packed bank, preserving
its factors and all source, coefficient-page and binary-geometry spectators. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

theorem periodicNativeCounters_exec {Q A precision q w s t u band a b W N : ℕ}
    {P U : Type} {body : P → Pr P 242 Q A U}
    (hw5 : 5 ≤ w) (hqw : q+4 ≤ w) (raw : List (Fin (A+4)))
    (v : HS 242 Q A U) (S : Stacks 242 A)
    (hready : CouplingReady precision q w s t u band a b raw
      (embStk (Fin.castLE (by decide : 117 ≤ 242)) S))
    (hbank : PackedPreparedBank q w W N S) :
    let e : Fin 117 → Fin 242 := Fin.castLE (by decide)
    let T := embStk e S
    let G := embOvr e ({T with R := counterR q w T.R} : Stacks 117 A).get S
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareCost q w+6*q+4*band+10 ∧
      Exec body (embProg e Empty.elim couplingReadiness) (mk v S) n (mk v' G) ∧
      RetainedCouplingReady precision q w s t u band a b raw (embStk e G) ∧
      PackedPreparedBank q w W N G ∧
      (∀ k : Fin 242, 96 ≤ k.val → G.R k = S.R k) ∧
      ∀ bo hf df, PackedBoundaryFactorPages bo hf df S → PackedBoundaryFactorPages bo hf df G := by
  dsimp only
  let e : Fin 117 → Fin 242 := Fin.castLE (by decide)
  let T := embStk e S
  let G := embOvr e ({T with R := counterR q w T.R} : Stacks 117 A).get S
  have hinj : Function.Injective e := by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin 242 => k.val) he)
  obtain ⟨v₁,n,hu₁,hn,he₁,hr⟩ := retainedCouplingCounters_exec
    (body := fun f : Empty => nomatch f) q w hw5 hqw raw (embDn e v) T hready
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun f => nomatch f) he₁ v rfl S rfl
  have hframe (k : Fin 242) (hk : k.val < 64 ∨ 96 ≤ k.val) : G.R k = S.R k := by
    by_cases hlo : k.val < 117
    · let i : Fin 117 := ⟨k.val,hlo⟩
      have hei : e i = k := Fin.ext rfl
      have hoff (r : CR) : i ≠ cr r := by
        intro he
        have hv := congrArg (fun j : Fin 117 => j.val) he
        have hb := cr_range r
        change k.val = (cr r).val at hv
        omega
      have hh := embOvr_get hinj ({T with R := counterR q w T.R} : Stacks 117 A).get S (.rt i)
      change G.R (e i) = (counterR q w T.R i).map id at hh
      simp only [List.map_id,counterR,Function.update_of_ne (hoff .nn),
        Function.update_of_ne (hoff .pn),Function.update_of_ne (hoff .wn)] at hh
      change G.R (e i) = S.R (e i) at hh
      simpa only [hei] using hh
    · exact (embOvr_off ({T with R := counterR q w T.R} : Stacks 117 A).get S
        (by intro i he
            have hv := congrArg (fun j : Fin 242 => j.val) he
            have hi := i.isLt
            change i.val = k.val at hv
            omega)).2
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂,?_,?_,?_,?_⟩
  · rw [embStk_ovr hinj]
    exact hr
  · apply hbank.of_runtime_frame (F := G) (embOvr_right_left S _)
    · intro k hk; exact hframe k (Or.inl hk)
    · exact hframe 119 (Or.inr (by decide))
    · intro k hk _; exact hframe k (Or.inr (by omega))
  · intro k hk; exact hframe k (Or.inr hk)
  · intro bo hf df hpages
    exact hpages.of_solution_frame (fun k hk _ => hframe k (Or.inr (by omega)))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
