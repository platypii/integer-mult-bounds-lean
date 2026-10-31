module

public import IntegerMultBounds.MathlibTM2.Fast.RingRecordStock

/-! The ring-product record loop retains all operand archives and completed
output, but uses only one packed-record scratch allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Host.WordCmd IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Tp
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

private theorem opWords_append (xs ys : List (List (List Bool × List Bool))) :
    opWords (xs++ys) = opWords xs++opWords ys := by
  simp only [opWords,List.map_append,List.flatten_append]

/-- Persistent state after exactly k record pairs. -/
def ringRecordBoundary (Wd r w s N : ℕ) (τ : Fin 𝕌 → WTape)
    (ps : List (List (List Bool × List Bool) × List (List Bool × List Bool)))
    (Lf Lg : List (List Bool)) (acc : List Bool) (k : ℕ) : Fin 𝕌 → WTape :=
  Function.update (Function.update (Function.update τ
    iP ⟨(opWords ((ps.take k).map Prod.fst)).reverse++Lf,opWords ((ps.drop k).map Prod.fst)⟩)
    iL ⟨(opWords ((ps.take k).map Prod.snd)).reverse++Lg,opWords ((ps.drop k).map Prod.snd)⟩)
    zO ⟨[acc++(ps.take k).flatMap (fun q => ((ringWords Wd r w s N q.1 q.2).map List.reverse).flatten)],[]⟩

theorem ringRecordLoop_exec_within (ι : Fin 𝕌 → Fin T) (hι : Function.Injective ι)
    (hQ : cmdStates recStep ≤ Q) {Wd r w s N : ℕ} (hr : 1 ≤ r)
    (ps : List (List (List Bool × List Bool) × List (List Bool × List Bool)))
    (τ : Fin 𝕌 → WTape) (Lf Lg : List (List Bool)) (acc : List Bool)
    (hq : ∀ q ∈ ps, q.1.length = r ∧ q.2.length = r ∧
      (∀ p ∈ q.1, p.1.length = w ∧ p.2.length = w) ∧
      (∀ p ∈ q.2, p.1.length = w ∧ p.2.length = w))
    (hR : RecReady Wd r w s N τ) (hW : τ iW = reg (ones (2*r)))
    (hP : τ iP = ⟨Lf,opWords (ps.map Prod.fst)⟩)
    (hL : τ iL = ⟨Lg,opWords (ps.map Prod.snd)⟩) (hZ : τ zO = ⟨[acc],[]⟩)
    (v : HS T Q A U) (S : Stacks T A) (depth : ℕ) :
    let output := ps.flatMap (fun q => ((ringWords Wd r w s N q.1 q.2).map List.reverse).flatten)
    ∃ v' steps, v'.user = v.user ∧ steps ≤ ps.length*(3*(ringRecordCost Wd r w s N+1)+2)+2 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v (place S ι τ))+2*ps.length*r*w+depth+
        mnProgPush (tcompile (P := P) (Q := Q) (A := A) (U := U) ι recStep)*
          (3*(ringRecordCost Wd r w s N+1))) depth (tcompile ι recLoop)
        (mk v (place S ι τ)) steps
        (mk v' (place S ι (Function.update (Function.update (Function.update τ
          iP ⟨(opWords (ps.map Prod.fst)).reverse++Lf,[]⟩)
          iL ⟨(opWords (ps.map Prod.snd)).reverse++Lg,[]⟩) zO ⟨[acc++output],[]⟩))) := by
  dsimp only
  have hPL : (iP : Fin 𝕌) ≠ iL := by decide
  have hPZ : (iP : Fin 𝕌) ≠ zO := by decide
  have hLZ : (iL : Fin 𝕌) ≠ zO := by decide
  have hWP : (iW : Fin 𝕌) ≠ iP := by decide
  have hWL : (iW : Fin 𝕌) ≠ iL := by decide
  have hWZ : (iW : Fin 𝕌) ≠ zO := by decide
  let σ := ringRecordBoundary Wd r w s N τ ps Lf Lg acc
  let output := fun q : List (List Bool × List Bool) × List (List Bool × List Bool) =>
    ((ringWords Wd r w s N q.1 q.2).map List.reverse).flatten
  have htotal : (ps.flatMap output).length ≤ 2*ps.length*r*w := by
    have h := ringRecordOutput_length_le Wd r w s N ps
    simpa only [output,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
  have hσP (k : ℕ) : σ k iP =
      ⟨(opWords ((ps.take k).map Prod.fst)).reverse++Lf,opWords ((ps.drop k).map Prod.fst)⟩ := by
    simp only [σ,ringRecordBoundary,Function.update_of_ne hPZ,Function.update_of_ne hPL,Function.update_self]
  have hσL (k : ℕ) : σ k iL =
      ⟨(opWords ((ps.take k).map Prod.snd)).reverse++Lg,opWords ((ps.drop k).map Prod.snd)⟩ := by
    simp only [σ,ringRecordBoundary,Function.update_of_ne hLZ,Function.update_self]
  have hσZ (k : ℕ) : σ k zO = ⟨[acc++(ps.take k).flatMap output],[]⟩ := rfl
  have hσ0 : σ 0 = τ := by
    funext j
    by_cases hPi : j = iP
    · subst j
      rw [hσP]
      simpa only [List.take_zero,List.drop_zero,List.map_nil,show opWords [] = [] from rfl,
        List.reverse_nil,List.nil_append] using hP.symm
    by_cases hLi : j = iL
    · subst j
      rw [hσL]
      simpa only [List.take_zero,List.drop_zero,List.map_nil,show opWords [] = [] from rfl,
        List.reverse_nil,List.nil_append] using hL.symm
    by_cases hZi : j = zO
    · subst j
      rw [hσZ]
      simpa only [List.take_zero,List.flatMap_nil,List.append_nil] using hZ.symm
    simp only [σ,ringRecordBoundary,Function.update_of_ne hPi,Function.update_of_ne hLi,Function.update_of_ne hZi]
  have hstock (k : ℕ) : wordBankStock (σ k) = wordBankStock τ+((ps.take k).flatMap output).length := by
    have hsplit (f : (List (List Bool × List Bool) × List (List Bool × List Bool)) → List (List Bool × List Bool)) :
        opWords (ps.map f) = opWords ((ps.take k).map f)++opWords ((ps.drop k).map f) := by
      rw [←opWords_append,←List.map_append,List.take_append_drop]
    have hp := hP
    have hl := hL
    rw [hsplit Prod.fst] at hp
    rw [hsplit Prod.snd] at hl
    exact ringRecord_boundary_stock τ _ _ Lf _ _ Lg acc ((ps.take k).flatMap output) hp hl hZ
  have hstep (k : ℕ) (hk : k < ps.length) :
      Schoenhage.Runs recStep (σ k) (· = σ (k+1)) (ringRecordCost Wd r w s N) := by
    let q := ps[k]
    obtain ⟨h1,h2,h3,h4⟩ := hq q (List.getElem_mem hk)
    have hRk : RecReady Wd r w s N (σ k) :=
      ((hR.update_free (Or.inl rfl) _).update_free (Or.inr (Or.inl rfl)) _).update_free
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) _
    have hWk : σ k iW = reg (ones (2*r)) := by
      simpa only [σ,ringRecordBoundary,Function.update_of_ne hWP,Function.update_of_ne hWL,
        Function.update_of_ne hWZ] using hW
    have hp : σ k iP = ⟨(opWords ((ps.take k).map Prod.fst)).reverse++Lf,
        (flat q.1).map List.reverse++opWords ((ps.drop (k+1)).map Prod.fst)⟩ := by
      rw [hσP,List.drop_eq_getElem_cons hk]
      simp only [opWords,List.map_cons,List.flatten_cons,q]
    have hl : σ k iL = ⟨(opWords ((ps.take k).map Prod.snd)).reverse++Lg,
        (flat q.2).map List.reverse++opWords ((ps.drop (k+1)).map Prod.snd)⟩ := by
      rw [hσL,List.drop_eq_getElem_cons hk]
      simp only [opWords,List.map_cons,List.flatten_cons,q]
    apply (runs_recStep (σ k) hRk hWk h1 h2 h3 h4 hp hl (hσZ k)).mono ?_ le_rfl
    intro τ' hτ'
    rw [hτ']
    funext j
    by_cases hPi : j = iP
    · subst j
      simp only [σ,ringRecordBoundary,Function.update_of_ne hPZ,Function.update_of_ne hPL,Function.update_self]
      rw [List.take_succ_eq_append_getElem hk]
      simp only [opWords,List.map_append,List.map_cons,List.map_nil,List.flatten_append,
        List.flatten_cons,List.flatten_nil,List.append_nil,List.reverse_append,List.append_assoc,q]
    by_cases hLi : j = iL
    · subst j
      simp only [σ,ringRecordBoundary,Function.update_of_ne hLZ,Function.update_self]
      rw [List.take_succ_eq_append_getElem hk]
      simp only [opWords,List.map_append,List.map_cons,List.map_nil,List.flatten_append,
        List.flatten_cons,List.flatten_nil,List.append_nil,List.reverse_append,List.append_assoc,q]
    by_cases hZi : j = zO
    · subst j
      simp only [σ,ringRecordBoundary,Function.update_self]
      rw [List.take_succ_eq_append_getElem hk]
      simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc,output,q]
    simp only [σ,ringRecordBoundary,Function.update_of_ne hPi,Function.update_of_ne hLi,Function.update_of_ne hZi]
  have hne (k : ℕ) (hk : k < ps.length) : (σ k iP).right ≠ [] := by
    have hlen := (hq ps[k] (List.getElem_mem hk)).1
    have hl : ((flat ps[k].1).map List.reverse).length = 2*r := by simp [length_flat,hlen]
    rw [hσP,List.drop_eq_getElem_cons hk]
    simp only [opWords,List.map_cons,List.flatten_cons]
    intro hempty
    have he := List.append_eq_nil_iff.mp hempty
    rw [he.1] at hl
    simp only [List.length_nil] at hl
    omega
  have hend : (σ ps.length iP).right = [] := by simp [hσP,opWords]
  obtain ⟨v',steps,hu,hn,ht⟩ := tcompile_loop_runs_within (body := body) hι iP recStep ps.length
    (ringRecordCost Wd r w s N) (mnSize (mk v (place S ι τ))+2*ps.length*r*w) σ
    hne hend hstep hQ S (by
      intro k hk vi
      have hb := place_stock_balance ι hι vi v S (σ k) τ
      rw [hstock k] at hb
      have hpref : ((ps.take k).flatMap output).length ≤ (ps.flatMap output).length := by
        have he := congrArg (fun xs => (xs.flatMap output).length) (List.take_append_drop k ps)
        simp only [List.flatMap_append,List.length_append] at he
        omega
      omega) v depth
  rw [hσ0] at ht
  have hfinal : σ ps.length = Function.update (Function.update (Function.update τ
      iP ⟨(opWords (ps.map Prod.fst)).reverse++Lf,[]⟩)
      iL ⟨(opWords (ps.map Prod.snd)).reverse++Lg,[]⟩) zO ⟨[acc++ps.flatMap output],[]⟩ := by
    dsimp only [σ,ringRecordBoundary]
    simp only [List.take_length,List.drop_length,List.map_nil,show opWords [] = [] from rfl]
    rfl
  rw [hfinal] at ht
  exact ⟨v',steps,hu,hn,ht⟩

end IntegerMultBounds.MathlibTM2.Fast
