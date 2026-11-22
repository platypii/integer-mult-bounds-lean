module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepBlockRouting

/-! Enter and leave contiguous inherited-block order on an enclosing tape bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host CompactRows
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem sweepHostTranspose_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 8 ↪ Fin T) (middle : Pr P T Q prime U) :
    ∃ program : Pr P T Q prime U, ∀ w B K, 0 < B → 0 < K →
    let A := (prime^w)^16
    let labels := prime^(64*(w*64))
    ∀ (x y : Fin (A*(B*K)) → Fin (prime+4)) (record row : List (Fin (prime+4))) (cost : ℕ)
      (u : HS T Q prime U) (S : Stacks T prime), record.length = K → row.length = B*K →
    embStk bank S = transposeStacks (embStk bank S) [] (List.ofFn x) [] record row →
    (∀ (v : HS T Q prime U) (F : Stacks T prime),
      F.R (bank 0) = List.ofFn (compactTranspose x) →
      (∀ j, (∀ i, bank i ≠ j) → F.R j = S.R j) →
      ∃ z l, z.user = v.user ∧ l ≤ cost ∧ Exec body middle (mk v F) l
        (mk z {F with R := Function.update F.R (bank 0) (List.ofFn (compactTranspose y))})) →
    ∃ z t, z.user = u.user ∧ t ≤ cost+104*(A*(B*labels*K))+4 ∧ Exec body program
      (mk u S) t (mk z {S with R := Function.update S.R (bank 6) (List.ofFn y)}) := by
  let enter : Pr Empty 8 Q prime U := .seq (.act (peekR 6)) transposeLoop
  let leave : Pr Empty 8 Q prime U := .seq (.act (peekR 3)) returnTransposeLoop
  refine ⟨.seq (embProg bank Empty.elim enter) (.seq middle (embProg bank Empty.elim leave)),?_⟩
  intro w B K hb hk A labels x y record row cost u S len width start run
  obtain ⟨v,_,k,rfl,hv,trans,hk₁⟩ := remainderCompactTranspose_exec (P := Empty) Empty.elim w B K hb hk x
    (embStk bank S) (embDn bank u) record row len width
  obtain ⟨a,F,forward,_,ha,view,off⟩ := exec_emb (ι := (Empty.elim : Empty → P)) (body' := body)
    bank.injective (fun e => nomatch e) trans u rfl S start
  have port (i : Fin 8) := congrArg (fun D : Stacks 8 prime => D.R i) view
  obtain ⟨b,l,hb',hl,convert⟩ := run a F (port 0) (fun j hj => (off j hj).2)
  let G := {F with R := Function.update F.R (bank 0) (List.ofFn (compactTranspose y))}
  have viewinp := congrArg Stacks.inp view
  have viewout := congrArg Stacks.out view
  have viewL := congrArg Stacks.L view
  have prepared : embStk bank G = transposeStacks (embStk bank S) (List.ofFn (compactTranspose y)) []
      (List.replicate A record.reverse).flatten record row := by
    refine Stacks.ext viewinp viewout viewL ?_
    funext i
    by_cases h : i = 0
    · subst i; exact Function.update_self ..
    · exact (Function.update_of_ne (bank.injective.ne h) _ _).trans (by fin_cases i <;> first | contradiction | exact port _)
  obtain ⟨c,m,hc,back,hm⟩ := remainderCompactReturn_exec (P := Empty) Empty.elim w B K hb hk (compactTranspose y)
    (embStk bank S) (embDn bank b) record row len
  obtain ⟨z,D,restore,_,hz,endView,endOff⟩ := exec_emb (ι := (Empty.elim : Empty → P)) (body' := body)
    bank.injective (fun e => nomatch e) back b rfl G prepared
  have twice : compactTranspose (compactTranspose y) = y := by
    funext j
    obtain ⟨⟨i,t⟩,rfl⟩ := finProdFinEquiv.surjective j
    obtain ⟨⟨d,k⟩,rfl⟩ := finProdFinEquiv.surjective t
    simp [compactTranspose]
  rw [twice] at endView
  have endViewinp := congrArg Stacks.inp endView
  have endViewout := congrArg Stacks.out endView
  have final : D = {S with R := Function.update S.R (bank 6) (List.ofFn y)} := by
    refine Stacks.ext endViewinp endViewout ?_ ?_
    · funext j
      by_cases h : ∃ i, bank i = j
      · obtain ⟨i,rfl⟩ := h; exact congrArg (fun E : Stacks 8 prime => E.L i) endView
      · have ext := not_exists.mp h; exact ((endOff j ext).1).trans (off j ext).1
    · funext j
      change D.R j = Function.update S.R (bank 6) (List.ofFn y) j
      by_cases h : ∃ i, bank i = j
      · obtain ⟨i,rfl⟩ := h
        have before := congrArg (fun E : Stacks 8 prime => E.R i) start
        have after := congrArg (fun E : Stacks 8 prime => E.R i) endView
        by_cases hi : i = 6
        · subst i; rw [Function.update_self]; exact after
        · rw [Function.update_of_ne (bank.injective.ne hi)]
          exact after.trans (by fin_cases i <;> first | contradiction | exact before.symm)
      · have ext := not_exists.mp h
        rw [Function.update_of_ne (Ne.symm (ext 6))]
        exact ((endOff j ext).2).trans ((Function.update_of_ne (Ne.symm (ext 0)) _ _).trans (off j ext).2)
  rw [final] at restore
  change k ≤ 52*(A*(B*labels*K))+2 at hk₁
  change m ≤ 52*(A*(B*labels*K))+2 at hm
  exact ⟨z,_,hz.trans (hc.trans (hb'.trans (ha.trans hv))),by omega,Exec.seq forward (Exec.seq convert restore)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
