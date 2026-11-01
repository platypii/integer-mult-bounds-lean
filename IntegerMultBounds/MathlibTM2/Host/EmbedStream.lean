module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Stream-only frames survive register-bank embedding, with unchanged time. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack

/-- Extending a bank commutes with changing one of its owned registers. -/
theorem embExt_update {T T' : ℕ} {β : Type} (e : Fin T → Fin T') (he : Function.Injective e)
    (f : Fin T → β) (g : Fin T' → β) (i : Fin T) (x : β) :
    embExt e (Function.update f i x) g = Function.update (embExt e f g) (e i) x := by
  funext j
  by_cases hj : ∃ k, e k = j
  · obtain ⟨k,rfl⟩ := hj
    rw [embExt_apply he]
    by_cases hk : k = i
    · subst k; simp
    · rw [Function.update_of_ne hk,Function.update_of_ne (fun h => hk (he h)),embExt_apply he]
  · have hoff : ∀ k, e k ≠ j := by simpa using hj
    rw [embExt_off _ _ hoff,Function.update_of_ne (hoff i).symm,embExt_off _ _ hoff]

theorem embExt_update_stream {T T' A : ℕ} (e : Fin T → Fin T') (he : Function.Injective e)
    (R : Fin T' → List (Fin (A + 4))) (str : Fin T) (out : List (Fin (A + 4))) :
    embExt e (Function.update (R ∘ e) str out) R = Function.update R (e str) out := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [embExt_apply he]
    by_cases hi : i = str
    · subst i; simp
    · simp [Function.update_of_ne hi, Function.update_of_ne (fun h => hi (he h))]
  · have hoff : ∀ i, e i ≠ j := by simpa using hj
    rw [embExt_off _ _ hoff, Function.update_of_ne (hoff str).symm]

theorem embOvr_stream {T T' A : ℕ} (e : Fin T → Fin T') (he : Function.Injective e)
    (S : Stacks T' A) (str : Fin T) (out : List (Fin (A + 4))) :
    embOvr e ({ embStk e S with R := Function.update (embStk e S).R str out } : Stacks T A).get S =
      { S with R := Function.update S.R (e str) out } := by
  have hL : embExt e (S.L ∘ e) S.L = S.L := embExt_comp (e := e) S.L
  have hR := embExt_update_stream e he S.R str out
  simp only [embOvr, embStk, Stacks.get, hL, hR]

/-- Two changed streams retain a literal ambient frame under placement. -/
theorem embOvr_two_streams {T T' A : ℕ} (e : Fin T → Fin T') (he : Function.Injective e)
    (S : Stacks T' A) (src dst : Fin T) (input output : List (Fin (A+4))) :
    embOvr e ({embStk e S with R := (Function.update
      (Function.update (embStk e S).R src input) dst output)} : Stacks T A).get S =
      {S with R := Function.update (Function.update S.R (e src) input) (e dst) output} := by
  have hL : embExt e (S.L ∘ e) S.L = S.L := embExt_comp (e := e) S.L
  have hR : embExt e (Function.update (Function.update (S.R ∘ e) src input) dst output) S.R =
      Function.update (Function.update S.R (e src) input) (e dst) output := by
    rw [embExt_update e he,embExt_update_stream e he]
  simp only [embOvr,embStk,Stacks.get,hL,hR]

/-- Reading a changed shared stream back through the embedding changes only the
small program's stream. This supplies the next phase's exact initial state. -/
theorem embStk_update_stream {T T' A : ℕ} (e : Fin T → Fin T') (he : Function.Injective e)
    (S : Stacks T' A) (str : Fin T) (out : List (Fin (A + 4))) :
    embStk e { S with R := Function.update S.R (e str) out } =
      { embStk e S with R := Function.update (embStk e S).R str out } := by
  have hR : Function.update S.R (e str) out ∘ e = Function.update (S.R ∘ e) str out := by
    funext i
    by_cases hi : i = str
    · subst i; simp
    · simp [Function.update_of_ne hi, Function.update_of_ne (fun h => hi (he h))]
  simp only [embStk, hR]

/-- Lift an actual stream-only execution into a larger bank. The procedure-table
condition is the ordinary embedding condition, and no execution is postulated. -/
theorem exec_emb_stream {T T' Q A : ℕ} {U P P' : Type}
    (e : Fin T → Fin T') (he : Function.Injective e) (ι : P → P')
    (body : P → Pr P T Q A U) (body' : P' → Pr P' T' Q A U)
    (hbody : ∀ f, body' (ι f) = embProg e ι (body f))
    (p : Pr P T Q A U) (v : HS T' Q A U) (S : Stacks T' A)
    (v₁ : HS T Q A U) (m : ℕ) (str : Fin T) (out : List (Fin (A + 4)))
    (h : Exec body p (mk (embDn e v) (embStk e S)) m
      (mk v₁ { embStk e S with R := Function.update (embStk e S).R str out })) :
    ∃ v', v'.user = v₁.user ∧ Exec body' (embProg e ι p) (mk v S) m
      (mk v' { S with R := Function.update S.R (e str) out }) := by
  obtain ⟨v', _, hu, he'⟩ := exec_emb_ovr he hbody h v rfl S rfl
  rw [embOvr_stream e he S str out] at he'
  exact ⟨v', hu, he'⟩

end IntegerMultBounds.MathlibTM2.Host
