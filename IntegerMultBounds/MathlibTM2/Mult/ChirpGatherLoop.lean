module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherControl

/-! # One fixed loop for overlapping windows

The invariant records only consumed prefixes and emitted windows. Its proof is structural
in the control packets; no execution premise or generated finite certificate is used.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def gatherControls (A : ℕ) : List ℕ → List (Fin (A + 4))
  | [] => []
  | d :: ds => List.replicate d tick ++ blank :: gatherControls A ds

def gatherRows {A : ℕ} (L : ℕ) (E : List (Fin (A + 4))) : List ℕ → List (Fin (A + 4))
  | [] => []
  | d :: ds => E.take L ++ gatherRows L (E.drop d) ds

def GatherFits {A : ℕ} (L : ℕ) (E : List (Fin (A + 4))) : List ℕ → Prop
  | [] => True
  | d :: ds => L ≤ E.length ∧ d ≤ E.length ∧ GatherFits L (E.drop d) ds

/-- Five observable registers suffice for the loop's accumulated effects. -/
def gatherUpdate (R : Regs T A) (control savedControl src savedSource acc : Fin T)
    (ct cs xs ss ys : List (Fin (A + 4))) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update (Function.update R control ct)
    savedControl (cs ++ R savedControl)) src xs) savedSource (ss ++ R savedSource)) acc (ys ++ R acc)

theorem gatherUpdate_comp {control savedControl src savedSource acc : Fin T}
    (hreg : [control, savedControl, src, savedSource, acc].Nodup) (R : Regs T A)
    (ct cs xs ss ys ct' cs' xs' ss' ys' : List (Fin (A + 4))) :
    gatherUpdate (gatherUpdate R control savedControl src savedSource acc ct cs xs ss ys)
        control savedControl src savedSource acc ct' cs' xs' ss' ys' =
      gatherUpdate R control savedControl src savedSource acc ct' (cs' ++ cs) xs'
        (ss' ++ ss) (ys' ++ ys) := by
  have hreg' := hreg
  regs_ne hreg'
  funext k
  simp only [gatherUpdate, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all only [ne_eq, eq_self,
    not_false_eq_true, List.append_assoc]

@[simp] theorem length_gatherControls (ds : List ℕ) :
    (gatherControls A ds).length = ds.sum + ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [gatherControls, List.length_append, List.length_replicate,
      List.length_cons, List.sum_cons, ih]; omega

theorem length_gatherRows (L : ℕ) (E : List (Fin (A + 4))) (ds : List ℕ)
    (hfit : GatherFits L E ds) : (gatherRows L E ds).length = ds.length * L := by
  induction ds generalizing E with
  | nil => simp [gatherRows]
  | cons d ds ih =>
    rw [gatherRows, List.length_append, List.length_take, Nat.min_eq_left hfit.1,
      ih _ hfit.2.2, List.length_cons]
    ring

def gatherLoopBody (control savedControl advance window src acc current savedSource buf tmp : Fin T) :
    Pr P T Q A U :=
  .seq (gatherPacket control savedControl advance window src acc current savedSource buf tmp)
    (.act (peekR control))

/-- The whole sweep, before reversing the accumulated output and saved prefixes. -/
theorem gatherLoop_exec {control savedControl advance window src acc current savedSource buf tmp : Fin T}
    (hreg : [control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp].Nodup)
    (L : ℕ) (ds : List ℕ) (E : List (Fin (A + 4))) (hfit : GatherFits L E ds)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R control = gatherControls A ds) (hs : S.R src = E) (hw : (S.R window).length = L)
    (hclean : ∀ k ∈ [advance, current, buf, tmp], S.R k = [])
    (hflag : v.flag = (gatherControls A ds).head?.isSome) :
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (gatherLoopBody control savedControl advance window src acc current savedSource buf tmp))
        (mk v S) (ds.length * (12 * L + 23) + 8 * ds.sum + 1)
        (mk v' { S with R := (gatherUpdate S.R control savedControl src savedSource acc []
          (gatherControls A ds).reverse (E.drop ds.sum) (E.take ds.sum).reverse
          (gatherRows L E ds).reverse) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have heffect : [control, savedControl, src, savedSource, acc].Nodup := by regs_nodup
  induction ds generalizing E v S with
  | nil =>
    have he := Exec.loop_false (body := body)
      (p := gatherLoopBody control savedControl advance window src acc current savedSource buf tmp)
      (s := mk v S) (by simpa [gatherControls] using hflag)
    refine ⟨v, rfl, he.cast (by simp) ?_⟩
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [gatherUpdate, gatherControls, gatherRows, List.sum_nil, List.drop_zero,
      List.take_zero, List.reverse_nil, List.nil_append, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all only [ne_eq, eq_self, not_false_eq_true, gatherControls]
  | cons d ds ih =>
    obtain ⟨v₁, hu₁, he₁⟩ := gatherPacket_exec (body := body) hreg d (gatherControls A ds)
      (E.take L) (E.drop L) (E.take d) (E.drop d) v S hc
      (by simpa using hs) (by simpa using hs)
      (by rw [List.length_take, Nat.min_eq_left hfit.1]; exact hw)
      (by rw [List.length_take, Nat.min_eq_left hfit.2.1])
      (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
    let S₁ : Stacks T A := { S with R := (gatherUpdate S.R control savedControl src savedSource acc
      (gatherControls A ds) (blank :: List.replicate d tick) (E.drop d) (E.take d).reverse (E.take L).reverse) }
    have stable (k : Fin T) (hkc : k ≠ control) (hksc : k ≠ savedControl)
        (hks : k ≠ src) (hkss : k ≠ savedSource) (hka : k ≠ acc) : S₁.R k = S.R k := by
      simp [S₁, gatherUpdate, hkc, hksc, hks, hkss, hka]
    have hclean₁ : ∀ k ∈ [advance, current, buf, tmp], S₁.R k = [] := by
      intro k hk
      have hz := hclean k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;>
        rw [stable _ (by first | assumption | (apply Ne.symm; assumption))
          (by first | assumption | (apply Ne.symm; assumption))
          (by first | assumption | (apply Ne.symm; assumption))
          (by first | assumption | (apply Ne.symm; assumption))
          (by first | assumption | (apply Ne.symm; assumption))] <;> exact hz
    have hc₁ : S₁.R control = gatherControls A ds := by
      simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₁, gatherUpdate]
    have hs₁ : S₁.R src = E.drop d := by
      simp (disch := first | assumption | (apply Ne.symm; assumption)) [S₁, gatherUpdate]
    have hp := Exec.act (body := body) (peekR control) (mk v₁ S₁)
    rw [peekR_run, hc₁] at hp
    obtain ⟨v₂, hu₂, he₂⟩ := ih (E.drop d) hfit.2.2
      { v₁ with flag := (gatherControls A ds).head?.isSome } S₁ hc₁ hs₁
      (by rw [stable _ (by first | assumption | (apply Ne.symm; assumption))
        (by first | assumption | (apply Ne.symm; assumption)) (by assumption) (by assumption) (by assumption)]; exact hw)
      hclean₁ rfl
    have hstep : Exec body (gatherLoopBody control savedControl advance window src acc current savedSource buf tmp)
        (mk v S) (12 * L + 8 * d + 22)
        (mk { v₁ with flag := (gatherControls A ds).head?.isSome } S₁) := by
      exact (Exec.seq he₁ hp).cast (by rw [List.length_take, Nat.min_eq_left hfit.1]) rfl
    refine ⟨v₂, hu₂.trans hu₁, (Exec.loop_true ?_ hstep he₂).cast (by simp only [List.length_cons, List.sum_cons]; ring) ?_⟩
    · simpa [gatherControls] using hflag
    · congr 1
      ext1
      · rfl
      · rfl
      · rfl
      change gatherUpdate (gatherUpdate S.R control savedControl src savedSource acc _ _ _ _ _)
        control savedControl src savedSource acc _ _ _ _ _ = _
      rw [gatherUpdate_comp heffect]
      simp only [gatherControls, gatherRows, List.sum_cons, List.drop_drop, List.take_add,
        List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
        List.singleton_append]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
