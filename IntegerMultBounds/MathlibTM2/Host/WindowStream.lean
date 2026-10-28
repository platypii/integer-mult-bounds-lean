module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! A linear window filter driven by two decreasing unary counters. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {U P : Type}

def windowWord {α : Type} (inside outside : α → α) : ℕ → ℕ → List α → List α
  | _,_,[] => []
  | a,b,x::xs => (if a = 0 ∧ 0 < b then inside x else outside x)::windowWord inside outside (a-1) (b-1) xs

theorem windowWord_length {α : Type} (inside outside : α → α) (a b : ℕ) (xs : List α) :
    (windowWord inside outside a b xs).length = xs.length := by
  induction xs generalizing a b with
  | nil => rfl
  | cons x xs ih => simp [windowWord,ih]

theorem windowWord_map_range {α : Type} (inside outside : α → α) (a b n : ℕ) (f : ℕ → α) :
    windowWord inside outside a b ((List.range n).map f) =
      (List.range n).map (fun j => if a ≤ j ∧ j < b then inside (f j) else outside (f j)) := by
  induction n generalizing a b f with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ_eq_map,List.map_cons,List.map_map,windowWord]
    congr 1
    · simp
    · rw [ih]
      apply List.map_congr_left
      intro j hj
      have he : (a-1 ≤ j ∧ j < b-1) ↔ (a ≤ j+1 ∧ j+1 < b) := by omega
      simp only [Function.comp_apply,he]

def windowStep (lo hi src dst : Fin T) (inside outside : Fin (A+4) → Fin (A+4)) (k : Act T Q A U) : Act T Q A U :=
  .pop (.rt lo) (fun v o => {v with flag := o.isNone})
    (.pop (.rt hi) (fun v o => {v with flag := v.flag && o.isSome})
      (.pop (.rt src) (fun v o => {v with sym := o})
        (.push (.rt dst) (fun v => if v.flag then inside (v.sym.getD blank) else outside (v.sym.getD blank)) k)))

def windowStepFx (lo hi src dst : Fin T) (inside outside : Fin (A+4) → Fin (A+4)) :
    Fin (A+4) → Regs T A → Regs T A := fun _ R =>
  Function.update (Function.update (Function.update (Function.update R lo (R lo).tail) hi (R hi).tail)
    src (R src).tail) dst
      ((if (R lo).head?.isNone && (R hi).head?.isSome then inside ((R src).head?.getD blank) else outside ((R src).head?.getD blank))::R dst)

theorem windowStep_fx {lo hi src dst : Fin T} (hreg : [lo,hi,src,dst].Nodup)
    (inside outside : Fin (A+4) → Fin (A+4)) : RegFx (windowStep (Q := Q) (U := U) lo hi src dst inside outside)
      (windowStepFx lo hi src dst inside outside) := by
  have hr := hreg
  regs_ne hr
  have hhilo := Ne.symm ‹lo ≠ hi›
  have hsrclo := Ne.symm ‹lo ≠ src›
  have hsrchi := Ne.symm ‹hi ≠ src›
  have hdstlo := Ne.symm ‹lo ≠ dst›
  have hdsthi := Ne.symm ‹hi ≠ dst›
  have hdstsrc := Ne.symm ‹src ≠ dst›
  intro x k v S hx
  refine ⟨{v with flag := ((S.R lo).head?.isNone && (S.R hi).head?.isSome), sym := (S.R src).head?},rfl,?_⟩
  simp_all [windowStep,windowStepFx,Action.run,update_rt,store_mk]

theorem windowStep_frame {lo hi src dst r : Fin T}
    (hlo : r ≠ lo) (hhi : r ≠ hi) (hsrc : r ≠ src) (hdst : r ≠ dst)
    (inside outside : Fin (A+4) → Fin (A+4)) : Frame r (windowStepFx lo hi src dst inside outside) := by
  intro x R l
  simp only [windowStepFx,Function.update_of_ne hlo.symm,Function.update_of_ne hhi.symm,
    Function.update_of_ne hsrc.symm,Function.update_of_ne hdst.symm]
  rw [Function.update_comm hlo,Function.update_comm hhi,Function.update_comm hsrc,Function.update_comm hdst]

private theorem counterWindow (a b : ℕ) :
    (((List.replicate a (tick : Fin (A+4))).head?.isNone &&
      (List.replicate b (tick : Fin (A+4))).head?.isSome)) = decide (a = 0 ∧ 0 < b) := by
  cases a <;> cases b <;> simp

/-- The scan consumes exactly the controlled prefix, preserving any borrowed suffix. -/
theorem windowStep_fold {lo hi src dst : Fin T} (hreg : [lo,hi,src,dst].Nodup)
    (inside outside : Fin (A+4) → Fin (A+4)) (cs xs tail : List (Fin (A+4))) (a b : ℕ) (R : Regs T A)
    (hlen : cs.length = xs.length) (hlo : R lo = List.replicate a tick)
    (hhi : R hi = List.replicate b tick) (hsrc : R src = xs++tail) :
    cs.foldl (fun R x => windowStepFx lo hi src dst inside outside x R) R =
      Function.update (Function.update (Function.update (Function.update R lo
        (List.replicate (a-xs.length) tick)) hi (List.replicate (b-xs.length) tick)) src tail) dst
        ((windowWord inside outside a b xs).reverse++R dst) := by
  have hr := hreg
  regs_ne hr
  induction cs generalizing xs a b R with
  | nil =>
    have hxs : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst xs
    simp only [List.nil_append] at hsrc
    funext r
    simp only [List.foldl_nil,List.length_nil,Nat.sub_zero,windowWord,List.reverse_nil,List.nil_append,
      Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  | cons c cs ih =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      let R₁ := windowStepFx lo hi src dst inside outside c R
      have hlo₁ : R₁ lo = List.replicate (a-1) tick := by
        simp_all [R₁,windowStepFx,List.tail_replicate]
      have hhi₁ : R₁ hi = List.replicate (b-1) tick := by
        simp_all [R₁,windowStepFx,List.tail_replicate]
      have hsrc₁ : R₁ src = xs++tail := by simp_all [R₁,windowStepFx]
      simp only [List.foldl_cons]
      rw [ih xs (a-1) (b-1) R₁ (by simpa using hlen) hlo₁ hhi₁ hsrc₁]
      funext r
      simp only [List.length_cons,windowWord,List.reverse_cons,List.append_assoc,
        R₁,windowStepFx,Function.update_apply]
      have ha : a-1-xs.length = a-(xs.length+1) := by omega
      have hb : b-1-xs.length = b-(xs.length+1) := by omega
      simp only [ha,hb]
      split_ifs <;> subst_vars <;> simp_all [counterWindow]

def windowScan (lo hi src dst count saved : Fin T) (inside outside : Fin (A+4) → Fin (A+4)) : Pr P T Q A U :=
  scanR count saved (windowStep lo hi src dst inside outside)

theorem windowScan_exec (body : P → Pr P T Q A U) {lo hi src dst count saved : Fin T}
    (hreg : [lo,hi,src,dst,count,saved].Nodup) (inside outside : Fin (A+4) → Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A) (xs tail : List (Fin (A+4))) (a b : ℕ)
    (hlen : (S.R count).length = xs.length) (ha : a ≤ xs.length) (hb : b ≤ xs.length)
    (hlo : S.R lo = List.replicate a tick) (hhi : S.R hi = List.replicate b tick)
    (hsrc : S.R src = xs++tail) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (windowScan lo hi src dst count saved inside outside) (mk v S) (4*xs.length+4)
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R lo []) hi [])
          src tail) dst ((windowWord inside outside a b xs).reverse++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  have hfour : [lo,hi,src,dst].Nodup := by simp_all
  obtain ⟨v',hu,he⟩ := scanR_exec' body ‹count ≠ saved› (windowStep_fx hfour inside outside)
    (windowStep_frame (Ne.symm ‹lo ≠ count›) (Ne.symm ‹hi ≠ count›)
      (Ne.symm ‹src ≠ count›) (Ne.symm ‹dst ≠ count›) inside outside)
    (windowStep_frame (Ne.symm ‹lo ≠ saved›) (Ne.symm ‹hi ≠ saved›)
      (Ne.symm ‹src ≠ saved›) (Ne.symm ‹dst ≠ saved›) inside outside) v S hsaved
  have hfold := windowStep_fold hfour inside outside (S.R count) xs tail a b S.R hlen hlo hhi hsrc
  refine ⟨v',hu,he.cast (by rw [hlen]) ?_⟩
  rw [hfold]
  simp only [Nat.sub_eq_zero_of_le ha,Nat.sub_eq_zero_of_le hb,List.replicate_zero]

end IntegerMultBounds.MathlibTM2.Host
