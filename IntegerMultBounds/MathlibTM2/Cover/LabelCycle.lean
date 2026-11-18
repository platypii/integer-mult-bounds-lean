module

public import IntegerMultBounds.MathlibTM2.Cover.LabelSelectors

/-! Emit a fixed residue cycle for each symbol of a retained unary high-part count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelCycle
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Host Node
variable {T Q A : ℕ} {P U : Type}

/-- Push the symbols of a fixed word, starting at its end. -/
def pushWord (out : Fin T) : List (Fin (A+4)) → Act T Q A U → Act T Q A U
  | [], k => k
  | x :: xs, k => pushWord out xs (.push (.rt out) (fun _ => x) k)

theorem pushWord_run (out : Fin T) (word : List (Fin (A+4))) (k : Act T Q A U)
    (u : HS T Q A U) (S : Stacks T A) :
    (pushWord out word k).run (mk u S) =
      k.run (mk u {S with R := Function.update S.R out (word ++ S.R out)}) := by
  induction word generalizing k with
  | nil => simp [pushWord]
  | cons x xs ih =>
    rw [pushWord, ih]
    simp [Action.run, update_rt]

def emit (count saved out : Fin T) (word : List (Fin (A+4))) : Pr P T Q A U :=
  scanR count saved (pushWord out word)

private theorem repeat_fold (xs word : List (Fin (A+4))) (out : Fin T) (R : Regs T A) :
    xs.foldl (fun R _ => Function.update R out (word ++ R out)) R =
      Function.update R out ((List.replicate xs.length word).flatten ++ R out) := by
  induction xs generalizing R with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp [List.replicate_succ', List.append_assoc]

theorem emit_exec (body : P → Pr P T Q A U) {count saved out : Fin T}
    (hr : [count,saved,out].Nodup) (word : List (Fin (A+4))) (u : HS T Q A U)
    (S : Stacks T A) (hs : S.R saved = []) :
    ∃ u', u'.user = u.user ∧ Exec body (emit count saved out word) (mk u S)
      (4*(S.R count).length+4) (mk u' {S with R := Function.update S.R out ((List.replicate (S.R count).length word).flatten ++ S.R out)}) := by
  regs_ne hr
  let Φ := fun (_ : Fin (A+4)) (R : Regs T A) => Function.update R out (word ++ R out)
  have hf : RegFx (pushWord (Q := Q) (U := U) out word) Φ :=
    fun _ k v S _ => ⟨v, rfl, pushWord_run out word k v S⟩
  have frame {j : Fin T} (hj : j ≠ out) : Frame j Φ := by
    intro x R xs
    simp only [Φ, Function.update_of_ne hj.symm, Function.update_comm hj]
  obtain ⟨u', hu, he⟩ := scanR_exec' body ‹count ≠ saved› hf (frame ‹count ≠ out›)
    (frame ‹saved ≠ out›) u S hs
  exact ⟨u', hu, by simpa only [emit, Φ, repeat_fold] using he⟩

def lowWord (f : ZMod prime → Bool) : List (Fin (A+4)) :=
  ((List.range prime).map fun (i : ℕ) => bitSymbol (f (i : ZMod prime)))

/-- The selector for the innermost atom may depend on all fixed outer residues. -/
theorem low_exec (body : P → Pr P T Q A U) {count saved out : Fin T}
    (hr : [count,saved,out].Nodup) (f : ZMod prime → Bool) (u : HS T Q A U)
    (S : Stacks T A) (hs : S.R saved = []) :
    ∃ u', u'.user = u.user ∧ Exec body (emit count saved out (lowWord f)) (mk u S)
      (4*(S.R count).length+4) (mk u' {S with R := Function.update S.R out (((LabelSelectors.cycle (S.R count).length).map (bitSymbol ∘ f)) ++ S.R out)}) := by
  simpa only [LabelSelectors.cycle, List.map_flatten, List.map_replicate, List.map_map, Function.comp_def, lowWord]
    using emit_exec body hr (lowWord f) u S hs

/-- A retained unary loop for an inner traversal whose output word depends on runtime dimensions. -/
def repeatBlock (count saved : Fin T) (p : Pr P T Q A U) :=
  Prog.seq (eachSym count saved p) (moveR saved count id)

theorem repeat_exec (body : P → Pr P T Q A U) {count saved out : Fin T}
    (hr : [count,saved,out].Nodup) (p : Pr P T Q A U) (word : List (Fin (A+4))) (c : ℕ)
    (u : HS T Q A U) (S : Stacks T A) (hs : S.R saved = [])
    (step : ∀ (v : HS T Q A U) (M : Stacks T A),
      (∀ k, k ≠ count → k ≠ saved → k ≠ out → M.R k = S.R k) →
      ∃ v' n, v'.user = v.user ∧ n ≤ c ∧ Exec body p (mk v M) n
        (mk v' {M with R := Function.update M.R out (word ++ M.R out)})) :
    ∃ u' n, u'.user = u.user ∧ n ≤ (S.R count).length*(c+5)+4 ∧
      Exec body (repeatBlock count saved p) (mk u S) n
        (mk u' {S with R := Function.update S.R out ((List.replicate (S.R count).length word).flatten ++ S.R out)}) := by
  regs_ne hr
  let R (j : ℕ) := Function.update S.R out ((List.replicate j word).flatten ++ S.R out)
  have spec : SymSpec body p count saved (S.R count) R c := by
    intro j _ v M _ hM
    obtain ⟨v', n, hu, hn, he⟩ := step v M (fun k hc hs ho => by simpa [R, ho] using hM k hc hs)
    refine ⟨v', _, n, hu, hn, he, Function.update_of_ne ‹count ≠ out› ..,
      Function.update_of_ne ‹saved ≠ out› .., ?_⟩
    intro k hc hs
    by_cases ho : k = out
    · subst k
      simp [R, hM out hc hs, List.replicate_succ, List.append_assoc]
    · simp [R, ho, hM k hc hs]
  obtain ⟨v, M, n, hu, hn, he, hc, hsave, hM⟩ := eachSym_exec body ‹count ≠ saved› u S spec
    (by simp [R])
  obtain ⟨v', hu', he'⟩ := moveR_exec (body := body) saved count (Ne.symm ‹count ≠ saved›) id v {S with R := M}
  simp only [hs, List.append_nil] at hsave
  refine ⟨v', _, hu'.trans hu, ?_, (Exec.seq he he').cast rfl ?_⟩
  · change n + (2*(M saved).length+2) ≤ _
    rw [hsave, List.length_reverse]
    nlinarith
  · apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h : k = count
    · subst k; simp [movedR, hc, hsave, ‹count ≠ out›]
    by_cases h' : k = saved
    · subst k; simp [movedR, h, hs, ‹saved ≠ out›]
    · simp [movedR, h, h', hM k h h', R]


end
end IntegerMultBounds.MathlibTM2.Cover.LabelCycle
