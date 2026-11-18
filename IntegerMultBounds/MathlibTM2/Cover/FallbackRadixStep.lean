module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRadixHorner

/-! Update the binary accumulator using the radix digit in the host symbol register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node RadixDigits
variable {T Q q : ℕ} {P U : Type}

def hornerStep (ins outs : Fin 1 → Fin T) (st width tmp : Fin T) (d : Fin q) : Pr P T Q q U :=
  .seq (autoWords ins outs st width tmp (radixHorner d)) (moveR (outs 0) (ins 0) id)

theorem hornerStep_exec (body : P → Pr P T Q q U) {ins outs : Fin 1 → Fin T} {st width tmp : Fin T}
    (h : AutoLayout ins outs st width tmp) (d : Fin q) (H x : ℕ) (pos : 0 < H)
    (v : HS T Q q U) (S : Stacks T q) (hw : (S.R width).length = H)
    (blank : S.R tmp = []) (work : S.R (outs 0) = []) (input : S.R (ins 0) = binSyms H x) :
    ∃ z n, z.user = v.user ∧ n ≤ 7*H+10 ∧ Exec body (hornerStep ins outs st width tmp d)
      (mk v S) n (mk z {S with R := Function.update S.R (ins 0) (binSyms H (q*x+d.val))}) := by
  let word := binSyms (A := q) H (q*x+d.val)
  let B := {S with R := autoRegs S.R ins outs (fun _ => word)}
  obtain ⟨u,n,hu,hn,scan⟩ := radixHorner_exec body h d H x pos v S hw blank input
  obtain ⟨z,hz,move⟩ := moveR_exec body (outs 0) (ins 0) (h.ins_outs 0 0).symm id u B
  have acc : B.R (ins 0) = [] := autoRegs_ins h.ins_inj 0
  have rev : B.R (outs 0) = word.reverse := by
    change autoRegs _ _ _ _ _ = _
    rw [autoRegs_outs h.outs_inj h.ins_outs,work,List.append_nil]
  refine ⟨z,_,hz.trans hu,?_,(Exec.seq scan move).cast rfl ?_⟩
  · simp only [rev,List.length_reverse,word,length_binSyms]; omega
  · apply congrArg (mk z)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = ins 0
    · subst i; simp [movedR,acc,rev,word]
    by_cases ho : i = outs 0
    · subst i; simp [movedR,hi,work]
    simp only [movedR,Function.update_of_ne hi,Function.update_of_ne ho]
    apply autoRegs_of_notMem <;> rintro ⟨j,rfl⟩ <;> fin_cases j <;> contradiction

def onDigit (f : Fin q → Pr P T Q q U) : List (Fin q) → Pr P T Q q U
  | [] => .act .done
  | d :: ds => .cond (fun v => v.sym == some (digitSymbol d)) (f d) (onDigit f ds)

theorem onDigit_exec (body : P → Pr P T Q q U) (f : Fin q → Pr P T Q q U)
    (ds : List (Fin q)) (d : Fin q) (hd : d ∈ ds) (v : HS T Q q U) (S : Stacks T q)
    (sym : v.sym = some (digitSymbol d)) {z F n} (run : Exec body (f d) (mk v S) n (mk z F)) :
    ∃ t ≤ n+ds.length, Exec body (onDigit f ds) (mk v S) t (mk z F) := by
  induction ds with
  | nil => simp at hd
  | cons a ds ih =>
    by_cases eq : d = a
    · subst a; exact ⟨_,by simp,Exec.cond_true (by change (v.sym == some (digitSymbol d)) = true; simp [sym]) run⟩
    have ne : digitSymbol d ≠ digitSymbol a := fun e => eq (Fin.ext (by have := congrArg Fin.val e; simp [digitSymbol] at this; omega))
    obtain ⟨t,ht,exec⟩ := ih ((List.mem_cons.mp hd).resolve_left eq)
    exact ⟨_,by simp; omega,Exec.cond_false (by change (v.sym == some (digitSymbol a)) = false; simp [sym,ne]) exec⟩

theorem radixDigits_exec (body : P → Pr P T Q q U) {ins outs : Fin 1 → Fin T} {st width tmp src saved : Fin T}
    (layout : AutoLayout ins outs st width tmp) (regs : [src,saved,ins 0,outs 0,width,tmp].Nodup)
    (xs : List (Fin q)) (H : ℕ) (pos : 0 < H) (v : HS T Q q U) (S : Stacks T q)
    (digits : S.R src = xs.reverse.map digitSymbol) (hw : (S.R width).length = H)
    (work : S.R (outs 0) = []) (blank : S.R tmp = []) (zero : S.R (ins 0) = binSyms H 0) :
    ∃ z R n, z.user = v.user ∧ n ≤ xs.length*(7*H+q+13)+2 ∧
      Exec body (eachSym src saved (onDigit (hornerStep ins outs st width tmp) (List.finRange q)))
        (mk v S) n (mk z {S with R := R}) ∧ R src = [] ∧ R saved = xs.map digitSymbol ++ S.R saved ∧
      ∀ k, k ≠ src → k ≠ saved → R k = Function.update S.R (ins 0) (binSyms H (value xs)) k := by
  regs_ne regs
  let x := fun j => value (xs.drop (xs.length-j))
  let Ψ := fun j => Function.update S.R (ins 0) (binSyms H (x j))
  have step : SymSpec body (onDigit (hornerStep ins outs st width tmp) (List.finRange q))
      src saved (S.R src) Ψ (7*H+10+q) := by
    intro j hj u B sym keep
    have lt : j < xs.length := by simpa [digits] using hj
    let i := xs.length-1-j
    have hi : i < xs.length := by dsimp [i]; omega
    let d := xs[i]
    have next : x (j+1) = q*x j+d.val := by
      change value (xs.drop _) = q*value (xs.drop _) + _
      rw [show xs.length-(j+1) = i by dsimp [i]; omega,List.drop_eq_getElem_cons hi]
      simp only [d,value,show i+1 = xs.length-j by dsimp [i]; omega,Nat.add_comm]
    have hs : u.sym = some (digitSymbol d) := by simpa [digits,List.getElem_reverse,d,i] using sym
    have other (k) (ha : k ≠ src) (hb : k ≠ saved) (hc : k ≠ ins 0) :
        B.R k = S.R k := (keep k ha hb).trans (Function.update_of_ne hc _ _)
    obtain ⟨z,n,hz,hn,run⟩ := hornerStep_exec body layout d H (x j) pos u B
      (by rw [other width (by apply Ne.symm; assumption) (by apply Ne.symm; assumption) (by apply Ne.symm; assumption),hw])
      ((other tmp (by apply Ne.symm; assumption) (by apply Ne.symm; assumption) (by apply Ne.symm; assumption)).trans blank)
      ((other _ (by apply Ne.symm; assumption) (by apply Ne.symm; assumption) (by apply Ne.symm; assumption)).trans work)
      (by rw [keep _ (by apply Ne.symm; assumption) (by apply Ne.symm; assumption)]; simp [Ψ])
    obtain ⟨t,ht,branch⟩ := onDigit_exec body _ (List.finRange q) d (by simp) u B hs run
    refine ⟨z,_,t,hz,by simp at ht; omega,branch,Function.update_of_ne (by assumption) _ _,
      Function.update_of_ne (by assumption) _ _,?_⟩
    intro k ha hb
    by_cases eq : k = ins 0
    · subst k; simp [Ψ,next]
    · simpa [Ψ,Function.update_of_ne eq] using other k ha hb eq
  obtain ⟨z,R,n,hz,hn,run,empty,rest,frame⟩ := eachSym_exec body ‹src ≠ saved› v S step
    (fun k _ _ => by simp [Ψ,x,value,← zero])
  exact ⟨z,R,n,hz,by simpa [digits,show 7*H+10+q+3 = 7*H+q+13 by omega] using hn,run,empty,
    by simpa [digits,← List.map_reverse] using rest,by simpa [Ψ,x,digits] using frame⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
