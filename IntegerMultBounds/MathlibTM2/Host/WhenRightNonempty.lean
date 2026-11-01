module

public import IntegerMultBounds.MathlibTM2.Host.FirstAction
public import IntegerMultBounds.MathlibTM2.Host.Stream
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Guard native work by an actual counter, reusing traces whose first peek
already overwrites the flag. Empty counters execute no body work. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def whenRightNonempty (count : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (.act (peekR count)) (.cond (·.flag) p (.act .done))

theorem whenRightNonempty_exec_within (count reset : Fin T) {p : Pr P T Q A U}
    (hfirst : FirstAction (peekR reset) p)
    {s t : Store (HΓ (T := T) A) (HS T Q A U)} {depth n bound : ℕ}
    (he : ExecWithin body (fun d z => mnSize z+d ≤ bound) depth p s n t)
    (hcount : s.stk (.rt count) ≠ []) :
    ExecWithin body (fun d z => mnSize z+d ≤ bound) depth (whenRightNonempty count p) s (n+2) t := by
  let s' := {s with var := {s.var with flag := true}}
  have hflag : (s.stk (.rt count)).head?.isSome = true := by
    cases hs : s.stk (.rt count) with
    | nil => exact False.elim (hcount hs)
    | cons x xs => simp
  have hpeek : (peekR count : Act T Q A U).run s = s' := by
    change {s with var := {s.var with flag := (s.stk (.rt count)).head?.isSome}} = _
    rw [hflag]
  have hp : ExecWithin body (fun d z => mnSize z+d ≤ bound) depth (.act (peekR count)) s 1 s' := by
    have hh := ExecWithin.act (body := body) (Inv := fun d z => mnSize z+d ≤ bound) (d := depth) (peekR count) s he.initial he.initial
    exact hh.cast rfl hpeek
  have he' := hfirst.change_start he (s' := s') he.initial (by rfl)
  have hc : ExecWithin body (fun d z => mnSize z+d ≤ bound) depth
      (.cond (·.flag) p (.act .done)) s' (n+1) t := .cond_true rfl he'
  exact (ExecWithin.seq hp hc).cast (by omega) rfl

theorem whenRightNonempty_empty_within (count : Fin T) (p : Pr P T Q A U)
    (s : Store (HΓ (T := T) A) (HS T Q A U)) (depth bound : ℕ)
    (hbound : mnSize s+depth ≤ bound) (hcount : s.stk (.rt count) = []) :
    ExecWithin body (fun d z => mnSize z+d ≤ bound) depth (whenRightNonempty count p) s 3
      {s with var := {s.var with flag := false}} := by
  let s' := {s with var := {s.var with flag := false}}
  have hpeek : (peekR count : Act T Q A U).run s = s' := by
    change {s with var := {s.var with flag := (s.stk (.rt count)).head?.isSome}} = _
    simp [hcount,s']
  have hp : ExecWithin body (fun d z => mnSize z+d ≤ bound) depth (.act (peekR count)) s 1 s' :=
    (ExecWithin.act (body := body) (Inv := fun d z => mnSize z+d ≤ bound) (d := depth) (peekR count) s hbound hbound).cast rfl hpeek
  have hd : ExecWithin body (fun d z => mnSize z+d ≤ bound) depth (.act .done) s' 1 s' :=
    .act .done s' hbound hbound
  exact .seq hp (.cond_false rfl hd)

/-- Insert a counter guard between existing stages without replaying the body. -/
theorem guard_middle_exec_within (count reset : Fin T) (before p after : Pr P T Q A U)
    (hfirst : FirstAction (peekR reset) p)
    {s t : Store (HΓ (T := T) A) (HS T Q A U)} {depth n bound : ℕ}
    (he : ExecWithin body (fun d z => mnSize z+d ≤ bound) depth (.seq before (.seq p after)) s n t)
    (hcount : ∀ z m, Exec body before s m z → z.stk (.rt count) ≠ []) :
    ExecWithin body (fun d z => mnSize z+d ≤ bound) depth
      (.seq before (.seq (whenRightNonempty count p) after)) s (n+2) t := by
  cases he with
  | seq hb ht =>
    cases ht with
    | seq hp ha =>
      have hg := whenRightNonempty_exec_within count reset hfirst hp (hcount _ _ hb.toExec)
      exact (ExecWithin.seq hb (ExecWithin.seq hg ha)).cast (by omega) rfl

end IntegerMultBounds.MathlibTM2.Host
