module

public import IntegerMultBounds.MathlibTM2.Node.TopWord
public import IntegerMultBounds.MathlibTM2.Host.BinArithStock
public import IntegerMultBounds.MathlibTM2.Host.ConsumeRuns

/-! Nonexpanding word passes reuse one word's scratch across the entire stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Charge the native word program once, rather than once per word in the stream. -/
theorem topWords_within {wp : Pr P T Q A U} {src dst : Fin T} (hsd : src ≠ dst)
    {G : Regs T A → Prop} (hG : TopWordFrame src dst G) {L c push : ℕ}
    {F : List (Fin (A+4)) → List (Fin (A+4))}
    (hwp : TopWordSpec body wp src dst G L F c) (hnative : mnNativePushBound push wp)
    (ws : List (List (Fin (A+4)))) (v : HS T Q A U) (S : Stacks T A)
    (hlen : ∀ x ∈ ws, x.length = L) (hvolume : ∀ x ∈ ws, (F x).length ≤ x.length)
    (hsrc : S.R src = ws.flatten) (hg : G S.R)
    {n : ℕ} {t : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : Exec body (topWords src wp) (mk v S) n t) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+push*c) depth
      (topWords src wp) (mk v S) n t := by
  let base := mnSize (mk v S)
  let I : Store (HΓ (T := T) A) (HS T Q A U) → Prop := fun z =>
    ∃ (w : HS T Q A U) (R : Stacks T A) (todo : List (List (Fin (A+4)))),
      z = mk w R ∧ (∀ x ∈ todo, x.length = L ∧ (F x).length ≤ x.length) ∧
      R.R src = todo.flatten ∧ G R.R ∧ w.flag = todo.flatten.head?.isSome ∧ mnSize z ≤ base
  cases he with
  | seq hp hloop =>
    cases hp
    have hpeek : ExecWithin body (fun d z => mnSize z+d ≤ base+depth+push*c) depth
        (.act (peekR src)) (mk v S) 1 ((peekR src).run (mk v S)) :=
      mn_native_exec_within (.act _ _) 0 (by simp [peekR,mnNativePushBound,mnActPush]) depth _ (by omega)
    refine .seq hpeek (loop_within_of_boundary body wp (·.flag) I
      (fun d z => mnSize z+d ≤ base+depth+push*c) depth ?_ ?_ hloop ?_)
    · intro z hz
      obtain ⟨w,R,todo,rfl,_,_,_,_,hb⟩ := hz
      omega
    · intro z t n hz hf hex
      obtain ⟨w,R,todo,rfl,htodo,hsource,hGR,hflag,hbound⟩ := hz
      cases todo with
      | nil => simp at hflag; simp [hflag] at hf
      | cons x todo =>
        have hx := htodo x (by simp)
        have hsource' : R.R src = x++todo.flatten := by simpa only [List.flatten_cons] using hsource
        obtain ⟨w',hu,hflag',hw⟩ := hwp x todo.flatten w R hx.1 hsource' hGR
        obtain ⟨hn,ht⟩ := hex.unique hw
        subst n
        subst t
        let R' : Stacks T A := {R with R := (Function.update (Function.update R.R src todo.flatten)
          dst ((F x).reverse++R.R dst))}
        have hsize : mnSize (mk w' R') ≤ mnSize (mk w R) :=
          mn_consume_appendR_size_nonincreasing w w' R src dst hsd x todo.flatten (F x).reverse
            hsource' (by simpa only [List.length_reverse] using hx.2)
        refine ⟨mn_native_exec_within hw push hnative depth _ (by omega),w',R',todo,rfl,?_,?_,
          hG _ _ _ hGR,hflag',hsize.trans hbound⟩
        · intro y hy; exact htodo y (List.mem_cons_of_mem _ hy)
        · simp [R',Function.update_of_ne hsd]
    · rw [peekR_run]
      refine ⟨{v with flag := (S.R src).head?.isSome},S,ws,rfl,?_,hsrc,hg,?_,?_⟩
      · intro x hx; exact ⟨hlen x hx,hvolume x hx⟩
      · exact congrArg (fun xs => xs.head?.isSome) hsrc
      · exact le_rfl

/-- The final ordered move uses no extra storage beyond the shared word reserve. -/
theorem topPass_within {wp : Pr P T Q A U} {src dst : Fin T} (hsd : src ≠ dst)
    {G : Regs T A → Prop} (hG : TopWordFrame src dst G) {L c push : ℕ}
    {F : List (Fin (A+4)) → List (Fin (A+4))}
    (hwp : TopWordSpec body wp src dst G L F c) (hnative : mnNativePushBound push wp)
    (ws : List (List (Fin (A+4)))) (v : HS T Q A U) (S : Stacks T A)
    (hlen : ∀ x ∈ ws, x.length = L) (hvolume : ∀ x ∈ ws, (F x).length ≤ x.length)
    (hsrc : S.R src = ws.flatten) (hg : G S.R)
    {n : ℕ} {t : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : Exec body (topPass src dst wp) (mk v S) n t) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+push*c) depth
      (topPass src dst wp) (mk v S) n t := by
  cases he with
  | seq hp hmove =>
    have hw := topWords_within hsd hG hwp hnative ws v S hlen hvolume hsrc hg hp depth
    exact .seq hw (moveR_within dst src id hmove depth _ hw.final)

/-- A fixed bound on pushes in one truncating-shift word program. -/
theorem topShiftWord_native (src dst tmp cW cS cE cD sp sg cy : Fin T) :
    mnNativePushBound 13 (topShiftWord (P := P) (Q := Q) (A := A) (U := U)
      src dst tmp cW cS cE cD sp sg cy) := by
  simp [topShiftWord,Shift.counted,Shift.copyStep,topSignAct,topAbsF,topEmitF,topEndAct,
    usub,dropTop,scanR,drainR,popDo,keepIn,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Node
