module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderCopies
public import IntegerMultBounds.MathlibTM2.Fast.Input

/-! Copy retained words, including binary geometry, through one shared scratch
register. Sources survive verbatim; only listed destinations change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def copyWordHeader (src dst tmp saved : Fin T) : Pr P T Q A U :=
  .seq (copyR src tmp saved id) (moveR tmp dst id)

theorem copyWordHeader_exec (src dst tmp saved : Fin T)
    (hreg : [src,dst,tmp,saved].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧ Exec body (copyWordHeader src dst tmp saved) (mk v S)
      (6*(S.R src).length+6) (mk v' {S with R := Function.update S.R dst (S.R src++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec body src tmp saved ‹src ≠ tmp› ‹src ≠ saved› ‹tmp ≠ saved› id v S hsaved
  let M : Stacks T A := {S with R := Function.update S.R tmp (S.R src).reverse}
  have he₁' : Exec body (copyR src tmp saved id) (mk v S) (4*(S.R src).length+4) (mk v₁ M) := by
    simpa [M,htmp] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body tmp dst ‹dst ≠ tmp›.symm id v₁ M
  have hend : movedR M.R tmp dst id (M.R tmp) = Function.update S.R dst (S.R src++S.R dst) := by
    funext i
    by_cases hd : i = dst
    · subst i; simp [M,movedR,‹dst ≠ tmp›]
    · by_cases ht : i = tmp
      · subst i; simp [M,movedR,hd,htmp]
      · simp [M,movedR,hd,ht]
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast ?_ ?_⟩
  · simp [M]; omega
  · simp only [hend]; rfl

def copyWordHeaders (tmp saved : Fin T) : List (Fin T × Fin T) → Pr P T Q A U
  | [] => .act .done
  | (src,dst)::rs => .seq (copyWordHeader src dst tmp saved) (copyWordHeaders tmp saved rs)

def copyWordHeadersR (value : Fin T → List (Fin (A+4))) :
    List (Fin T × Fin T) → Regs T A → Regs T A
  | [],R => R
  | (src,dst)::rs,R => copyWordHeadersR value rs (Function.update R dst (value src++R dst))

theorem copyWordHeadersR_off (value : Fin T → List (Fin (A+4))) (rs : List (Fin T × Fin T))
    (R : Regs T A) (i : Fin T) (hi : ∀ r ∈ rs, r.2 ≠ i) : copyWordHeadersR value rs R i = R i := by
  induction rs generalizing R with
  | nil => rfl
  | cons r rs ih =>
    rw [copyWordHeadersR,ih _ (by intro s hs; exact hi s (by simp [hs]))]
    exact Function.update_of_ne (hi r (by simp)).symm _ _

/-- Loading retained headers commutes with an unrelated data-port update. -/
theorem copyWordHeadersR_update_off (value R : Regs T A) (rs : List (Fin T × Fin T))
    (k : Fin T) (xs : List (Fin (A+4)))
    (hoff : ∀ r ∈ rs, r.1 ≠ k ∧ r.2 ≠ k) :
    copyWordHeadersR (Function.update value k xs) rs (Function.update R k xs) =
      Function.update (copyWordHeadersR value rs R) k xs := by
  induction rs generalizing R with
  | nil => rfl
  | cons r rs ih =>
    have hr := hoff r (by simp)
    simp only [copyWordHeadersR,Function.update_of_ne hr.1]
    rw [Function.update_of_ne hr.2,Function.update_comm hr.2.symm]
    exact ih _ (by intro p hp; exact hoff p (by simp [hp]))

theorem copyWordHeadersR_get (value : Fin T → List (Fin (A+4))) (rs : List (Fin T × Fin T))
    (hnd : (rs.map Prod.snd).Nodup) (R : Regs T A) (r : Fin T × Fin T) (hr : r ∈ rs) :
    copyWordHeadersR value rs R r.2 = value r.1++R r.2 := by
  induction rs generalizing R with
  | nil => simp at hr
  | cons p ps ih =>
    have hn := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hr with he | hr
    · subst r
      rw [copyWordHeadersR,copyWordHeadersR_off value ps _ p.2 (by
        intro q hq he
        exact hn.1 (List.mem_map.mpr ⟨q,hq,he⟩))]
      exact Function.update_self _ _ _
    · rw [copyWordHeadersR,ih hn.2 _ hr]
      rw [Function.update_of_ne (show r.2 ≠ p.2 from fun he => hn.1 (List.mem_map.mpr ⟨r,hr,he⟩))]

theorem copyWordHeaders_exec (tmp saved : Fin T) (rs : List (Fin T × Fin T))
    (hregs : ∀ r ∈ rs, [r.1,r.2,tmp,saved].Nodup)
    (hsep : ∀ r ∈ rs, ∀ p ∈ rs, r.2 ≠ p.1)
    (value : Fin T → List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : ∀ r ∈ rs, S.R r.1 = value r.1) (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyWordHeaders tmp saved rs) (mk v S)
        ((rs.map (fun r => 6*(value r.1).length+6)).sum+1)
        (mk v' {S with R := copyWordHeadersR value rs S.R}) := by
  induction rs generalizing v S with
  | nil => exact ⟨v,rfl,by simpa [copyWordHeaders,copyWordHeadersR] using Exec.act (body := body) .done (mk v S)⟩
  | cons r rs ih =>
    have hr := hregs r (by simp)
    regs_ne hr
    obtain ⟨v₁,hu₁,he₁⟩ := copyWordHeader_exec (body := body) r.1 r.2 tmp saved (hregs r (by simp)) v S htmp hsaved
    let M : Stacks T A := {S with R := Function.update S.R r.2 (value r.1++S.R r.2)}
    have he₁' : Exec body (copyWordHeader r.1 r.2 tmp saved) (mk v S) (6*(value r.1).length+6) (mk v₁ M) := by
      simpa [M,hsrc r (by simp)] using he₁
    obtain ⟨v₂,hu₂,he₂⟩ := ih (by intro p hp; exact hregs p (by simp [hp]))
      (by intro p hp q hq; exact hsep p (by simp [hp]) q (by simp [hq])) v₁ M
      (by intro p hp; simpa [M,(hsep r (by simp) p (by simp [hp])).symm] using hsrc p (by simp [hp]))
      (by simpa [M,‹r.2 ≠ tmp›.symm] using htmp)
      (by simpa [M,‹r.2 ≠ saved›.symm] using hsaved)
    refine ⟨v₂,hu₂.trans hu₁,?_⟩
    simpa [copyWordHeaders,copyWordHeadersR,M,Nat.add_assoc] using Exec.seq he₁' he₂

theorem copyWordHeaders_native (tmp saved : Fin T) (rs : List (Fin T × Fin T)) :
    mnNativePushBound 2 (copyWordHeaders (P := P) (Q := Q) (A := A) (U := U) tmp saved rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    refine ⟨?_,ih⟩
    simp [copyWordHeader,copyR,copyStep,scanR,keepIn,drainR,popDo,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
