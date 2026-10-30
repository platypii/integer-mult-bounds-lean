module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalUnaryHeader

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def canonicalHeaderWord (A n : ℕ) : List (Fin (A+4)) :=
  separator::(binBits (Nat.size n) n).map bitSymbol

def canonicalHeaderList (a half par bits cnt saved : Fin T) : List (Fin T × Fin T) → Pr P T Q A U
  | [] => .act .done
  | (src,dst)::rs => .seq (canonicalUnaryHeader src dst a half par bits cnt saved)
      (canonicalHeaderList a half par bits cnt saved rs)

def canonicalHeaderListR (value : Fin T → ℕ) : List (Fin T × Fin T) → (Fin T → List (Fin (A+4))) → Fin T → List (Fin (A+4))
  | [],R => R
  | (src,dst)::rs,R => canonicalHeaderListR value rs (Function.update R dst (canonicalHeaderWord A (value src)))

theorem canonicalHeaderListR_off (value : Fin T → ℕ) (rs : List (Fin T × Fin T))
    (R : Fin T → List (Fin (A+4))) (i : Fin T) (hi : ∀ r ∈ rs, r.2 ≠ i) :
    canonicalHeaderListR value rs R i = R i := by
  induction rs generalizing R with
  | nil => rfl
  | cons r rs ih =>
    rw [canonicalHeaderListR,ih _ (by intro s hs; exact hi s (by simp [hs]))]
    exact Function.update_of_ne (hi r (by simp)).symm _ _

theorem canonicalHeaderListR_get (value : Fin T → ℕ) (rs : List (Fin T × Fin T))
    (hnd : (rs.map Prod.snd).Nodup) (R : Fin T → List (Fin (A+4)))
    (r : Fin T × Fin T) (hr : r ∈ rs) :
    canonicalHeaderListR value rs R r.2 = canonicalHeaderWord A (value r.1) := by
  induction rs generalizing R with
  | nil => simp at hr
  | cons s rs ih =>
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hr with he | hr
    · subst r
      rw [canonicalHeaderListR,canonicalHeaderListR_off value rs _ s.2 (by
        intro r hr he
        exact hnd'.1 (List.mem_map.mpr ⟨r,hr,he⟩))]
      exact Function.update_self _ _ _
    · exact ih hnd'.2 _ hr

/-- One structural proof composes any header list, with shared restored scratch
and borrowed unary sources. Only the listed destinations change. -/
theorem canonicalHeaderList_exec (a half par bits cnt saved : Fin T)
    (value : Fin T → ℕ) (rs : List (Fin T × Fin T))
    (hreg : ∀ r ∈ rs, [r.1,r.2,a,half,par,bits,cnt,saved].Nodup)
    (hnd : (rs.map Prod.snd).Nodup)
    (hdisjoint : ∀ r ∈ rs, ∀ s ∈ rs, r.2 ≠ s.1)
    (v : HS T Q A U) (S : Stacks T A)
    (hsource : ∀ r ∈ rs, (S.R r.1).length = value r.1)
    (hdst : ∀ r ∈ rs, S.R r.2 = [])
    (hfresh : ∀ i ∈ [a,half,par,bits,cnt,saved], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (rs.map (fun r => 21*value r.1+11)).sum+1 ∧
      Exec body (canonicalHeaderList a half par bits cnt saved rs) (mk v S) n
        (mk v' {S with R := canonicalHeaderListR value rs S.R}) := by
  induction rs generalizing v S with
  | nil => exact ⟨v,1,rfl,by simp,by simpa [canonicalHeaderList,canonicalHeaderListR] using Exec.act (body := body) .done (mk v S)⟩
  | cons r rs ih =>
    have hhead := hreg r (by simp)
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hval,hcanon⟩ := canonicalUnaryHeader_exec
      r.1 r.2 a half par bits cnt saved hhead (value r.1) v S (hsource r (by simp)) (by
        intro i hi
        rcases List.mem_cons.mp hi with he | hi
        · subst i; exact hdst r (by simp)
        · exact hfresh i hi)
    let M : Stacks T A := {S with R := Function.update S.R r.2 (canonicalHeaderWord A (value r.1))}
    have hscratch : ∀ i ∈ [a,half,par,bits,cnt,saved], i ≠ r.2 := by
      intro i hi he
      subst i
      exact (List.nodup_cons.mp (List.nodup_cons.mp hhead).2).1 hi
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ih
      (by intro s hs; exact hreg s (by simp [hs])) hnd'.2
      (by intro s hs t ht; exact hdisjoint s (by simp [hs]) t (by simp [ht])) v₁ M
      (by intro s hs
          rw [show M.R s.1 = S.R s.1 from Function.update_of_ne (hdisjoint r (by simp) s (by simp [hs])).symm _ _]
          exact hsource s (by simp [hs]))
      (by intro s hs
          have hne : s.2 ≠ r.2 := by intro he; exact hnd'.1 (List.mem_map.mpr ⟨s,hs,he⟩)
          simpa only [M,Function.update_of_ne hne] using hdst s (by simp [hs]))
      (by intro i hi; simpa only [M,Function.update_of_ne (hscratch i hi)] using hfresh i hi)
    refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
    simp only [List.map_cons,List.sum_cons]
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
