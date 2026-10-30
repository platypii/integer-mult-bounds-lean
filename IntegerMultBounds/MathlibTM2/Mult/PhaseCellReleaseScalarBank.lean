module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeScalarBank
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Dispose allocated scalar-variable words while retaining the borrowed width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def releaseScalarBank (rg : TblR n → Fin T) : Pr P T Q A U :=
  clearWords ((List.finRange n).map (fun i => rg (.v i)))

/-- After scalar restoration, erase every allocated variable word. The table's
width word and all registers outside its bank are preserved. -/
theorem releaseScalarBank_exec (rg : TblR n → Fin T) (hrg : Function.Injective rg)
    (W : ℕ) (wl : List (Fin (A+4))) (st : TblSt n A) (hacc : st.acc = [])
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl [] st)) :
    ∃ v' F, v'.user = v.user ∧
      Exec body (releaseScalarBank rg) (mk v S) (2*(n*W)+2*n+1) (mk v' F) ∧
      F.R (rg .wr) = wl ∧ (∀ r : TblR n, r ≠ .wr → F.R (rg r) = []) ∧ tblFr rg S F := by
  let rs := (List.finRange n).map (fun i => rg (.v i))
  have hnd : rs.Nodup := (List.nodup_finRange n).map (by
    intro i j he
    exact TblR.v.inj (hrg he))
  have hlen i : (S.R (rg (.v i))).length = W := by rw [hS (.v i)]; simp
  have hsum : (rs.map (fun r => (S.R r).length)).sum = n*W := by
    simp [rs,List.map_map,Function.comp_def,hlen]
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) rs hnd v S
  let F : Stacks T A := {S with R := fun i => if i ∈ rs then [] else S.R i}
  refine ⟨v',F,hu,?_,?_,?_,rfl,rfl,rfl,?_⟩
  · simpa only [releaseScalarBank,rs,hsum,List.length_map,List.length_finRange] using he
  · simpa [F,rs,List.mem_map,hrg.eq_iff] using hS .wr
  · intro r hr
    cases r with
    | v i => simp [F,rs,List.mem_map,hrg.eq_iff]
    | wr => exact False.elim (hr rfl)
    | wn => simpa [F,rs,List.mem_map,hrg.eq_iff] using hS .wn
    | acc => simpa [F,rs,List.mem_map,hrg.eq_iff,hacc] using hS .acc
    | z i => simpa [F,rs,List.mem_map,hrg.eq_iff] using hS (.z i)
  · intro i hoff
    have hi : i ∉ rs := by
      intro hi
      obtain ⟨j,hj,he⟩ := List.mem_map.mp hi
      exact hoff (.v j) he
    simp [F,hi]

/-- A blank scalar bank and its outside frame determine the whole machine
state. This avoids one register case per scalar variable or scratch port. -/
theorem blankScalarBank_eq (rg : TblR n → Fin T) (S F : Stacks T A)
    (hwidth : F.R (rg .wr) = S.R (rg .wr))
    (hS : ∀ r : TblR n, r ≠ .wr → S.R (rg r) = [])
    (hF : ∀ r : TblR n, r ≠ .wr → F.R (rg r) = [])
    (hin : F.inp = S.inp) (hout : F.out = S.out) (hL : F.L = S.L)
    (hframe : ∀ i, (∀ r, rg r ≠ i) → F.R i = S.R i) : F = S := by
  refine Stacks.ext hin hout hL ?_
  funext i
  by_cases hi : ∃ r, rg r = i
  · obtain ⟨r,rfl⟩ := hi
    by_cases hr : r = .wr
    · subst r; exact hwidth
    · exact (hF r hr).trans (hS r hr).symm
  · exact hframe i (by simpa using hi)

/-- Execute disposal into a specified restored state. All premises describe
the initial blank bank and the actual non-scalar frame, not a final execution. -/
theorem releaseScalarBank_to_state_exec (rg : TblR n → Fin T) (hrg : Function.Injective rg)
    (W : ℕ) (wl : List (Fin (A+4))) (st : TblSt n A) (hacc : st.acc = [])
    (v : HS T Q A U) (F S : Stacks T A) (hF : tblHolds rg F (tblRho W wl [] st))
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ r : TblR n, r ≠ .wr → S.R (rg r) = [])
    (hin : F.inp = S.inp) (hout : F.out = S.out) (hL : F.L = S.L)
    (hframe : ∀ i, (∀ r, rg r ≠ i) → F.R i = S.R i) :
    ∃ v', v'.user = v.user ∧
      Exec body (releaseScalarBank rg) (mk v F) (2*(n*W)+2*n+1) (mk v' S) := by
  obtain ⟨v',G,hu,he,hw,hb,hi,ho,hl,hf⟩ := releaseScalarBank_exec (body := body) rg hrg W wl st hacc v F hF
  have hG := blankScalarBank_eq rg S G (hw.trans hwidth.symm) hblank hb
    (hi.trans hin) (ho.trans hout) (hl.trans hL) (by
      intro i hoff
      exact (hf i hoff).trans (hframe i hoff))
  exact ⟨v',hu,he.cast rfl (congrArg (mk v') hG)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
