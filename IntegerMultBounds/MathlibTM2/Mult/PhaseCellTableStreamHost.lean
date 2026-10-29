module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def tableStreamHost (rg : TblR n → Fin T) (ports : List (Fin T)) (out : Fin T) (code : TblCode n) : Pr P T Q A U :=
  .seq (uclear (rg .wn)) (.seq (.act (.push (.rt (rg .wn)) (fun _ => tick) .done))
    (.seq (tblHost rg code out) (clearWords ports)))

theorem tableStreamHost_exec (rg : TblR n → Fin T) (hrg : Function.Injective rg)
    (ports : List (Fin T)) (hnd : ports.Nodup)
    (hcover : ∀ k ∈ ports, ∃ r, rg r = k) (hinside : ∀ r, rg r ∈ ports)
    (out : Fin T) (hout : out ∉ ports) {V K : ℕ} (hV : 1 ≤ V)
    (code : TblCode n) (st : TblSt n A) (xs : List (Fin (A+4))) (hacc : st.acc = [])
    (hc : TblDo A V 1 code st (fun st' => st'.acc = xs.reverse++st.acc) K)
    (hbound : ∀ r, st.val r < 2^V) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ K*tblC V 1+(2*ports.length+2)*V+2*xs.length+2*ports.length+6 ∧
      Exec body (tableStreamHost rg ports out code) (mk v S) m
        (mk v' {S with R := fun r => if r ∈ ports then [] else if r = out then xs++S.R r else S.R r}) := by
  have hsep : ∀ r, rg r ≠ out := by intro r he; exact hout (he ▸ hinside r)
  have hwidth : S.R (rg .wn) = List.replicate V tick := hS .wn
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec (body := body) (rg .wn) v S
  let S₁ : Stacks T A := {S with R := Function.update S.R (rg .wn) []}
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R (rg .wn) [tick]}
  have he₁' : Exec body (uclear (rg .wn)) (mk v S) (2*V+2) (mk v₁ S₁) := by
    simpa [hwidth,S₁] using he₁
  have he₂ : Exec body (.act (.push (.rt (rg .wn)) (fun _ => tick) .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    simpa [S₂,S₁,Action.run,update_rt] using
      Exec.act (body := body) (.push (.rt (rg .wn)) (fun _ => tick) .done) (mk v₁ S₁)
  have hh₂ : tblHolds rg S₂ (tblRho V (List.replicate V tick) [tick] st) := by
    intro r
    by_cases hr : r = .wn
    · subst r; simp [S₂,S₁,tblRho]
    · have hn := hrg.ne hr
      have hh := hS r
      cases r <;> simp_all [S₂,S₁,tblRho]
  obtain ⟨v₃,S₃,m₃,st',hp,hu₃,hm₃,he₃,ho,hh₃,hin,hout₃,hl,hf⟩ :=
    tblHost_runs (body := body) hrg hsep (List.replicate V tick) [tick] (by simp) (by simp)
      hV hc hbound v₁ S₂ hh₂
  rw [hp,hacc,List.append_nil,List.length_reverse] at hm₃
  rw [hp,hacc,List.append_nil,List.reverse_reverse] at ho
  have hlen (k : Fin T) (hk : k ∈ ports) : (S₃.R k).length ≤ V := by
    obtain ⟨r,rfl⟩ := hcover k hk
    rw [hh₃ r]
    cases r <;> simp [tblRho,binSyms,hV]
  have hsum : (ports.map (fun k => (S₃.R k).length)).sum ≤ ports.length*V := by
    have hh : ∀ ls : List (Fin T), (∀ k ∈ ls, (S₃.R k).length ≤ V) →
        (ls.map (fun k => (S₃.R k).length)).sum ≤ ls.length*V := by
      intro ls
      induction ls with
      | nil => simp
      | cons k ks ih =>
        intro hb
        have ht := ih (fun j hj => hb j (by simp [hj]))
        have hk := hb k (by simp)
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith only [ht,hk]
    exact hh ports hlen
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) ports hnd v₃ S₃
  refine ⟨v₄,(2*V+2)+(1+(m₃+(2*(ports.map (fun k => (S₃.R k).length)).sum+2*ports.length+1))),
    hu₄.trans (hu₃.trans hu₁),by nlinarith only [hsum,hm₃],
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  apply congrArg (mk v₄)
  refine Stacks.ext hin hout₃ hl ?_
  funext r
  by_cases hr : r ∈ ports
  · simp [hr]
  · have hwr : r ≠ rg .wn := by intro he; exact hr (he ▸ hinside .wn)
    have hrg' : ∀ k, rg k ≠ r := by intro k he; exact hr (he ▸ hinside k)
    by_cases hor : r = out
    · subst r; simpa [hout,S₂,S₁,Ne.symm (hsep .wn)] using ho
    · simp [hr,hor,hf r hor hrg',S₂,S₁,hwr]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
