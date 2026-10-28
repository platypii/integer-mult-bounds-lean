module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundScalarSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellParameterArithmetic
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies

/-! Generate the four rounding counters from binary scalar inputs. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def roundHeaderSource : Fin 4 → Fin 8 := ![0,6,5,7]
def roundHeaderValues (w q p j E : ℕ) : Fin 4 → ℕ :=
  ![w,q-p+j,p+E+5,w-(q-p+j)-(p+E+5)]
def roundHeaderAssignments {T : ℕ} (ports : Fin 4 → Fin T) : List (Fin 8 × Fin T) :=
  (List.finRange 4).map (fun i => (roundHeaderSource i,ports i))

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def installRoundHeaders (rg : TblR 8 → Fin T) (ports : Fin 4 → Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg tblRoundScalars) (tblUnaryCopies rg (roundHeaderAssignments ports))

theorem installRoundHeaders_exec (rg : TblR 8 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i)
    {W w q p j E : ℕ} (wl : List (Fin (A+4))) (hwl : wl.length = W)
    (st : TblSt 8 A) (h0 : st.val 0 = w) (h1 : st.val 1 = q) (h2 : st.val 2 = p)
    (h3 : st.val 3 = j) (h4 : st.val 4 = E)
    (hp : p ≤ q) (hsize : q-p+j+(p+E+5) ≤ w) (hroom : w < 2^W)
    (hfit : ∀ i, st.val i < 2^W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl [] st)) :
    ∃ v' S' n z, v'.user = v.user ∧
      n ≤ 10*tblC W 0+unaryCopiesCost W (roundHeaderValues w q p j E)
        ((List.finRange 4).map (fun i => (i,ports i))) ∧
      Exec body (installRoundHeaders rg ports) (mk v S) n (mk v' S') ∧
      tblHolds rg S' (tblRho W wl [] z) ∧
      (∀ i : Fin 5, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.acc = st.acc ∧ (∀ i, z.val i < 2^W) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i, S'.R (ports i) = List.replicate (roundHeaderValues w q p j E i) Node.tick++S.R (ports i)) ∧
      ∀ k, (∀ r, rg r ≠ k) → (∀ i, ports i ≠ k) → S'.R k = S.R k := by
  have hc := tblDo_with_fits (tblRoundScalars_do (e := 0) st h0 h1 h2 h3 h4 hp hsize hroom) hfit
  obtain ⟨z,⟨⟨hkeep,hk,hd,hdrop,hacc⟩,hfitZ⟩,hrun⟩ := hc.host (body := body) hrg wl [] hwl rfl
    (Nat.zero_le W) hfit
  have hvalue (i : Fin 4) : z.val (roundHeaderSource i) = roundHeaderValues w q p j E i := by
    fin_cases i
    · exact (hkeep 0).trans h0
    · exact hd
    · exact hk
    · exact hdrop
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh₁,hframe⟩ := hrun v S hS
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := tblUnaryCopies_exec (body := body) hrg wl [] z hfitZ
    (roundHeaderAssignments ports) (by
      intro x hx r
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact hsep i r) v₁ S₁ hh₁
  let S₂ : Stacks T A := {S₁ with R := unaryCopiesR z.val S₁.R (roundHeaderAssignments ports)}
  have hcost : unaryCopiesCost W z.val (roundHeaderAssignments ports) =
      unaryCopiesCost W (roundHeaderValues w q p j E) ((List.finRange 4).map (fun i => (i,ports i))) := by
    simp only [unaryCopiesCost,roundHeaderAssignments,List.map_map,Function.comp_def,hvalue]
  refine ⟨v₂,S₂,n₁+n₂,z,hu₂.trans hu₁,Nat.add_le_add hn₁ (hn₂.trans_eq hcost),
    Exec.seq he₁ he₂,?_,hkeep,hacc,hfitZ,hframe.1,hframe.2.1,hframe.2.2.1,?_,?_⟩
  · intro r
    rw [show S₂.R (rg r) = S₁.R (rg r) from unaryCopiesR_off z.val S₁.R _ _ (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact (hsep i r).symm)]
    exact hh₁ r
  · intro i
    have hnd : ((roundHeaderAssignments ports).map Prod.snd).Nodup := by
      simpa only [roundHeaderAssignments,List.map_map,Function.comp_def] using (List.nodup_finRange 4).map hports
    have hh := unaryCopiesR_at z.val S₁.R (roundHeaderAssignments ports) hnd
      (roundHeaderSource i,ports i) (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
    change S₂.R (ports i) = _ at hh
    rw [hh,hvalue,hframe.2.2.2 (ports i) (hsep i)]
  · intro k hk hp
    exact (unaryCopiesR_off z.val S₁.R _ k (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact hp i)).trans (hframe.2.2.2 k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
