module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseCallerWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClearInverseScalars

/-! Release scalar-generated headers at arbitrary disjoint caller ports. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def inverseReleaseCost (W : ℕ) (values : Fin 10 → ℕ) : ℕ :=
  2*((List.finRange 10).map values).sum+21+17*tblC W 0

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def releaseInverseHeaders (rg : TblR 25 → Fin T) (ports : Fin 10 → Fin T) : Pr P T Q A U :=
  .seq (clearWords ((List.finRange 10).map ports)) (tblCompile rg tblClearInverseScalars)

theorem releaseInverseHeaders_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 10 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i)
    {W : ℕ} (wl : List (Fin (A+4))) (hwl : wl.length = W)
    (st initial : TblSt 25 A) (values : Fin 10 → ℕ)
    (hkeep : ∀ i : Fin 25, i.val < 8 → st.val i = initial.val i)
    (hzero : ∀ i : Fin 25, 8 ≤ i.val → initial.val i = 0) (hacc : st.acc = initial.acc)
    (hfit : ∀ i, st.val i < 2^W) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl [] st))
    (hheaders : ∀ i, (S.R (ports i)).length = values i) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ inverseReleaseCost W values ∧
      Exec body (releaseInverseHeaders rg ports) (mk v S) n (mk v' S') ∧
      tblHolds rg S' (tblRho W wl [] initial) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, (∀ r, rg r ≠ k) →
        S'.R k = if k ∈ (List.finRange 10).map ports then [] else S.R k := by
  let regs := (List.finRange 10).map ports
  have hnd : regs.Nodup := (List.nodup_finRange 10).map hports
  have hnot (r : TblR 25) : rg r ∉ regs := by
    intro hr
    obtain ⟨i,_,he⟩ := List.mem_map.mp hr
    exact hsep i r he.symm
  obtain ⟨v₁,hu₁,he₁⟩ := clearWords_exec (body := body) regs hnd v S
  let S₁ : Stacks T A := {S with R := fun i => if i ∈ regs then [] else S.R i}
  have hh₁ : tblHolds rg S₁ (tblRho W wl [] st) := by
    intro r
    simpa [S₁,hnot] using hS r
  have hc := tblClearInverseScalars_do (A := A) (W := W) (e := 0) st initial hkeep hzero hacc
  obtain ⟨z,hz,hrun⟩ := hc.host (body := body) hrg wl [] hwl rfl (Nat.zero_le W) hfit
  subst z
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hh₂,hframe⟩ := hrun v₁ S₁ hh₁
  have hsum : (regs.map fun r => (S.R r).length).sum = ((List.finRange 10).map values).sum := by
    simp only [regs,List.map_map,Function.comp_def,hheaders]
  refine ⟨v₂,S₂,(2*(regs.map fun r => (S.R r).length).sum+2*regs.length+1)+n₂,
    hu₂.trans hu₁,?_,Exec.seq he₁ he₂,hh₂,hframe.1,hframe.2.1,hframe.2.2.1,?_⟩
  · rw [hsum]
    simp only [inverseReleaseCost,regs,List.length_map,List.length_finRange]
    have hn₂' : n₂ ≤ 17*tblC W 0 := hn₂
    omega
  · intro k hk
    exact hframe.2.2.2 k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
