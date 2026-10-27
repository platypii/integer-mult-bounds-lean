module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseCallerWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClearInverseScalars

/-! Release generated unary masters and restore the scalar setup bank after the retained solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def inverseMasterRegs : List (Fin 264) := (List.finRange 10).map inverseMasterPort

theorem inverseMasterRegs_nodup : inverseMasterRegs.Nodup :=
  (List.nodup_finRange 10).map inverseMasterPort_injective

theorem inverseScalarReg_not_master (r : TblR 25) : inverseScalarReg r ∉ inverseMasterRegs := by
  intro hr
  obtain ⟨i,_,he⟩ := List.mem_map.mp hr
  exact inverseScalarReg_master i r he.symm

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 264 Q A U}

def releaseInverseCaller : Pr P 264 Q A U :=
  .seq (clearWords inverseMasterRegs) (tblCompile inverseScalarReg tblClearInverseScalars)

def inverseReleaseCost (W : ℕ) (values : Fin 10 → ℕ) : ℕ :=
  2*((List.finRange 10).map values).sum+21+17*tblC W 0

theorem releaseInverseCaller_exec {W : ℕ} (wl : List (Fin (A+4))) (hwl : wl.length = W)
    (st initial : TblSt 25 A) (values : Fin 10 → ℕ)
    (hkeep : ∀ i : Fin 25, i.val < 8 → st.val i = initial.val i)
    (hzero : ∀ i : Fin 25, 8 ≤ i.val → initial.val i = 0) (hacc : st.acc = initial.acc)
    (hfit : ∀ i, st.val i < 2^W) (v : HS 264 Q A U) (S : Stacks 264 A)
    (hS : tblHolds inverseScalarReg S (tblRho W wl [] st))
    (hheaders : ∀ i, (S.R (inverseMasterPort i)).length = values i) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ inverseReleaseCost W values ∧
      Exec body releaseInverseCaller (mk v S) n (mk v' S') ∧
      tblHolds inverseScalarReg S' (tblRho W wl [] initial) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ i, S'.R (inverseCoreReg i) = if inverseCoreReg i ∈ inverseMasterRegs then [] else S.R (inverseCoreReg i) := by
  obtain ⟨v₁,hu₁,he₁⟩ := clearWords_exec (body := body) inverseMasterRegs inverseMasterRegs_nodup v S
  let S₁ : Stacks 264 A := {S with R := fun i => if i ∈ inverseMasterRegs then [] else S.R i}
  have hh₁ : tblHolds inverseScalarReg S₁ (tblRho W wl [] st) := by
    intro r
    simpa [S₁,inverseScalarReg_not_master] using hS r
  have hc := tblClearInverseScalars_do (A := A) (W := W) (e := 0) st initial hkeep hzero hacc
  obtain ⟨z,hz,hrun⟩ := hc.host (body := body) inverseScalarReg_injective wl [] hwl rfl (Nat.zero_le W) hfit
  subst z
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hh₂,hframe⟩ := hrun v₁ S₁ hh₁
  have hsum : (inverseMasterRegs.map fun r => (S.R r).length).sum = ((List.finRange 10).map values).sum := by
    simp only [inverseMasterRegs,List.map_map,Function.comp_def,hheaders]
  refine ⟨v₂,S₂,(2*(inverseMasterRegs.map fun r => (S.R r).length).sum+2*inverseMasterRegs.length+1)+n₂,
    hu₂.trans hu₁,?_,Exec.seq he₁ he₂,hh₂,hframe.1,hframe.2.1,hframe.2.2.1,?_⟩
  · rw [hsum]
    simp only [inverseReleaseCost,inverseMasterRegs,List.length_map,List.length_finRange]
    have hn₂' : n₂ ≤ 17*tblC W 0 := hn₂
    omega
  · intro i
    exact hframe.2.2.2 (inverseCoreReg i) (fun r => inverseScalarReg_core r i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
