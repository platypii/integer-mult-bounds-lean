module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseInverseHeaders

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
  obtain ⟨v',S',n,hu,hn,he,hh,hinp,hout,hL,hframe⟩ :=
    releaseInverseHeaders_exec (body := body) inverseScalarReg inverseScalarReg_injective
      inverseMasterPort inverseMasterPort_injective inverseScalarReg_master
      wl hwl st initial values hkeep hzero hacc hfit v S hS hheaders
  exact ⟨v',S',n,hu,hn,he,hh,hinp,hout,hL,
    fun i => hframe (inverseCoreReg i) (fun r => inverseScalarReg_core r i)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
