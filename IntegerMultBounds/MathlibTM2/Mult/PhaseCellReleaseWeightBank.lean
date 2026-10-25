module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableHost

/-! Release a retained table bank once, after its last emitted weight row. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def releaseWeightBank : Pr P₀ 117 Q A U := clearWords coefficientPorts

theorem releaseWeightBank_exec (V w : ℕ) (st : TblSt 48 A) (hw : w ≤ V) (ha : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds coefficientReg S (tblRho V (List.replicate V tick) (List.replicate w tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 126*V+127 ∧
      Exec body releaseWeightBank (mk v S) m
        (mk v' { S with R := fun k => if k.val < 63 then [] else S.R k }) := by
  obtain ⟨v', hv, he⟩ := clearWords_exec (body := body) coefficientPorts coefficientPorts_nodup v S
  have hlen (k : Fin 117) (hk : k ∈ coefficientPorts) : (S.R k).length ≤ V := by
    obtain ⟨r, rfl⟩ := coefficientReg_covers k (mem_coefficientPorts k |>.mp hk)
    rw [hS r]
    cases r <;> simp [tblRho, ha, hw]
  have bound (rs : List (Fin 117)) : (∀ k ∈ rs, (S.R k).length ≤ V) →
      (rs.map (fun k => (S.R k).length)).sum ≤ rs.length*V := by
    induction rs with
    | nil => simp
    | cons k rs ih =>
      intro h
      simpa [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_mul, Nat.one_mul, Nat.add_comm] using Nat.add_le_add (h k (by simp)) (ih (fun j hj => h j (by simp [hj])))
  have hh := bound coefficientPorts hlen
  have hc : coefficientPorts.length = 63 := by simp [coefficientPorts]
  have hh' : (coefficientPorts.map (fun k => (S.R k).length)).sum ≤ 63*V := by simpa only [hc] using hh
  refine ⟨v', 2*(coefficientPorts.map (fun k => (S.R k).length)).sum+2*coefficientPorts.length+1,
    hv, by rw [hc]; omega, he.cast rfl ?_⟩
  congr 1
  simp only [mem_coefficientPorts]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
