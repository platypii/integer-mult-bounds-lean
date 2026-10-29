module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryGuardIntervalCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def intervalGuardReg : TblR 17 → Fin 117
  | .v i => ⟨i.val,by omega⟩
  | .wr => 17 | .wn => 18 | .acc => 19
  | .z i => ⟨20+i.val,by omega⟩

theorem intervalGuardReg_injective : Function.Injective intervalGuardReg := by
  intro x y h
  cases x <;> cases y <;> simp_all [intervalGuardReg,Fin.ext_iff]
  all_goals omega

theorem intervalGuardReg_range (r : TblR 17) : (intervalGuardReg r).val < 32 := by
  cases r <;> simp [intervalGuardReg] <;> omega

def intervalGuardPorts : List (Fin 117) := List.ofFn (fun i : Fin 32 => (⟨i.val,by omega⟩ : Fin 117))

theorem mem_intervalGuardPorts (k : Fin 117) : k ∈ intervalGuardPorts ↔ k.val < 32 := by
  simp only [intervalGuardPorts,List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩; exact i.isLt
  · intro hk; exact ⟨⟨k.val,hk⟩,Fin.ext rfl⟩

theorem intervalGuardReg_covers (k : Fin 117) (hk : k.val < 32) : ∃ r, intervalGuardReg r = k := by
  by_cases hv : k.val < 17
  · exact ⟨.v ⟨k.val,hv⟩,Fin.ext rfl⟩
  by_cases h17 : k.val = 17
  · exact ⟨.wr,Fin.ext h17.symm⟩
  by_cases h18 : k.val = 18
  · exact ⟨.wn,Fin.ext h18.symm⟩
  by_cases h19 : k.val = 19
  · exact ⟨.acc,Fin.ext h19.symm⟩
  exact ⟨.z ⟨k.val-20,by omega⟩,Fin.ext (by simp [intervalGuardReg]; omega)⟩

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def releaseIntervalGuardBank : Pr P₀ 117 Q A U := clearWords intervalGuardPorts

theorem releaseIntervalGuardBank_exec (V W : ℕ) (hWV : W ≤ V) (value : Fin 17 → ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds intervalGuardReg S (tblRho V (List.replicate V tick) (List.replicate W tick) ⟨value, []⟩)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 64*V+65 ∧
      Exec body releaseIntervalGuardBank (mk v S) m
        (mk v' { S with R := fun k => if k.val < 32 then [] else S.R k }) := by
  have hlen (k : Fin 117) (hk : k ∈ intervalGuardPorts) : (S.R k).length ≤ V := by
    obtain ⟨r, rfl⟩ := intervalGuardReg_covers k ((mem_intervalGuardPorts k).mp hk)
    rw [hS r]
    cases r <;> simp [tblRho, binSyms, hWV]
  have hsum : (intervalGuardPorts.map (fun k => (S.R k).length)).sum ≤ 32*V := by
    have hh : ∀ rs : List (Fin 117), (∀ k ∈ rs, (S.R k).length ≤ V) →
        (rs.map (fun k => (S.R k).length)).sum ≤ rs.length*V := by
      intro rs
      induction rs with
      | nil => simp
      | cons k rs ih =>
        intro hb
        have ht := ih (fun j hj => hb j (by simp [hj]))
        have hk := hb k (by simp)
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        nlinarith only [ht, hk]
    simpa [intervalGuardPorts] using hh intervalGuardPorts hlen
  have hnd : intervalGuardPorts.Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j he
    apply Fin.ext
    exact congrArg (fun k : Fin 117 => k.val) he
  obtain ⟨v', hu, he⟩ := clearWords_exec (body := body) intervalGuardPorts hnd v S
  refine ⟨v', 2*(intervalGuardPorts.map (fun k => (S.R k).length)).sum+2*intervalGuardPorts.length+1,
    hu, ?_, ?_⟩
  · simp only [intervalGuardPorts, List.length_ofFn] at *
    omega
  · simpa only [releaseIntervalGuardBank, mem_intervalGuardPorts] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
