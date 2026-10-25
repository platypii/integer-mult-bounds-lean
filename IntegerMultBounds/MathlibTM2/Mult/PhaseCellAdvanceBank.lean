module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceHost
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad
public import IntegerMultBounds.MathlibTM2.Fast.TableLoad
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Construct and release the small forward-advance table from a width source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def initializeAdvanceBank : Pr P₀ 117 Q A U :=
  chirpBankLoad advanceReg (fun _ => 106) 115 115

/-- All zero-valued table variables and both word counters are constructed. -/
theorem initializeAdvanceBank_exec (V : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (hz : S.R 106 = [])
    (hblank : ∀ r, S.R (advanceReg r) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body initializeAdvanceBank (mk v S) (32 * V + 41)
        (mk v' { S with R := chirpBankLoadR advanceReg (fun _ => 106) V V (fun _ => 0) S.R }) ∧
      tblHolds advanceReg { S with R := chirpBankLoadR advanceReg (fun _ => 106) V V (fun _ => 0) S.R }
        (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨fun _ => 0, []⟩) := by
  have hoff (k : Fin 117) (hk : 19 ≤ k.val) : ∀ r, advanceReg r ≠ k := by
    intro r he
    have hr := advanceReg_range r
    rw [he] at hr
    omega
  obtain ⟨v', hu, he⟩ := chirpBankLoad_exec (body := body) advanceReg advanceReg_injective
    (fun _ => 106) 115 115 (hoff 115 (by decide)) (hoff 115 (by decide))
    (fun _ => hoff 106 (by decide)) V V (fun _ => 0) (fun _ => 0) (by simp) (by simp)
    v S hV hV (by simpa [binSyms] using hz) hblank
  have hcost : chirpBankLoadCost advanceReg (fun _ : Fin 4 => 106) V V (fun _ => 0) =
      32 * V + 41 := by
    simp [chirpBankLoadCost, chirpBankCopiesCost, chirpBankInputAssignments,
      ]
    ring
  exact ⟨v', hu, he.cast hcost rfl,
    chirpBankLoad_holds advanceReg advanceReg_injective (fun _ => 106) V V (fun _ => 0) S hblank⟩

def advancePorts : List (Fin 117) := List.ofFn (fun i : Fin 19 => (⟨i.val, by omega⟩ : Fin 117))

theorem mem_advancePorts (k : Fin 117) : k ∈ advancePorts ↔ k.val < 19 := by
  simp only [advancePorts, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩; exact i.isLt
  · intro hk; exact ⟨⟨k.val, hk⟩, Fin.ext rfl⟩

theorem advanceReg_covers (k : Fin 117) (hk : k.val < 19) : ∃ r, advanceReg r = k := by
  by_cases hv : k.val < 4
  · exact ⟨.v ⟨k.val, hv⟩, Fin.ext rfl⟩
  by_cases h4 : k.val = 4
  · exact ⟨.wr, Fin.ext h4.symm⟩
  by_cases h5 : k.val = 5
  · exact ⟨.wn, Fin.ext h5.symm⟩
  by_cases h6 : k.val = 6
  · exact ⟨.acc, Fin.ext h6.symm⟩
  exact ⟨.z ⟨k.val-7, by omega⟩, Fin.ext (by simp [advanceReg]; omega)⟩


def releaseAdvanceBank : Pr P₀ 117 Q A U := clearWords advancePorts

theorem releaseAdvanceBank_exec (V : ℕ) (value : Fin 4 → ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds advanceReg S (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨value, []⟩)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 38*V+39 ∧
      Exec body releaseAdvanceBank (mk v S) m
        (mk v' { S with R := fun k => if k.val < 19 then [] else S.R k }) := by
  have hlen (k : Fin 117) (hk : k ∈ advancePorts) : (S.R k).length ≤ V := by
    obtain ⟨r, rfl⟩ := advanceReg_covers k ((mem_advancePorts k).mp hk)
    rw [hS r]
    cases r <;> simp [tblRho, binSyms]
  have hsum : (advancePorts.map (fun k => (S.R k).length)).sum ≤ 19*V := by
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
    simpa [advancePorts] using hh advancePorts hlen
  have hnd : advancePorts.Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j he
    apply Fin.ext
    exact congrArg (fun k : Fin 117 => k.val) he
  obtain ⟨v', hu, he⟩ := clearWords_exec (body := body) advancePorts hnd v S
  refine ⟨v', 2*(advancePorts.map (fun k => (S.R k).length)).sum+2*advancePorts.length+1,
    hu, ?_, ?_⟩
  · simp only [advancePorts, List.length_ofFn] at *
    omega
  · simpa only [releaseAdvanceBank, mem_advancePorts] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
