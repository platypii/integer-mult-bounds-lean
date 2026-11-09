module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableHost
public import IntegerMultBounds.MathlibTM2.Fast.TableHostStock
public import IntegerMultBounds.MathlibTM2.Host.ClearBankExcept

/-! Table stream retirement allocates no symbols and preserves the shared compiler reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem coefficientTableHost_trace_within {code : TblCode 48}
    {v₀ v₁ v₂ : HS 117 Q A U} {S₀ S₁ S₂ : Stacks 117 A} {m₁ m₂ depth cap : ℕ}
    (h₁ : ExecWithin body (fun d z => mnSize z+d ≤ cap) depth
      (tblHost coefficientReg code 110) (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : Exec body (clearWords coefficientPorts) (mk v₁ S₁) m₂ (mk v₂ S₂)) :
    ExecWithin body (fun d z => mnSize z+d ≤ cap) depth
      (coefficientTableHost code) (mk v₀ S₀) (m₁+m₂) (mk v₂ S₂) := by
  exact .seq h₁ (mn_native_exec_within h₂ 0 (clearWords_native_zero _) depth cap (by
    have hf := h₁.final
    omega))

theorem coefficientTableHost_exec_within {V w K : ℕ} (code : TblCode 48) (st : TblSt 48 A)
    (xs : List (Fin (A + 4)))
    (hcode : TblDo A V w code st (fun st' => st'.acc = xs.reverse ++ st.acc) K)
    (hstV : ∀ j, st.val j < 2 ^ V) (hacc : st.acc = [])
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = V) (hnl : nl.length = w) (hw : w ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hS : tblHolds coefficientReg S (tblRho V wl nl st)) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ K * tblC V w + 2 * xs.length + 126 * V + 129 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*xs.length+3*tblC V w+2)
        depth (coefficientTableHost code) (mk v S) m
        (mk v' { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
          (xs ++ S.R 110) else S.R k) })) := by
  have hout : ∀ r, coefficientReg r ≠ (110 : Fin 117) := by
    intro r he
    have hr := coefficientReg_range r
    rw [he] at hr
    omega
  obtain ⟨v₁, S₁, m₁, st', hpost, hu₁, hm₁, he₁, houtput, hholds, hin, houtS, hleft, hframe⟩ :=
    tblHost_runs_within (body := body) coefficientReg_injective hout wl nl hwl hnl hw
      hcode hstV v S hS
  rw [hpost, hacc, List.append_nil, List.length_reverse] at hm₁ he₁
  rw [hpost, hacc, List.append_nil, List.reverse_reverse] at houtput
  obtain ⟨v₂, hu₂, he₂⟩ := clearWords_exec (body := body) coefficientPorts coefficientPorts_nodup v₁ S₁
  have hlen (k : Fin 117) (hk : k ∈ coefficientPorts) : (S₁.R k).length ≤ V := by
    obtain ⟨r, rfl⟩ := coefficientReg_covers k (mem_coefficientPorts k |>.mp hk)
    rw [hholds r]
    cases r <;> simp [tblRho, hwl, hnl, hw]
  have hsum : (coefficientPorts.map (fun k => (S₁.R k).length)).sum ≤ 63 * V := by
    have bound (rs : List (Fin 117)) : (∀ k ∈ rs, (S₁.R k).length ≤ V) →
        (rs.map (fun k => (S₁.R k).length)).sum ≤ rs.length * V := by
      induction rs with
      | nil => simp
      | cons k rs ih =>
        intro h
        simpa [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
          Nat.add_le_add (h k (by simp)) (ih (fun j hj => h j (by simp [hj])))
    simpa [coefficientPorts] using bound coefficientPorts hlen
  refine ⟨v₂, m₁ + (2 * (coefficientPorts.map (fun k => (S₁.R k).length)).sum + 2 * coefficientPorts.length + 1),
    hu₂.trans hu₁, ?_, (fun depth => (coefficientTableHost_trace_within (he₁ depth) he₂).cast rfl ?_)⟩
  · have hports : coefficientPorts.length = 63 := by simp [coefficientPorts]
    rw [hports]
    nlinarith only [hm₁, hsum]
  · congr 1
    ext1
    · exact hin
    · exact houtS
    · exact hleft
    funext k
    by_cases hk : k.val < 63
    · simp [hk]
    by_cases ho : k = 110
    · subst k; simpa using houtput
    simp only [mem_coefficientPorts, hk, ite_false, ho]
    exact hframe k ho (fun r he => by have hr := coefficientReg_range r; rw [he] at hr; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
