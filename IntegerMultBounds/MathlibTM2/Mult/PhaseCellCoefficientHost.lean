module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientStream
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Execute the numerical coefficient stream and release its table workspace

The binary table headers are owned setup inputs. All registers outside the
63-register table bank survive, with the distance vector prefixed to tape 110.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def coefficientReg : TblR 48 → Fin 117
  | .v i => ⟨i.val, by omega⟩
  | .wr => 48 | .wn => 49 | .acc => 50
  | .z i => ⟨51 + i.val, by omega⟩

theorem coefficientReg_injective : Function.Injective coefficientReg := by
  intro x y h
  cases x <;> cases y <;> simp_all [coefficientReg, Fin.ext_iff]
  all_goals omega

theorem coefficientReg_range (r : TblR 48) : (coefficientReg r).val < 63 := by
  cases r <;> simp [coefficientReg] <;> omega

theorem coefficientReg_covers (k : Fin 117) (hk : k.val < 63) : ∃ r, coefficientReg r = k := by
  by_cases hv : k.val < 48
  · exact ⟨.v ⟨k.val, hv⟩, Fin.ext rfl⟩
  by_cases h48 : k.val = 48
  · exact ⟨.wr, Fin.ext h48.symm⟩
  by_cases h49 : k.val = 49
  · exact ⟨.wn, Fin.ext h49.symm⟩
  by_cases h50 : k.val = 50
  · exact ⟨.acc, Fin.ext h50.symm⟩
  refine ⟨.z ⟨k.val - 51, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [coefficientReg]
  omega

def coefficientPorts : List (Fin 117) := List.ofFn fun i : Fin 63 => ⟨i.val, by omega⟩

@[simp] theorem mem_coefficientPorts (k : Fin 117) : k ∈ coefficientPorts ↔ k.val < 63 := by
  simp only [coefficientPorts, List.mem_ofFn]
  constructor
  · rintro ⟨i, hi⟩
    have he := congrArg (fun j : Fin 117 => j.val) hi
    have hh := i.isLt
    change i.val = k.val at he
    omega
  · intro hk
    exact ⟨⟨k.val, hk⟩, Fin.ext rfl⟩

theorem coefficientPorts_nodup : coefficientPorts.Nodup := by
  rw [coefficientPorts, List.nodup_ofFn]
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 117 => k.val) h)

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def coefficientHost : Pr P₀ 117 Q A U :=
  .seq (tblHost coefficientReg coefficientStreamCode 110) (clearWords coefficientPorts)

/-- The only non-workspace change is the constructed distance vector. -/
theorem coefficientHost_exec {V w P s t u band L : ℕ} (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hs' : st.val 34 = s) (ht' : st.val 35 = t)
    (hu' : st.val 36 = u) (hb' : st.val 38 = band) (hL' : st.val 42 = L)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (hV : u * t * (L + 1) ^ 2 * 2 ^ (13 * P + 8) < 2 ^ V)
    (hstV : ∀ j, st.val j < 2 ^ V) (hacc : st.acc = [])
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = V) (hnl : nl.length = w) (hw : w ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hS : tblHolds coefficientReg S (tblRho V wl nl st)) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (L * (310 * P + 114) + (160 * P + 450)) * tblC V w + 2 * (L * w) + 126 * V + 129 ∧
      Exec body coefficientHost (mk v S) m
        (mk v' { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
          (cstream A w (distanceFactorWords P s t u band L) ++ S.R 110) else S.R k) }) := by
  have hout : ∀ r, coefficientReg r ≠ (110 : Fin 117) := by
    intro r he
    have hr := coefficientReg_range r
    rw [he] at hr
    omega
  obtain ⟨v₁, S₁, m₁, st', hpost, hu₁, hm₁, he₁, houtput, hholds, hin, houtS, hleft, hframe⟩ :=
    tblHost_runs (body := body) coefficientReg_injective hout wl nl hwl hnl hw
      (coefficientStreamCode_do st hP' hs' ht' hu' hb' hL' hP hs hst hu hV) hstV v S hS
  rw [hpost, hacc, List.append_nil, List.length_reverse, length_cstream, distanceFactorWords_length] at hm₁
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
    hu₂.trans hu₁, ?_, (Exec.seq he₁ he₂).cast rfl ?_⟩
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
