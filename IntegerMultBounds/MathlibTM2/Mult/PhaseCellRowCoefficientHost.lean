module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableHost

/-! Host the complete coefficient row using only the existing fresh workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def rowCoefficientReg : TblR 50 → Fin 117
  | .v i => ⟨i.val,by omega⟩
  | .wr => 50 | .wn => 51 | .acc => 52
  | .z i => if i.val < 10 then ⟨53+i.val,by omega⟩ else if i.val = 10 then 108 else 116

theorem rowCoefficientReg_injective : Function.Injective rowCoefficientReg := by
  intro x y he
  cases x <;> cases y <;> simp_all [rowCoefficientReg,Fin.ext_iff]
  all_goals first | omega | (split_ifs at * <;> simp_all [Fin.ext_iff] <;> omega)

theorem rowCoefficientReg_range (r : TblR 50) :
    (rowCoefficientReg r).val < 63 ∨ rowCoefficientReg r = 108 ∨ rowCoefficientReg r = 116 := by
  cases r with
  | v i => left; simp [rowCoefficientReg]; omega
  | wr => decide
  | wn => decide
  | acc => decide
  | z i => simp only [rowCoefficientReg]; split_ifs <;> simp_all <;> omega

def rowCoefficientPorts : List (Fin 117) := coefficientPorts++[108,116]

@[simp] theorem mem_rowCoefficientPorts (k : Fin 117) :
    k ∈ rowCoefficientPorts ↔ k.val < 63 ∨ k = 108 ∨ k = 116 := by
  simp [rowCoefficientPorts,or_assoc]

theorem rowCoefficientPorts_nodup : rowCoefficientPorts.Nodup := by
  simp [rowCoefficientPorts,coefficientPorts_nodup,List.nodup_append,mem_coefficientPorts,
    List.disjoint_left]
  intro a ha
  constructor <;> intro he <;> subst a <;> norm_num at ha

theorem rowCoefficientReg_covers (k : Fin 117) (hk : k ∈ rowCoefficientPorts) : ∃ r, rowCoefficientReg r = k := by
  simp only [mem_rowCoefficientPorts] at hk
  rcases hk with hk | rfl | rfl
  · by_cases h50 : k.val < 50
    · exact ⟨.v ⟨k.val,h50⟩,Fin.ext rfl⟩
    by_cases h50' : k.val = 50
    · exact ⟨.wr,Fin.ext h50'.symm⟩
    by_cases h51 : k.val = 51
    · exact ⟨.wn,Fin.ext h51.symm⟩
    by_cases h52 : k.val = 52
    · exact ⟨.acc,Fin.ext h52.symm⟩
    refine ⟨.z ⟨k.val-53,by omega⟩,?_⟩
    apply Fin.ext
    simp [rowCoefficientReg,show k.val-53 < 10 by omega]
    omega
  · exact ⟨.z 10,by decide⟩
  · exact ⟨.z 11,by decide⟩

theorem rowCoefficientReg_off (k : Fin 117) (hk : k ∉ rowCoefficientPorts) (r : TblR 50) : rowCoefficientReg r ≠ k := by
  intro he
  apply hk
  simpa only [mem_rowCoefficientPorts,he] using rowCoefficientReg_range r

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def rowCoefficientHost (code : TblCode 50) : Pr P 117 Q A U :=
  .seq (tblHost rowCoefficientReg code 111) (clearWords rowCoefficientPorts)

theorem rowCoefficientHost_exec {V w K : ℕ} (code : TblCode 50) (st : TblSt 50 A)
    (xs : List (Fin (A+4)))
    (hcode : TblDo A V w code st (fun st' => st'.acc = xs.reverse++st.acc) K)
    (hstV : ∀ j, st.val j < 2^V) (hacc : st.acc = [])
    (wl nl : List (Fin (A+4))) (hwl : wl.length = V) (hnl : nl.length = w) (hw : w ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hS : tblHolds rowCoefficientReg S (tblRho V wl nl st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ K*tblC V w+2*xs.length+130*V+133 ∧
      Exec body (rowCoefficientHost code) (mk v S) m
        (mk v' {S with R := fun k => if k ∈ rowCoefficientPorts then [] else if k = 111 then xs++S.R 111 else S.R k}) := by
  obtain ⟨v₁,S₁,m₁,st',hpost,hu₁,hm₁,he₁,houtput,hholds,hin,hout,hleft,hframe⟩ :=
    tblHost_runs (body := body) rowCoefficientReg_injective (rowCoefficientReg_off 111 (by simp))
      wl nl hwl hnl hw hcode hstV v S hS
  rw [hpost,hacc,List.append_nil,List.length_reverse] at hm₁
  rw [hpost,hacc,List.append_nil,List.reverse_reverse] at houtput
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) rowCoefficientPorts rowCoefficientPorts_nodup v₁ S₁
  have hlen (k : Fin 117) (hk : k ∈ rowCoefficientPorts) : (S₁.R k).length ≤ V := by
    obtain ⟨r,rfl⟩ := rowCoefficientReg_covers k hk
    rw [hholds r]
    cases r <;> simp [tblRho,hwl,hnl,hw]
  have hsum : (rowCoefficientPorts.map (fun k => (S₁.R k).length)).sum ≤ 65*V := by
    have bound (rs : List (Fin 117)) : (∀ k ∈ rs, (S₁.R k).length ≤ V) →
        (rs.map (fun k => (S₁.R k).length)).sum ≤ rs.length*V := by
      induction rs with
      | nil => simp
      | cons k rs ih =>
        intro h
        simpa [Nat.succ_mul,Nat.add_mul,Nat.add_comm] using
          Nat.add_le_add (h k (by simp)) (ih (fun j hj => h j (by simp [hj])))
    simpa [rowCoefficientPorts,coefficientPorts] using bound rowCoefficientPorts hlen
  refine ⟨v₂,m₁+(2*(rowCoefficientPorts.map (fun k => (S₁.R k).length)).sum+2*rowCoefficientPorts.length+1),
    hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · have hp : rowCoefficientPorts.length = 65 := by simp [rowCoefficientPorts,coefficientPorts]
    rw [hp]
    nlinarith only [hm₁,hsum]
  · apply congrArg (mk v₂)
    refine Stacks.ext hin hout hleft ?_
    funext k
    by_cases hk : k ∈ rowCoefficientPorts
    · simp [hk]
    by_cases ho : k = 111
    · subst k; simpa using houtput
    simp only [hk,ite_false,ho]
    exact hframe k ho (rowCoefficientReg_off k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
