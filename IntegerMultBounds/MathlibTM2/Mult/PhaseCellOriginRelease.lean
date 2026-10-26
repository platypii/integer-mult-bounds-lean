module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnaryOriginController

/-! Release the bounded origin-controller table after its packets and count
have been published outside the table bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def originPorts : List (Fin 117) := List.ofFn (fun i : Fin 31 => (⟨i.val, by omega⟩ : Fin 117))

theorem mem_originPorts (k : Fin 117) : k ∈ originPorts ↔ k.val < 31 := by
  simp only [originPorts, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩; exact i.isLt
  · intro hk; exact ⟨⟨k.val, hk⟩, Fin.ext rfl⟩

theorem originReg_covers (k : Fin 117) (hk : k.val < 31) : ∃ r, originReg r = k := by
  by_cases hv : k.val < 16
  · exact ⟨.v ⟨k.val, hv⟩, Fin.ext rfl⟩
  by_cases h16 : k.val = 16
  · exact ⟨.wr, Fin.ext h16.symm⟩
  by_cases h17 : k.val = 17
  · exact ⟨.wn, Fin.ext h17.symm⟩
  by_cases h18 : k.val = 18
  · exact ⟨.acc, Fin.ext h18.symm⟩
  exact ⟨.z ⟨k.val-19, by omega⟩, Fin.ext (by simp [originReg]; omega)⟩

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def releaseOriginBank : Pr P₀ 117 Q A U := clearWords originPorts

theorem releaseOriginBank_width_exec (V W : ℕ) (hWV : W ≤ V) (value : Fin 16 → ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate W tick) ⟨value, []⟩)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 62*V+63 ∧
      Exec body releaseOriginBank (mk v S) m
        (mk v' { S with R := fun k => if k.val < 31 then [] else S.R k }) := by
  have hlen (k : Fin 117) (hk : k ∈ originPorts) : (S.R k).length ≤ V := by
    obtain ⟨r, rfl⟩ := originReg_covers k ((mem_originPorts k).mp hk)
    rw [hS r]
    cases r <;> simp [tblRho, binSyms, hWV]
  have hsum : (originPorts.map (fun k => (S.R k).length)).sum ≤ 31*V := by
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
    simpa [originPorts] using hh originPorts hlen
  have hnd : originPorts.Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j he
    apply Fin.ext
    exact congrArg (fun k : Fin 117 => k.val) he
  obtain ⟨v', hu, he⟩ := clearWords_exec (body := body) originPorts hnd v S
  refine ⟨v', 2*(originPorts.map (fun k => (S.R k).length)).sum+2*originPorts.length+1,
    hu, ?_, ?_⟩
  · simp only [originPorts, List.length_ofFn] at *
    omega
  · simpa only [releaseOriginBank, mem_originPorts] using he

theorem releaseOriginBank_exec (V : ℕ) (value : Fin 16 → ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨value, []⟩)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 62*V+63 ∧
      Exec body releaseOriginBank (mk v S) m
        (mk v' { S with R := fun k => if k.val < 31 then [] else S.R k }) :=
  releaseOriginBank_width_exec V V le_rfl value v S hS

open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def cleanOriginController : Pr P₀ 117 Q A U :=
  .seq unaryOriginController releaseOriginBank

theorem cleanOriginController_exec (P q w s t u band L : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbSrc : (S.R 100).length = band) (hLSrc : (S.R 102).length = L)
    (hV : (S.R 115).length = weightWorkspaceWidth P q w t u)
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hblank : ∀ r, S.R (originReg r) = []) :
    let V := weightWorkspaceWidth P q w t u
    ∃ v' m, v'.user = v.user ∧
      m ≤ unaryOriginControllerCost P q w s t u band L + (62*V+63) ∧
      Exec body cleanOriginController (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R 109
          (naturalOriginPackets A V s t band L ++ S.R 109)) 116
          (List.replicate (naturalLengthGroup s t band L).length tick)) }) := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₁, S₁, m₁, st₁, hu₁, hm₁, he₁, hout, hcount, hh₁, hb₁, hi₁, ho₁, hl₁, hf₁⟩ :=
    unaryOriginController_exec (body := body) P q w s t u band L hP hs hst hu hband hL hLs hA v S
      hsSrc htSrc hbSrc hLSrc hV h104 h106 h116 hblank
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseOriginBank_exec (body := body) V st₁.val v₁ S₁ hh₁
  refine ⟨v₂, m₁+m₂, hu₂.trans hu₁, by omega, (Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  ext1
  · exact hi₁
  · exact ho₁
  · exact hl₁
  · funext k
    by_cases hlo : k.val < 31
    · have hk109 : k ≠ (109 : Fin 117) := by intro he; subst k; norm_num at hlo
      have hk116 : k ≠ (116 : Fin 117) := by intro he; subst k; norm_num at hlo
      obtain ⟨r, rfl⟩ := originReg_covers k hlo
      simp [hlo, hk109, hk116, hblank r]
    by_cases hk116 : k = 116
    · subst k; simp [hcount]
    by_cases hk109 : k = 109
    · subst k; simp [hout]
    have hoff : ∀ r, originReg r ≠ k := by
      intro r he
      have hr := originReg_range r
      rw [he] at hr
      omega
    simp [hlo, hk109, hk116, hf₁ k hk109 hk116 hoff]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
