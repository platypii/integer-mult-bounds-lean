module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassController
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloGroupHostStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginController
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth

/-! Initialize the ambient phase constants and generate the origins and count
of one positive clipped length class. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloClassControllerWorkspace (V B : ℕ) : ℕ :=
  3*tblC V V+countedOriginWorkspace V V B

theorem haloClassController_exec_within {V s t band a b L : ℕ}
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hA : 4 ≤ A) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V
      (List.replicate V tick)
      (List.replicate V tick) (haloClassRawState A s t band a b L)))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (36*(t-s+1)+9)*tblC V V + (haloLengthGroup s t band a b L).length*(8*V+6)+6 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          haloClassControllerWorkspace V (haloLengthGroup s t band a b L).length)
        depth haloClassController (mk v S) m (mk v' S')) ∧
      S'.R 109 = haloOriginPackets A V s t band a b L ++ S.R 109 ∧
      S'.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick ∧
      tblHolds originReg S' (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^V) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 116 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  have hpkt : s < 2^V := by nlinarith only [hwide, hst]
  have hbound := haloClassRawState_bounded (A := A) has hbs hLs hst hband hwide
  have hc := haloClassInitCode_do (A := A) (W := V) (w := V) (a := a) (b := b) (L := L) hs hst hwide
  obtain ⟨st₁,k,hbig,⟨heq,hb₁⟩,hk⟩ := hc.bounded hbound
  subst heq
  obtain ⟨v₁,S₁,m₁,hu₁,hm₁,he₁,hh₁,hf₁⟩ :=
    tblCompile_runs_within (body := body) originReg_injective
      (List.replicate V tick) (List.replicate V tick) (by simp) (by simp) le_rfl hbig hbound v S hS
  have hm₁ := hm₁.trans (Nat.mul_le_mul_right (tblC V V) hk)
  obtain ⟨v₂, S₂, m₂, st₂, hu₂, hm₂, he₂, hout, hcount, hh₂, hb₂, hi₂, ho₂, hl₂, hframe⟩ :=
    haloGroupCountedHost_exec_within (body := body) (s := s) (t := t) (band := band) (a := a) (b := b) (L := L)
      (haloClassReadyState A s t band a b L)
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      (by simp [haloClassReadyState,haloClassRawState])
      has hbs hs hst hL hwide hpkt.le le_rfl hA (by
        have hv : V ≠ 0 := by intro he; rw [he] at hwide; simp at hwide
        omega) hb₁ rfl v₁ S₁ hh₁
      (by rw [hf₁.2.2.2 104 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega),h104])
      (by rw [hf₁.2.2.2 106 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega),h106])
      (by rw [hf₁.2.2.2 116 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega),h116])
  refine ⟨v₂, S₂, m₁+m₂, st₂, hu₂.trans hu₁, ?_, ?_, ?_, hcount, hh₂, hb₂,
    hi₂.trans hf₁.1, ho₂.trans hf₁.2.1, hl₂.trans hf₁.2.2.1, ?_⟩
  · nlinarith only [hm₁, hm₂]
  · intro depth
    have ht₁ : ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*tblC V V)
        depth (tblCompile originReg originInitCode) (mk v S) m₁ (mk v₁ S₁) := by
      simpa only [haloClassReadyState,haloClassRawState,List.length_nil,Nat.sub_self,Nat.add_zero]
        using he₁ depth
    exact mn_seq_within_add ht₁ (he₂ depth)
  · rw [hout, hf₁.2.2.2 109 (fun r he => by have hh := originReg_range r; rw [he] at hh; omega)]
  · intro k hk109 hk116 hk
    exact (hframe k hk109 hk116 hk).trans (hf₁.2.2.2 k hk)


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
