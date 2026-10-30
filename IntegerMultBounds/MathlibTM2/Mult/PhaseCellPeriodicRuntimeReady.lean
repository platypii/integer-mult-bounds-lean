module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicPreparedPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicNativeCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallCouplingHeaders

/-! Install native headers and generate arithmetic counters beside the computed
coefficient page. The restored factory bank supplies all physical premises. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

theorem periodicRuntimeReady_exec {Q A precision stage q l s t u band V W N : ℕ}
    {P U : Type} {body : P → Pr P 242 Q A U}
    (xs : List GaussianInt) (v : HS 242 Q A U) (S : Stacks 242 A)
    (h : PackedHaloBetweenInputs precision stage q l s t u band 0 s V (2*q+8) W N
      (extendStacks (by decide) S)) :
    let e : Fin 144 → Fin 242 := Fin.castLE (by decide)
    let B := periodicCouplingPageBank band (2*q+8) xs (periodicCouplingWidthBank q S)
    let T := embStk e B
    let H := embOvr e ({T with R := couplingHeadersR precision q s t u band 0 s T.R} : Stacks 144 A).get B
    let c : Fin 117 → Fin 242 := Fin.castLE (by decide)
    let K := embStk c H
    let G := embOvr c ({K with R := counterR q (2*q+8) K.R} : Stacks 117 A).get H
    ∃ v' n, v'.user = v.user ∧
      n ≤ installCouplingHeadersCost precision q s t u band 0 s+
        (prepareCost q (2*q+8)+6*q+4*band+10) ∧
      Exec body (.seq (embProg e Empty.elim installCouplingHeaders)
        (embProg c Empty.elim couplingReadiness)) (mk v B) n (mk v' G) ∧
      RetainedCouplingReady precision q (2*q+8) s t u band 0 s (S.R 110) (embStk c G) ∧
      PackedPreparedBank q (2*q+8) W N G ∧
      ∀ bo hf df, PackedBoundaryFactorPages bo hf df S → PackedBoundaryFactorPages bo hf df G := by
  dsimp only
  let e : Fin 144 → Fin 242 := Fin.castLE (by decide)
  let B := periodicCouplingPageBank band (2*q+8) xs (periodicCouplingWidthBank q S)
  let T := embStk e B
  have hinj : Function.Injective e := by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin 242 => k.val) he)
  have hsrc : ∀ r ∈ couplingHeaderCopies,
      (T.R r.1).length = couplingHeaderValue precision q s t u band 0 s r.1 := by
    intro r hr
    simp only [couplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [T,B,e,embStk,periodicCouplingPageBank,periodicCouplingWidthBank,couplingHeaderValue,
        packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.precision
    · simpa [T,B,e,embStk,periodicCouplingPageBank,periodicCouplingWidthBank,couplingHeaderValue,
        packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.fraction
    · simpa [T,B,e,embStk,periodicCouplingPageBank,periodicCouplingWidthBank,couplingHeaderValue,
        packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.axis
    · simpa [T,B,e,embStk,periodicCouplingPageBank,periodicCouplingWidthBank,couplingHeaderValue,
        packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.period
    · simpa [T,B,e,embStk,periodicCouplingPageBank,periodicCouplingWidthBank,couplingHeaderValue,
        packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.parameter
    · simpa [T,B,e,embStk,periodicCouplingPageBank,periodicCouplingWidthBank,couplingHeaderValue,
        packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.bandwidth
    · simpa [T,B,e,embStk,periodicCouplingPageBank,periodicCouplingWidthBank,couplingHeaderValue,
        packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.lower
    · simpa [T,B,e,embStk,periodicCouplingPageBank,periodicCouplingWidthBank,couplingHeaderValue,
        packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.upper
  have hleft (k : Fin 144) (hk : k.val < 117) : T.L k = [] := by
    have hh := h.left_low (⟨k.val,by omega⟩ : Fin 248) (by change k.val < 140; omega)
    simpa [T,B,e,embStk,periodicCouplingPageBank,periodicCouplingWidthBank,extendStacks,
      Fin.castLE,show k.val < 242 by omega] using hh
  have hblank (k : Fin 144) (hk : k.val < 117) (h93 : k ≠ 93) (h110 : k ≠ 110) : T.R k = [] := by
    let i : Fin 117 := ⟨k.val,hk⟩
    have hh := h.native i (by intro he; exact h93 (Fin.ext (congrArg (fun j : Fin 117 => j.val) he)))
      (by intro he; exact h110 (Fin.ext (congrArg (fun j : Fin 117 => j.val) he)))
    have hR : T.R k = S.R ⟨k.val,by omega⟩ := by
      have hn : k.val ≠ 130 ∧ k.val ≠ 135 ∧ k.val ≠ 138 ∧ k.val ≠ 139 ∧
          k.val ≠ 140 ∧ k.val ≠ 143 := by omega
      simp [T,B,e,embStk,periodicCouplingPageBank,periodicCouplingWidthBank,
        Fin.ext_iff,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2]
      rfl
    rw [hR]
    simpa [i,extendStacks,show k.val < 242 by omega] using hh
  obtain ⟨v₁,hu₁,he₁,hready⟩ := installCouplingHeaders_native_exec
    (body := fun f : Empty => nomatch f) precision q s t u band 0 s (S.R 110) (embDn e v) T
    hsrc hleft hblank rfl (by simp [T,B,e,embStk,periodicCouplingPageBank])
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun f => nomatch f) he₁ v rfl B rfl
  let G := embOvr e ({T with R := couplingHeadersR precision q s t u band 0 s T.R} : Stacks 144 A).get B
  have hreadyG : CouplingReady precision q (2*q+8) s t u band 0 s (S.R 110)
      (embStk groupReg (embStk e G)) := by
    rw [show embStk e G = {T with R := couplingHeadersR precision q s t u band 0 s T.R} from
      embStk_ovr hinj _ B]
    exact hready
  have hframe (k : Fin 242) (hk : k.val < 64 ∨ k = 119 ∨ 168 ≤ k.val) : G.R k = B.R k := by
    by_cases hlo : k.val < 144
    · let i : Fin 144 := ⟨k.val,hlo⟩
      have hei : e i = k := Fin.ext rfl
      have hnot : i ∉ [(114 : Fin 144),112,97,98,99,100,101,103,94] := by
        have hn : k.val < 64 ∨ k.val = 119 ∨ 168 ≤ k.val := by
          rcases hk with hk | hk | hk
          · exact Or.inl hk
          · exact Or.inr (Or.inl (congrArg Fin.val hk))
          · exact Or.inr (Or.inr hk)
        simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
        change ¬ (k.val = 114 ∨ k.val = 112 ∨ k.val = 97 ∨ k.val = 98 ∨
          k.val = 99 ∨ k.val = 100 ∨ k.val = 101 ∨ k.val = 103 ∨ k.val = 94)
        omega
      have hh := embOvr_get hinj
        ({T with R := couplingHeadersR precision q s t u band 0 s T.R} : Stacks 144 A).get B (.rt i)
      change G.R (e i) = (couplingHeadersR precision q s t u band 0 s T.R i).map id at hh
      rw [List.map_id,couplingHeadersR_off precision q s t u band 0 s T.R i hnot] at hh
      change G.R (e i) = B.R (e i) at hh
      simpa only [hei] using hh
    · exact (embOvr_off
        ({T with R := couplingHeadersR precision q s t u band 0 s T.R} : Stacks 144 A).get B
        (by intro i he
            have hv := congrArg (fun j : Fin 242 => j.val) he
            have hi := i.isLt
            change i.val = k.val at hv
            omega)).2
  have hbank := h.bank
  simp only [packedBoundaryRecoveryBase,embStk_extendStacks] at hbank
  have hbankB := periodicCouplingPageBank_bank (band := band) (xs := xs) (periodicCouplingWidth_bank hbank)
  have hbankG : PackedPreparedBank q (2*q+8) W N G := by
    apply hbankB.of_runtime_frame (F := G) (embOvr_right_left B _)
    · intro k hk; exact hframe k (Or.inl hk)
    · exact hframe 119 (Or.inr (Or.inl rfl))
    · intro k hk _; exact hframe k (Or.inr (Or.inr hk))
  have hpagesG : ∀ bo hf df, PackedBoundaryFactorPages bo hf df S → PackedBoundaryFactorPages bo hf df G := by
    intro bo hf df hpages
    have hpagesB := periodicCouplingPageBank_factorPages (band := band) (w := 2*q+8) (xs := xs)
      (periodicCouplingWidth_factorPages (q := q) hpages)
    exact hpagesB.of_solution_frame (fun k hk _ => hframe k (Or.inr (Or.inr hk)))
  obtain ⟨v₃,n,hu₃,hn,he₃,hr,hbank₃,hpages₃⟩ := periodicNativeCounters_exec (body := body)
    (by omega) (by omega) (S.R 110) v₂ G hreadyG hbankG
  refine ⟨v₃,installCouplingHeadersCost precision q s t u band 0 s+n,
    hu₃.trans (hu₂.trans hu₁),Nat.add_le_add_left hn _,Exec.seq he₂ he₃,hr,hbank₃,?_⟩
  intro bo hf df hpages
  exact hpages₃ bo hf df (hpagesG bo hf df hpages)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
