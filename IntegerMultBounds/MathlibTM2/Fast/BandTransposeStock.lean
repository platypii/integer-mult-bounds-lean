module

public import IntegerMultBounds.MathlibTM2.Fast.BandFactor
public import IntegerMultBounds.MathlibTM2.Fast.ResampBScanStock
public import IntegerMultBounds.MathlibTM2.Fast.ResampBFrameStock

/-! Transposition consumes pivot rows to pay for its column archive, sharing
one native window reserve across the whole axis. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {Proc U : Type} {body : Proc → Pr Proc T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem bandTBlkP_native :
    mnNativePushBound 2 (bandTBlkP (P := Proc) (Q := Q) (A := A) (U := U) rg) := by
  refine ⟨rsbMv_native .., rsbMv_native .., ?_⟩
  simp [copyR, copyStep, moveR, moveStep, whileR, peekR, mnNativePushBound, mnActPush]

theorem bandTStepP_native :
    mnNativePushBound 2 (bandTStepP (P := Proc) (Q := Q) (A := A) (U := U) rg) := by
  have hempty (a : Fin T) : mnNativePushBound 2 (emptyR (P := Proc) (Q := Q) (A := A) (U := U) a) := by
    simp [emptyR, emptyStep, whileR, peekR, mnNativePushBound, mnActPush]
  have hmove (a b : Fin T) : mnNativePushBound 2 (moveR (P := Proc) (Q := Q) (A := A) (U := U) a b id) := by
    simp [moveR, moveStep, whileR, peekR, mnNativePushBound, mnActPush]
  exact ⟨rsbMv_native .., hempty _, rsbMv_native .., rsbMv_native .., hempty _,
    rsbRep_native _ _ bandTBlkP_native, rsbMv_native .., rsbMv_native .., hempty _,
    hmove _ _, hmove _ _, hmove _ _⟩

theorem band_tLoop_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w k s : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (Ur : List (List ℤ)) (hUr : Ur.length = s)
    (hrow : ∀ row ∈ Ur, row.length = 2 * (k + 1) + 1) (SRC EF : List (Fin (A + 4)))
    (hsrc : σ .src = cstream A w (Ur.map colC).flatten ++ SRC)
    (hvk : σ .vk = cstream A w ((Mult.BandFactor.tWin (k + 1) Ur 0).map colC).flatten)
    (hef : σ .ef = EF) (hmsk : σ .msk = csyms A w 0) (hpr : σ .pr = []) (hxs : σ .xs = [])
    (hya : σ .ya = []) (hnv : σ .nv = []) (htC : σ .tC = []) (htL : σ .tL = [])
    (hsel : σ .sel = []) (hsn : (σ .sn).length = s)
    (hwn : (σ (.cm .wn)).length = w) (hmwn : (σ .mwn).length = (k + 1) * w)
    (hm2wn : (σ .m2wn).length = k * w) (hms : (σ .ms).length = k) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandTLoopP rg) σ
      (Function.update (Function.update (Function.update σ .src SRC) .vk
        (cstream A w ((Mult.BandFactor.tWin (k + 1) Ur s).map colC).flatten))
        .ef (cstream A w ((List.range s).reverse.map fun m =>
          colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten ++ EF))
      (s * (bandTStepCost w k + 6) + 4) (2*bandTStepCost w k) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun m =>
      Function.update (Function.update (Function.update σ .src
        (cstream A w ((Ur.drop m).map colC).flatten ++ SRC)) .vk
        (cstream A w ((Mult.BandFactor.tWin (k + 1) Ur m).map colC).flatten))
        .ef (cstream A w ((List.range m).reverse.map fun m =>
          colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten ++ EF) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .sn).length, ∀ X Y, RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandTStepP rg)
      (rsbUpd2 (Ψ j) .sn X .sel Y) (rsbUpd2 (Ψ (j + 1)) .sn X .sel Y) (bandTStepCost w k) (2*bandTStepCost w k) := by
    intro j hj X Y
    rw [hsn] at hj
    have hjU : j < Ur.length := by omega
    set row := Ur[j]'hjU with hrowdef
    have hrl : row.length = 2 * (k + 1) + 1 := hrow row (List.getElem_mem _)
    have hWl : ∀ blk ∈ Mult.BandFactor.tWin (k + 1) Ur j, blk.length = k + 1 := by
      intro blk hb
      simp only [Mult.BandFactor.tWin, List.mem_map] at hb
      obtain ⟨d, -, rfl⟩ := hb
      simp
    have h := band_tStep_runs (body := body) (ι := ι) (w := w) (k := k) hrg hdisj
      (rsbUpd2 (Ψ j) .sn X .sel Y) row hrl (Mult.BandFactor.tWin (k + 1) Ur j)
      (by simp [Mult.BandFactor.tWin]) hWl (cstream A w ((Ur.drop (j+1)).map colC).flatten ++ SRC)
      (cstream A w ((List.range j).reverse.map fun m =>
          colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten ++ EF)
      (by
        have hdj : (Ur.map colC).drop j=colC row :: (Ur.map colC).drop (j+1) := by
          rw [List.drop_eq_getElem_cons (by simpa using hjU), List.getElem_map]
        simp [rsbUpd2, hΨ, hdj])
      (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ, hmsk])
      (by simp [rsbUpd2, hΨ, hpr]) (by simp [rsbUpd2, hΨ, hxs]) (by simp [rsbUpd2, hΨ, hya])
      (by simp [rsbUpd2, hΨ, hnv]) (by simp [rsbUpd2, hΨ, htC]) (by simp [rsbUpd2, hΨ, htL])
      (by simp [rsbUpd2, hΨ, hwn]) (by simp [rsbUpd2, hΨ, hmwn]) (by simp [rsbUpd2, hΨ, hm2wn])
      (by simp [rsbUpd2, hΨ, hms])
    refine (h.within_native bandTStepP_native).congr ?_
    have hgd : Ur.getD j [] = row := by rw [List.getD_eq_getElem _ _ hjU]
    have hstep := Mult.BandFactor.tWin_step (k + 1) Ur (by omega) j (by rw [hgd, hrl]; omega)
    rw [hgd] at hstep
    have hcol : (Mult.BandFactor.tStep (Mult.BandFactor.tWin (k + 1) Ur j)
        ((row.drop 1).take (k + 1))).1 = Mult.BandFactor.ucolZ (k + 1) Ur j := by
      simp only [Mult.BandFactor.tStep, Mult.BandFactor.tWin_heads]
    rw [hstep, hcol]
    funext x; cases x <;> simp [rsbUpd2, hΨ, List.range_succ]
  have hwindow (m : ℕ) :
      (cstream A w ((Mult.BandFactor.tWin (k+1) Ur m).map colC).flatten).length =
        (k+1)*(k+1)*w := by
    rw [length_cstream, List.length_flatten, List.map_map,
      List.map_congr_left (g := fun _ => k+1) (fun blk hb => by
        simp only [Mult.BandFactor.tWin, List.mem_map] at hb
        obtain ⟨d,hd,rfl⟩ := hb
        simp [colC]), List.map_const', List.sum_replicate, smul_eq_mul]
    simp [Mult.BandFactor.tWin]
  have hcolumns (m : ℕ) :
      (cstream A w ((List.range m).reverse.map fun i =>
        colC (Mult.BandFactor.ucolZ (k+1) Ur i)).flatten).length = m*(k+1)*w := by
    rw [length_cstream, List.length_flatten, List.map_map,
      List.map_congr_left (g := fun _ => k+1) (fun i hi => by
        simp [colC, Mult.BandFactor.ucolZ]), List.map_const', List.sum_replicate, smul_eq_mul]
    simp
  have hinput (m : ℕ) :
      (cstream A w ((Ur.drop m).map colC).flatten).length = (s-m)*(2*(k+1)+1)*w := by
    rw [length_cstream, List.length_flatten, List.map_map,
      List.map_congr_left (g := fun _ => 2*(k+1)+1) (fun row hr => by
        simp [colC, hrow row (List.mem_of_mem_drop hr)]),
      List.map_const', List.sum_replicate, smul_eq_mul]
    simp [hUr]
  let roles : Fin 3 → RsbR := ![.src,.vk,.ef]
  have hroles : Function.Injective roles := by decide
  have hstock : ∀ j < (σ .sn).length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) .sn X .sel Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) .sn X .sel Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S) := by
    intro j hj X Y v v' S F hS hF hf
    have hjs : j < s := by simpa only [hsn] using hj
    apply RsbHolds.size_le_of_bank hrg roles hroles hS hF hf _ _ v v'
    · intro x hx
      have h0 : x ≠ .src := (hx 0).symm
      have h1 : x ≠ .vk := (hx 1).symm
      have h2 : x ≠ .ef := (hx 2).symm
      simp [rsbUpd2, hΨ, Function.update_apply, h0,h1,h2]
    · simp only [roles, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, rsbUpd2, hΨ, Function.update_apply, reduceCtorEq,
        ↓reduceIte, List.length_append, Nat.add_zero]
      rw [hwindow j, hwindow (j+1), hcolumns j, hcolumns (j+1), hinput j, hinput (j+1)]
      rw [show s-j = s-(j+1)+1 by omega]
      nlinarith only [Nat.zero_le (k*w)]
  have h := rsb_rep_runs_within hrg hdisj (ra := .sn) (rt := .sel) (by decide) (bandTStepP rg)
    (σ .sn) Ψ _ (2*bandTStepCost w k) hbody hstock
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_ (le_refl _)
  · funext x; cases x <;> simp [rsbUpd2, hΨ, hsrc, hvk, hef, hsel]
  · rw [hsn]
    have hd : (Ur.map colC).drop s=[] := List.drop_of_length_le (by simp; omega)
    funext x; cases x <;> simp [rsbUpd2, hΨ, hsel, hd]
  · rw [hsn]

/-- Moving an archive preserves stock, independently of its length. -/
theorem RsbRuns.within_moveR {ρ σ : RsbR → List (Fin (A+4))} {time : ℕ}
    {a b : Fin T}
    (h : RsbRuns body rg ι (moveR a b id) ρ σ time) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (moveR a b id) ρ σ time 0 := by
  intro v S hc hS
  obtain ⟨v',F,n,hu,hn,he,hh,hf⟩ := h v S hc hS
  exact ⟨v',F,n,hu,hn,hh,hf,fun depth =>
    moveR_within _ _ _ he depth (mnSize (mk v S)+depth+0) (by omega)⟩

theorem band_axisTr_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j) {w k s : ℕ}
    (σ : RsbR → List (Fin (A + 4))) (Ur : List (List ℤ)) (hUr : Ur.length = s)
    (hrow : ∀ row ∈ Ur, row.length = 2 * (k + 1) + 1) (SRC : List (Fin (A + 4)))
    (hsrc : σ .src = cstream A w (Ur.map colC).flatten ++ SRC)
    (hvk : σ .vk = cstream A w ((Mult.BandFactor.tWin (k + 1) Ur 0).map colC).flatten)
    (hef : σ .ef = []) (hhf : σ .hf = []) (hmsk : σ .msk = csyms A w 0) (hpr : σ .pr = [])
    (hxs : σ .xs = []) (hya : σ .ya = []) (hnv : σ .nv = []) (htC : σ .tC = []) (htL : σ .tL = [])
    (hsel : σ .sel = []) (hac2 : σ .ac2 = []) (hsn : (σ .sn).length = s)
    (hwn : (σ (.cm .wn)).length = w) (hmwn : (σ .mwn).length = (k + 1) * w)
    (hm2wn : (σ .m2wn).length = k * w) (hms : (σ .ms).length = k) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandAxisTrP rg) σ
      (Function.update (Function.update (Function.update σ .src SRC) .vk []) .hf
        (cstream A w ((List.range s).reverse.map fun m =>
          colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten))
      (s * (bandTStepCost w k + 6) + 4 + (2 * ((k + 1) * (k + 1) * w) + 2) +
        (2 * (s * (k + 1) * w) + 2) + (2 * (s * (k + 1) * w) + 2)) (2*bandTStepCost w k) := by
  have h₁ := band_tLoop_runs_within (body := body) (ι := ι) hrg hdisj σ Ur hUr hrow SRC [] hsrc hvk hef hmsk
    hpr hxs hya hnv htC htL hsel hsn hwn hmwn hm2wn hms
  set σ₁ := Function.update (Function.update (Function.update σ .src SRC) .vk
    (cstream A w ((Mult.BandFactor.tWin (k + 1) Ur s).map colC).flatten))
    .ef (cstream A w ((List.range s).reverse.map fun m =>
      colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten ++ [])
  have h₂ := rsb_emptyR_runs (body := body) (ι := ι) hrg .vk σ₁
  have h₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ef) (b := .ac2) (by decide)
    (Function.update σ₁ .vk [])
  have h₄ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ac2) (b := .hf) (by decide)
    (Function.update (Function.update (Function.update σ₁ .vk []) .ef [])
      .ac2 (((Function.update σ₁ .vk []) .ef).reverse ++ (Function.update σ₁ .vk []) .ac2))
  have hwin : ∀ m, (cstream A w ((Mult.BandFactor.tWin (k + 1) Ur m).map colC).flatten).length =
      (k + 1) * (k + 1) * w := by
    intro m
    rw [length_cstream, List.length_flatten, List.map_map,
      List.map_congr_left (g := fun _ => k + 1) (fun r hr => by
        simp only [Mult.BandFactor.tWin, List.mem_map] at hr
        obtain ⟨d, -, rfl⟩ := hr
        simp [colC]),
      List.map_const', List.sum_replicate, smul_eq_mul]
    simp [Mult.BandFactor.tWin]
  have hcols : (cstream A w ((List.range s).reverse.map fun m =>
      colC (Mult.BandFactor.ucolZ (k + 1) Ur m)).flatten).length = s * (k + 1) * w := by
    rw [length_cstream, List.length_flatten, List.map_map,
      List.map_congr_left (g := fun _ => k + 1) (fun m _ => by simp [colC, Mult.BandFactor.ucolZ]),
      List.map_const', List.sum_replicate, smul_eq_mul]
    simp
  have h₂w := h₂.within_native (c := 0) (by
    simp [emptyR,emptyStep,whileR,peekR,mnNativePushBound,mnActPush])
  have h₃w := h₃.within_moveR
  have h₄w := h₄.within_moveR
  refine ((RsbRunsWithin.seq hdisj h₁ (RsbRunsWithin.seq hdisj h₂w (RsbRunsWithin.seq hdisj h₃w h₄w))).congr ?_).mono ?_ (by omega)
  · funext x; cases x <;> simp [σ₁, hef, hhf, hac2]
  · simp only [σ₁, Function.update_self, Function.update_of_ne (by decide : RsbR.ef ≠ RsbR.vk),
      Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.ef),
      Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.vk), Function.update_of_ne (by decide : RsbR.ac2 ≠ RsbR.src),
      List.append_nil, hcols, List.length_reverse, hac2]
    rw [Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.ef), Function.update_self, hwin]
    omega

end IntegerMultBounds.MathlibTM2.Fast
