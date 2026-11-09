module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandFactorRowStock
public import IntegerMultBounds.MathlibTM2.Fast.ResampBFrameStock

/-! The non-pivot row scan shares one arithmetic reserve. Shrinking input
windows and pivot tables pay for growing multiplier and updated-row archives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {Proc U : Type} {body : Proc → Pr Proc T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem band_facRows_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (r : ℤ) (tail0 : List ℤ) (rest : List (List ℤ)) (htl : tail0.length = 2 * B)
    (hrest : rest.length = B) (hrow : ∀ row ∈ rest, row.length = 2 * B + 1)
    (hfr : Fits w (⟨r, 0⟩ : GaussianInt)) (hft : ∀ a ∈ tail0, Fits w (⟨a, 0⟩ : GaussianInt))
    (hfh : ∀ row ∈ rest, Fits w (⟨row.headD 0, 0⟩ : GaussianInt) ∧
      Fits w (⟨facMul P r row, 0⟩ : GaussianInt))
    (D TB SR : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (rest.map colC).flatten)
    (htb : σ .tb = cstream A w (List.replicate B ⟨r, 0⟩) ++ TB)
    (hef : σ .ef = cstream A w (List.replicate B (colC tail0)).flatten) (hsr : σ .sr = SR)
    (hmsk : σ .msk = csyms A w 0)
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (hxa : σ .xa = []) (hhc : σ .hc = []) (htL : σ .tL = []) (hms : (σ .ms).length = B)
    (hm2n : (σ .m2n).length = 2 * B) (hmwn : (σ .mwn).length = 2 * B * w)
    (K L : ℕ)
    (hpushK : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ K)
    (hpushL : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ L) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandFacRowsP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        []) .tb TB) .ef []) .dout
        (cstream A w ((rest.map fun row => (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D)) .sr
        ((cstream A w (rest.map fun row => colC (facRow P r tail0 row)).flatten).reverse ++ SR))
      (B * (bandFacRowCost w B + 6) + 4)
      (((realWeightWorkspace K w 1+1000*(w+1))+(realWeightWorkspace L w (2*B)+1000*(2*B+1)*(w+1)))+100*(B+1)*(w+1)) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w ((rest.drop j).map colC).flatten)) .tb
        (cstream A w (List.replicate (B-j) ⟨r, 0⟩) ++ TB)) .ef
        (cstream A w (List.replicate (B-j) (colC tail0)).flatten)) .dout
        (cstream A w (((rest.take j).map fun row => (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D))
        .sr ((cstream A w ((rest.take j).map fun row => colC (facRow P r tail0 row)).flatten).reverse ++
          SR) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .ms).length, ∀ X Y, RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandFacRowP rg hι hT hQ)
      (rsbUpd2 (Ψ j) .ms X .tL Y) (rsbUpd2 (Ψ (j + 1)) .ms X .tL Y) (bandFacRowCost w B) (((realWeightWorkspace K w 1+1000*(w+1))+(realWeightWorkspace L w (2*B)+1000*(2*B+1)*(w+1)))+100*(B+1)*(w+1)) := by
    intro j hj X Y
    rw [hms] at hj
    have hjr : j < rest.length := by omega
    set row := rest[j]'hjr with hrowdef
    have hrl := hrow row (List.getElem_mem hjr)
    obtain ⟨h, tl, hht⟩ : ∃ h tl, row = h :: tl := by
      cases hr : row with
      | nil => rw [hr] at hrl; simp at hrl
      | cons h tl => exact ⟨h, tl, rfl⟩
    have htll : tl.length = 2 * B := by rw [hht] at hrl; simp at hrl; omega
    have hfhj := hfh row (List.getElem_mem hjr)
    rw [hht] at hfhj
    have hready' : RsbReady (rsbUpd2 (Ψ j) .ms X .tL Y) w P := by
      simp only [rsbUpd2, hΨ]
      exact ((((((hready.update .vk (fun c => by simp) _).update .tb (fun c => by simp) _).update
        .ef (fun c => by simp) _).update .dout (fun c => by simp) _).update .sr (fun c => by simp)
        _).update .ms (fun c => by simp) _).update .tL (fun c => by simp) _
    have hBj : B-j=(B-(j+1))+1 := by omega
    have hstep := band_facRow_runs_within (body := body) (ι := ι) (w := w) (B := B) hrg hdisj hι hT hQ hA
      (rsbUpd2 (Ψ j) .ms X .tL Y) hready' hw hp ⟨h, 0⟩ r (colC tl)
      ((rest.drop (j+1)).map colC).flatten (colC tail0)
      (List.replicate (B-(j+1)) (colC tail0)).flatten (by simp [colC, htll])
      (by simp [colC, htl]) hfhj.1 hfr (by rw [tdivN_real]; simpa [facMul, hht] using hfhj.2)
      (by intro a ha; simp only [colC, List.mem_map] at ha; obtain ⟨x, hx, rfl⟩ := ha
          exact ⟨hft x hx, rfl⟩)
      (cstream A w (((rest.take j).map fun row => (⟨facMul P r row, 0⟩ : GaussianInt)).reverse) ++ D)
      (cstream A w (List.replicate (B-(j+1)) ⟨r, 0⟩) ++ TB)
      ((cstream A w ((rest.take j).map fun row => colC (facRow P r tail0 row)).flatten).reverse ++ SR)
      (by
        simp only [rsbUpd2, hΨ, Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.tL),
          Function.update_of_ne (by decide : RsbR.vk ≠ RsbR.ms)]
        rw [List.drop_eq_getElem_cons hjr, ← hrowdef, hht]
        simp [colC])
      (by simp [rsbUpd2, hΨ, hBj, List.replicate_succ])
      (by simp [rsbUpd2, hΨ, hBj, List.replicate_succ])
      (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ, hmsk]) (by simp [rsbUpd2, hΨ])
      (by simp [rsbUpd2, hΨ, hhv]) (by simp [rsbUpd2, hΨ, hya]) (by simp [rsbUpd2, hΨ, hxs])
      (by simp [rsbUpd2, hΨ, hpr]) (by simp [rsbUpd2, hΨ, hnv]) (by simp [rsbUpd2, hΨ, hac])
      (by simp [rsbUpd2, hΨ, hac2]) (by simp [rsbUpd2, hΨ, htC]) (by simp [rsbUpd2, hΨ, htA])
      (by simp [rsbUpd2, hΨ, htJ]) (by simp [rsbUpd2, hΨ, hb1]) (by simp [rsbUpd2, hΨ, hxa])
      (by simp [rsbUpd2, hΨ, hhc]) (by simp [rsbUpd2, hΨ, hm2n]) (by simp [rsbUpd2, hΨ, hmwn]) K L hpushK hpushL
    refine hstep.congr ?_
    have htake : ∀ {β : Type} (F : List ℤ → β), (rest.map F).take (j+1)=(rest.map F).take j++[F row] := by
      intro β F
      rw [List.take_succ_eq_append_getElem (by simpa using hjr), List.getElem_map]
    have hmr := machine_row P (facMul P r row) (2 * B) tail0 tl htl htll
    rw [tdivN_real]
    have hfm : facMul P r row=(h*r).tdiv (2^P) := by simp [facMul, hht]
    rw [← hfm, hmr]
    have h0 : (0 : GaussianInt)=⟨0, 0⟩ := rfl
    funext x; cases x <;> simp [rsbUpd2, hΨ, htake, facRow, hht, colC, List.reverse_append, h0]
  let roles : Fin 5 → RsbR := ![.vk,.tb,.ef,.dout,.sr]
  have hroles : Function.Injective roles := by decide
  have hrawLengths : rest.map List.length = List.replicate B (2*B+1) := by
    calc
      rest.map List.length = rest.map (fun _ => 2*B+1) := List.map_congr_left (fun row hr => hrow row hr)
      _ = _ := by simp [hrest]
  have hnewLengths : rest.map (fun row => (facRow P r tail0 row).length) = List.replicate B (2*B+1) := by
    calc
      rest.map (fun row => (facRow P r tail0 row).length) = rest.map (fun _ => 2*B+1) := by
        apply List.map_congr_left
        intro row hr
        simp [facRow,Mult.BandFactor.subRowZ,htl,hrow row hr]
      _ = _ := by simp [hrest]
  have hstock : ∀ j < (σ .ms).length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) .ms X .tL Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) .ms X .tL Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S) := by
    intro j hj X Y v v' S F hS hF hf
    apply RsbHolds.size_le_of_bank hrg roles hroles hS hF hf _ _ v v'
    · intro x hx
      have h0 : x ≠ .vk := (hx 0).symm
      have h1 : x ≠ .tb := (hx 1).symm
      have h2 : x ≠ .ef := (hx 2).symm
      have h3 : x ≠ .dout := (hx 3).symm
      have h4 : x ≠ .sr := (hx 4).symm
      simp [rsbUpd2,hΨ,Function.update_apply,h0,h1,h2,h3,h4]
    · have hjB : j < B := by simpa only [hms] using hj
      simp [roles,Fin.sum_univ_succ,rsbUpd2,hΨ,length_cstream,List.length_flatten,
        List.map_map,Function.comp_def,colC,List.map_drop,List.map_take,hrawLengths,hnewLengths,
        hrest,Nat.min_eq_left (by omega : j ≤ B),Nat.min_eq_left (by omega : j+1 ≤ B)]
      rw [show B-j = B-(j+1)+1 by omega]
      nlinarith only [Nat.zero_le (B*w)]
  have h := rsb_rep_runs_within hrg hdisj (ra := .ms) (rt := .tL) (by decide) (bandFacRowP rg hι hT hQ)
    (σ .ms) Ψ _ (((realWeightWorkspace K w 1+1000*(w+1))+(realWeightWorkspace L w (2*B)+1000*(2*B+1)*(w+1)))+100*(B+1)*(w+1)) hbody hstock
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_ (le_refl _)
  · funext x; cases x <;> simp [rsbUpd2, hΨ, hvk, htb, hef, hdout, hsr, htL]
  · rw [hms]
    have hd : (rest.map colC).drop B=[] := List.drop_of_length_le (by simp [hrest])
    funext x; cases x <;> simp [rsbUpd2, hΨ, htL, hrest, List.take_of_length_le, hd]
  · rw [hms]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
