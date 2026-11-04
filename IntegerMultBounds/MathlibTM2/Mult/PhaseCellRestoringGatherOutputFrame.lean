module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringGatherMetadataCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableUpdate

/-! Retained numerical readiness survives a change confined to the ambient output.
Programs and metadata bills depend only on the borrowed input ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
open ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose Fast.TableVM
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K V s width radius L w : ℕ} {bank : ComputedClassBank → Fin T}
  {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
  {S : Stacks ((T+175)+tapeCount) (prime+K)}
namespace RestoringGatherData
noncomputable section

private theorem updateR_frame {N A : ℕ} (S : Stacks N A) (output : Fin N)
    (xs : List (Fin (A+4))) :
    ∀ k, k ≠ output → ({S with R := Function.update S.R output xs} : Stacks N A).R k = S.R k := by
  intro k hk
  exact Function.update_of_ne hk xs S.R


private theorem exposurePrivate_ne_caller (i : Fin 175) (output : Fin T) :
    exposureIntoRouting T (Fin.natAdd T i) ≠ classCallerRegister output := by
  intro heq
  have hh := congrArg (fun j : Fin ((T+175)+tapeCount) => j.val) heq
  simp only [exposureIntoRouting,classCallerRegister,Fin.val_castAdd,Fin.val_natAdd] at hh
  have := output.isLt
  omega

private theorem routingPrivate_ne_caller (i : Fin tapeCount) (output : Fin T) :
    Fin.natAdd (T+175) i ≠ classCallerRegister output := by
  intro heq
  have hh := congrArg (fun j : Fin ((T+175)+tapeCount) => j.val) heq
  simp only [exposureIntoRouting,classCallerRegister,Fin.val_castAdd,Fin.val_natAdd] at hh
  have := output.isLt
  omega

def reframe (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S)
    (F : Stacks ((T+175)+tapeCount) (prime+K)) (output : Fin T)
    (hR : ∀ k, k ≠ classCallerRegister output → F.R k = S.R k) (hL : F.L = S.L)
    (hExpose : ∀ j, g.exposeSrc j ≠ output) (hInput : g.input ≠ output)
    (hRoute : ∀ j, g.routeSrc j ≠ output) (hBank : ∀ j, bank j ≠ output) :
    RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed F := by
  have hcaller (k : Fin T) (hk : k ≠ output) : F.R (classCallerRegister k) = S.R (classCallerRegister k) :=
    hR _ (classCallerRegister_injective.ne hk)
  have hexposed (k : Fin T) (hk : k ≠ output) :
      (embStk (exposureIntoRouting T) F).R (Fin.castAdd 175 k) =
        (embStk (exposureIntoRouting T) S).R (Fin.castAdd 175 k) := hcaller k hk
  exact {g with
    hs := (hexposed _ (hExpose 0)).trans g.hs
    hw := (hexposed _ (hExpose 1)).trans g.hw
    hr := (hexposed _ (hExpose 2)).trans g.hr
    hL := (hexposed _ (hExpose 3)).trans g.hL
    hV := (congrArg List.length (hexposed _ (hExpose 4))).trans g.hV
    hword := (congrArg List.length (hexposed _ (hExpose 5))).trans g.hword
    hcount := (congrArg List.length (hexposed _ (hExpose 6))).trans g.hcount
    hreplicas := (congrArg List.length (hexposed _ (hExpose 7))).trans g.hreplicas
    hsource := (hexposed _ hInput).trans g.hsource
    hblank := by
      intro i
      change F.R (exposureIntoRouting T (Fin.natAdd T i)) = []
      rw [hR _ (exposurePrivate_ne_caller i output)]
      exact g.hblank i
    houtput := (hexposed _ (hBank (.control .source))).trans g.houtput
    hRs := (hcaller _ (hRoute 0)).trans g.hRs
    hRw := (hcaller _ (hRoute 1)).trans g.hRw
    hRr := (hcaller _ (hRoute 2)).trans g.hRr
    hRL := (hcaller _ (hRoute 3)).trans g.hRL
    hRV := (congrArg List.length (hcaller _ (hRoute 4))).trans g.hRV
    hRword := (congrArg List.length (hcaller _ (hRoute 5))).trans g.hRword
    hRrep := (congrArg List.length (hcaller _ (hRoute 6))).trans g.hRrep
    hRblank := by intro i; rw [hR _ (routingPrivate_ne_caller i output)]; exact g.hRblank i
    hRleft := by intro i; rw [hL]; exact g.hRleft i
    hsourceLeft := by rw [hL]; exact g.hsourceLeft}

theorem reframe_program {P U : Type}
    (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S)
    (F : Stacks ((T+175)+tapeCount) (prime+K)) (output : Fin T)
    (hR : ∀ k, k ≠ classCallerRegister output → F.R k = S.R k) (hL : F.L = S.L)
    (hExpose : ∀ j, g.exposeSrc j ≠ output) (hInput : g.input ≠ output)
    (hRoute : ∀ j, g.routeSrc j ≠ output) (hBank : ∀ j, bank j ≠ output) :
    (g.reframe F output hR hL hExpose hInput hRoute hBank).program (P := P) (U := U) = g.program := rfl

theorem reframe_timeCost
    (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S)
    (F : Stacks ((T+175)+tapeCount) (prime+K)) (output : Fin T)
    (hR : ∀ k, k ≠ classCallerRegister output → F.R k = S.R k) (hL : F.L = S.L)
    (hExpose : ∀ j, g.exposeSrc j ≠ output) (hInput : g.input ≠ output)
    (hRoute : ∀ j, g.routeSrc j ≠ output) (hBank : ∀ j, bank j ≠ output) :
    (g.reframe F output hR hL hExpose hInput hRoute hBank).timeCost = g.timeCost := by
  simp only [timeCost,exposureMetadataVolume_eq,routingMetadataVolume_eq]
  rfl

theorem reframe_stockAllowance
    (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S)
    (F : Stacks ((T+175)+tapeCount) (prime+K)) (output : Fin T)
    (hR : ∀ k, k ≠ classCallerRegister output → F.R k = S.R k) (hL : F.L = S.L)
    (hExpose : ∀ j, g.exposeSrc j ≠ output) (hInput : g.input ≠ output)
    (hRoute : ∀ j, g.routeSrc j ≠ output) (hBank : ∀ j, bank j ≠ output) :
    (g.reframe F output hR hL hExpose hInput hRoute hBank).stockAllowance = g.stockAllowance := by
  simp only [stockAllowance,exposureMetadataVolume_eq,routingMetadataVolume_eq]
  rfl

def updateOutput (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S)
    (output : Fin T) (xs : List (Fin (prime+K+4)))
    (hExpose : ∀ j, g.exposeSrc j ≠ output) (hInput : g.input ≠ output)
    (hRoute : ∀ j, g.routeSrc j ≠ output) (hBank : ∀ j, bank j ≠ output) :
    RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed
      {S with R := Function.update S.R (classCallerRegister output) xs} :=
  g.reframe {S with R := Function.update S.R (classCallerRegister output) xs}
    output (by exact updateR_frame S (classCallerRegister output) xs) rfl hExpose hInput hRoute hBank

def updateTableOutput {n : ℕ} (rg : TblR n → Fin ((T+175)+tapeCount))
    (masters : Fin n → Fin ((T+175)+tapeCount)) (D : ℕ) (value : Fin ((T+175)+tapeCount) → ℕ)
    (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed (loadedInputTable rg masters D value S))
    (output : Fin T) (xs : List (Fin (prime+K+4)))
    (hTable : ∀ r, rg r ≠ classCallerRegister output)
    (hExpose : ∀ j, g.exposeSrc j ≠ output) (hInput : g.input ≠ output)
    (hRoute : ∀ j, g.routeSrc j ≠ output) (hBank : ∀ j, bank j ≠ output) :
    RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed
      (loadedInputTable rg masters D value {S with R := Function.update S.R (classCallerRegister output) xs}) :=
  g.reframe _ output (by
    intro k hk
    rw [loadedInputTable_update_off rg masters D value S _ xs hTable]
    exact updateR_frame (loadedInputTable rg masters D value S) (classCallerRegister output) xs k hk) rfl hExpose hInput hRoute hBank

theorem updateTableOutput_program {P U : Type} {n : ℕ} (rg : TblR n → Fin ((T+175)+tapeCount))
    (masters : Fin n → Fin ((T+175)+tapeCount)) (D : ℕ) (value : Fin ((T+175)+tapeCount) → ℕ)
    (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed (loadedInputTable rg masters D value S))
    (output : Fin T) (xs : List (Fin (prime+K+4)))
    (hTable : ∀ r, rg r ≠ classCallerRegister output)
    (hExpose : ∀ j, g.exposeSrc j ≠ output) (hInput : g.input ≠ output)
    (hRoute : ∀ j, g.routeSrc j ≠ output) (hBank : ∀ j, bank j ≠ output) :
    (g.updateTableOutput rg masters D value output xs hTable hExpose hInput hRoute hBank).program (P := P) (U := U) =
      g.program := rfl

/-- The transported readiness runs the same actual exposure/routing program,
with the original metadata bills and the new ambient frame. -/
theorem exec_reframe {P U : Type}
    (g : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed S)
    (F : Stacks ((T+175)+tapeCount) (prime+K)) (output : Fin T)
    (hR : ∀ k, k ≠ classCallerRegister output → F.R k = S.R k) (hL : F.L = S.L)
    (hExpose : ∀ j, g.exposeSrc j ≠ output) (hInput : g.input ≠ output)
    (hRoute : ∀ j, g.routeSrc j ≠ output) (hBank : ∀ j, bank j ≠ output)
    (hinj : Function.Injective bank) (initSrc : Fin 4 → Fin ((T+175)+tapeCount))
    (body : P → Pr P ((T+175)+tapeCount) Q (prime+K) U)
    (v : HS ((T+175)+tapeCount) Q (prime+K) U) (depth : ℕ) :
    let M := loadedClassGeometry (fullExposedClassBank bank) initSrc F
    ∃ v' n, v'.user = v.user ∧ n ≤ g.timeCost ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v M)+depth+g.stockAllowance)
        depth g.program (Host.mk v M) n
        (Host.mk v' {M with R := (Function.update M.R (control (fullExposedClassBank bank) .source)
          (coreSupplierStream (prime+K) width radius L w Fs.reverse))}) := by
  have hp := reframe_program (P := P) (U := U) g F output hR hL hExpose hInput hRoute hBank
  have ht := reframe_timeCost g F output hR hL hExpose hInput hRoute hBank
  have hs := reframe_stockAllowance g F output hR hL hExpose hInput hRoute hBank
  simpa only [hp,ht,hs] using (g.reframe F output hR hL hExpose hInput hRoute hBank).exec hinj initSrc body v depth

end
end RestoringGatherData
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
