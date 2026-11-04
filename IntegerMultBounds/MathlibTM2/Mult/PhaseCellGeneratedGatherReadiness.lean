module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringGatherData

/-! Frame ordinary retained gather inputs while generated class headers are
written. The initialized setup supplies the class-specific halo fields. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open ScalarPlacement ScalarPlacement.ComputedClassBanks PackedTranspose
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K V s width radius L w : ℕ} {bank : ComputedClassBank → Fin T}
  {Fs : List (ZMod s → GaussianInt)} {borrowed : List (Fin (prime+K+4))}
  {S : Stacks ((T+175)+tapeCount) (prime+K)}
namespace RestoringGatherSeed
noncomputable section

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
  simp only [classCallerRegister,exposureIntoRouting,Fin.val_castAdd,Fin.val_natAdd] at hh
  have := output.isLt
  omega

/-- Transport the global inputs while class header ports are being written. -/
def reframe (g : RestoringGatherSeed (Q := Q) bank V s width radius L w Fs borrowed S)
    (F : Stacks ((T+175)+tapeCount) (prime+K)) (outputs : List (Fin T))
    (hR : ∀ k, (∀ output ∈ outputs, k ≠ classCallerRegister output) → F.R k = S.R k)
    (hL : F.L = S.L)
    (hExpose : ∀ j, j ≠ 3 → ∀ output ∈ outputs, g.exposeSrc j ≠ output)
    (hInput : ∀ output ∈ outputs, g.input ≠ output)
    (hRoute : ∀ j, j ≠ 3 → ∀ output ∈ outputs, g.routeSrc j ≠ output)
    (hOutput : ∀ output ∈ outputs, bank (.control .source) ≠ output) :
    RestoringGatherSeed (Q := Q) bank V s width radius L w Fs borrowed F := by
  have hc (k : Fin T) (hk : ∀ output ∈ outputs, k ≠ output) :
      F.R (classCallerRegister k) = S.R (classCallerRegister k) :=
    hR _ (fun output ho => classCallerRegister_injective.ne (hk output ho))
  exact {g with
    hs := (hc _ (hExpose 0 (by decide))).trans g.hs
    hw := (hc _ (hExpose 1 (by decide))).trans g.hw
    hr := (hc _ (hExpose 2 (by decide))).trans g.hr
    hV := (congrArg List.length (hc _ (hExpose 4 (by decide)))).trans g.hV
    hword := (congrArg List.length (hc _ (hExpose 5 (by decide)))).trans g.hword
    hcount := (congrArg List.length (hc _ (hExpose 6 (by decide)))).trans g.hcount
    hreplicas := (congrArg List.length (hc _ (hExpose 7 (by decide)))).trans g.hreplicas
    hsource := (hc _ hInput).trans g.hsource
    hblank := by
      intro i
      change F.R (exposureIntoRouting T (Fin.natAdd T i)) = []
      rw [hR _ (fun output _ => exposurePrivate_ne_caller i output)]
      exact g.hblank i
    houtput := (hc _ hOutput).trans g.houtput
    hRs := (hc _ (hRoute 0 (by decide))).trans g.hRs
    hRw := (hc _ (hRoute 1 (by decide))).trans g.hRw
    hRr := (hc _ (hRoute 2 (by decide))).trans g.hRr
    hRV := (congrArg List.length (hc _ (hRoute 4 (by decide)))).trans g.hRV
    hRword := (congrArg List.length (hc _ (hRoute 5 (by decide)))).trans g.hRword
    hRrep := (congrArg List.length (hc _ (hRoute 6 (by decide)))).trans g.hRrep
    hRblank := by
      intro i
      rw [hR _ (fun output _ => routingPrivate_ne_caller i output)]
      exact g.hRblank i
    hRleft := by intro i; rw [hL]; exact g.hRleft i
    hsourceLeft := by rw [hL]; exact g.hsourceLeft}


end
end RestoringGatherSeed
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
