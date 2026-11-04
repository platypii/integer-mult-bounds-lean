module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringGatherData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderFormats

/-! Retained gather inputs do not include initialized class halo words. Complete
them from the actual three-format export of the computed halo scalar. -/
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

/-- This runs the exporter; the two class-specific readiness fields come from
its actual endpoint, rather than from retained input hypotheses. -/
theorem exportHalo_exec_within {P U : Type}
    (body : P → Pr P ((T+175)+tapeCount) Q (prime+K) U)
    (g : RestoringGatherSeed (Q := Q) bank V s width radius L w Fs borrowed S)
    (src saved tmp : Fin ((T+175)+tapeCount))
    (count : Fin 3 → Fin ((T+175)+tapeCount)) (dst : Fin 3 → Fin T)
    (hregs : ∀ j, [count j,src,classCallerRegister (dst j),saved,tmp].Nodup)
    (hsep : ∀ i j, classCallerRegister (dst i) ≠ count j) (hdst : Function.Injective dst)
    (sourceWidth : ℕ) (bits : Fin ((T+175)+tapeCount) → ℕ)
    (hfit : ∀ j, bits (count j) ≤ sourceWidth)
    (hV : bits (count 1) = V) (hD : bits (count 2) = g.D)
    (hExposeHalo : g.exposeSrc 3 = dst 1) (hRouteHalo : g.routeSrc 3 = dst 2)
    (hExpose : ∀ j, j ≠ 3 → ∀ i, g.exposeSrc j ≠ dst i)
    (hInput : ∀ i, g.input ≠ dst i)
    (hRoute : ∀ j, j ≠ 3 → ∀ i, g.routeSrc j ≠ dst i)
    (hOutput : ∀ i, bank (.control .source) ≠ dst i)
    (v : HS ((T+175)+tapeCount) Q (prime+K) U)
    (hsrc : S.R src = binSyms sourceWidth L)
    (hcount : ∀ j, (S.R (count j)).length = bits (count j))
    (hblank : ∀ j, S.R (classCallerRegister (dst j)) = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    let F := {S with R := (copyWordHeadersR (fun k => binSyms (bits k) L)
      (classHaloFormats count (classCallerRegister ∘ dst)) S.R)}
    let cost := 10*(bits (count 0)+bits (count 1)+bits (count 2))+31
    ∃ v', ∃ ready : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed F,
      v'.user = v.user ∧ ready.exposeSrc = g.exposeSrc ∧ ready.routeSrc = g.routeSrc ∧
      ready.input = g.input ∧ ready.D = g.D ∧ ready.a = g.a ∧
      F.R (classCallerRegister (dst 0)) = binSyms (bits (count 0)) L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+3*cost) depth
        (copyBinaryFormats src saved tmp (classHaloFormats count (classCallerRegister ∘ dst)))
        (Host.mk v S) cost (Host.mk v' F) := by
  dsimp only
  obtain ⟨v',hu,hheaders,hframe,he⟩ := classHaloFormats_exec_within body src saved tmp count
    (classCallerRegister ∘ dst) hregs hsep (classCallerRegister_injective.comp hdst)
    sourceWidth L bits hfit v S hsrc hcount hblank hsaved htmp depth
  let F : Stacks ((T+175)+tapeCount) (prime+K) := {S with R := (copyWordHeadersR
    (fun k => binSyms (bits k) L) (classHaloFormats count (classCallerRegister ∘ dst)) S.R)}
  let seed := g.reframe F (List.ofFn dst)
    (by intro k hk; exact hframe k (fun j => (hk (dst j) (List.mem_ofFn.mpr ⟨j,rfl⟩)).symm)) rfl
    (by intro j hj output ho; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ho; exact hExpose j hj i)
    (by intro output ho; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ho; exact hInput i)
    (by intro j hj output ho; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ho; exact hRoute j hj i)
    (by intro output ho; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ho; exact hOutput i)
  let ready : RestoringGatherData (Q := Q) bank V s width radius L w Fs borrowed F :=
    {toRestoringGatherSeed := seed
     hL := by change F.R (classCallerRegister (g.exposeSrc 3)) = binSyms V L
              rw [hExposeHalo]; simpa only [F,Function.comp_apply,hV] using hheaders 1
     hRL := by change F.R (classCallerRegister (g.routeSrc 3)) = binSyms g.D L
               rw [hRouteHalo]; simpa only [F,Function.comp_apply,hD] using hheaders 2}
  exact ⟨v',ready,hu,rfl,rfl,rfl,rfl,rfl,hheaders 0,he⟩

end
end RestoringGatherSeed
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
