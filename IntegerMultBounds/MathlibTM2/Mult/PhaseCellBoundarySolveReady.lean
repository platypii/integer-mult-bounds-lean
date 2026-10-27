module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorPrepared
public import IntegerMultBounds.MathlibTM2.Fast.BandLineDriver

/-! The factorizer restores exactly the workspace needed by the triangular passes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer

/-- Scratch used by the two triangular passes; factor tables are retained separately. -/
def boundarySolveScratch : List RsbR :=
  [.ef,.tb,.dout,.hv,.ya,.xs,.pr,.nv,.ac,.ac2,.tC,.tA,.tJ,.b1,.tL,.xa,.hc]

structure BoundarySolveReady {A : ℕ} (σ : RsbR → List (Fin (A+4))) (q w W N : ℕ) : Prop where
  ready : RsbReady σ w q
  sn : (σ .sn).length = N
  m2n : (σ .m2n).length = W
  mwn : (σ .mwn).length = W*w
  empty : ∀ r ∈ boundarySolveScratch, σ r = []

theorem boundarySolveScratch_cases (r : RsbR) (hr : r ∈ boundarySolveScratch) :
    r = .ef ∨ r = .dout ∨ r = .xs ∨
      (r ∈ boundaryFactorScratch ∧
        r ∉ ([.src,.hf,.df,.dout,.bo,.vk,.m2n,.kn,.ms,.mwn,.ef,.xs] : List RsbR)) := by
  cases r <;> simp_all [boundarySolveScratch,boundaryFactorScratch]

theorem BoundarySolveReady.update_vk {A q w W N : ℕ} {σ : RsbR → List (Fin (A+4))}
    (h : BoundarySolveReady σ q w W N) (xs : List (Fin (A+4))) :
    BoundarySolveReady (Function.update σ .vk xs) q w W N := by
  refine ⟨h.ready.update .vk (fun _ => by simp) xs,?_,?_,?_,?_⟩
  · simpa using h.sn
  · simpa using h.m2n
  · simpa using h.mwn
  · intro r hr
    by_cases hrk : r = .vk
    · subst r
      simp [boundarySolveScratch] at hr
    · rw [Function.update_of_ne hrk]
      exact h.empty r hr

/-- The factorizer's exceptional ports are either tables, headers, or explicitly emptied.
Every other solve scratch tape is restored by its frame theorem. -/
theorem boundarySolveReady_of_factor {A p q band N : ℕ}
    {σ τ : RsbR → List (Fin (A+4))} (h : BoundaryFactorPrepared σ p q band N)
    (w : ℕ) (hready : RsbReady τ w q)
    (hsn : (τ .sn).length = N) (hm2n : (τ .m2n).length = 12*band+1)
    (hmwn : (τ .mwn).length = (12*band+1)*w)
    (hef : τ .ef = []) (hdout : τ .dout = []) (hxs : τ .xs = [])
    (hframe : ∀ r, r ∉ ([.src,.hf,.df,.dout,.bo,.vk,.m2n,.kn,.ms,.mwn,.ef,.xs] : List RsbR) →
      τ r = σ r) : BoundarySolveReady τ q w (12*band+1) N := by
  refine ⟨hready,hsn,hm2n,hmwn,?_⟩
  intro r hr
  have hcases := boundarySolveScratch_cases r hr
  rcases hcases with rfl | rfl | rfl | ⟨hin,hout⟩
  · exact hef
  · exact hdout
  · exact hxs
  · rw [hframe r hout]
    exact h.empty r hin

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

/-- Append the triangular look-ahead zeros without reversing the gathered RHS. -/
def boundaryPadRhs (rg : RsbR → Fin T) : Pr P T Q A U :=
  .seq (moveR (rg .vk) (rg .ya) id)
    (.seq (umulSym 1 (pairSym A false false) (rg .mwn) (rg .vk) (rg .tC))
      (moveR (rg .ya) (rg .vk) id))

theorem boundary_padRhs_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    {q w W N : ℕ} (σ : RsbR → List (Fin (A+4))) (h : BoundarySolveReady σ q w W N)
    (b : List GaussianInt) (hb : b.length = N) (hvk : σ .vk = cstream A w b) :
    RsbRuns body rg ι (boundaryPadRhs rg) σ
      (Function.update σ .vk (cstream A w (b ++ List.replicate W 0)))
      (4*N*w+4*W*w+8) := by
  have hya := h.empty .ya (by simp [boundarySolveScratch])
  have htC := h.empty .tC (by simp [boundarySolveScratch])
  have h₁ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .vk) (b := .ya) (by decide) σ
  let σ₁ := Function.update (Function.update σ .vk []) .ya ((σ .vk).reverse ++ σ .ya)
  have h₂ := rsb_umulSym_runs (body := body) (ι := ι) hrg (pairSym A false false)
    (c := .mwn) (a := .vk) (t := .tC) (by decide) (by decide) (by decide) σ₁
    (by simp [σ₁,htC])
  let σ₂ := Function.update σ₁ .vk (List.replicate (σ₁ .mwn).length (pairSym A false false) ++ σ₁ .vk)
  have h₃ := rsb_moveR_runs (body := body) (ι := ι) hrg (a := .ya) (b := .vk) (by decide) σ₂
  refine ((RsbRuns.seq hdisj h₁ (RsbRuns.seq hdisj h₂ h₃)).congr ?_).mono ?_
  · have hz : List.replicate (W*w) (pairSym A false false) = cstream A w (List.replicate W 0) := by
      rw [cstream_replicate_zero]
    funext r
    cases r <;> simp [σ₂,σ₁,hya,hvk,h.mwn,hz,cstream_append]
  · simp [σ₂,σ₁,hya,hvk,length_cstream,hb,h.mwn,Nat.mul_assoc]
    omega

/-- Solve a boundary RHS already gathered in folded order, preserving all three factor tables.
Only the padded RHS and the output ports change. Numerical bounds are separate from workspace
readiness, so the same restored factor bank can serve successive RHS vectors. -/
theorem boundary_solve_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q w W N : ℕ} (σ : RsbR → List (Fin (A+4))) (h : BoundarySolveReady σ q w W N)
    (hw : 1 ≤ w) (hq : q ≤ w)
    (Lc Uc : List (List ℤ)) (rcs : List ℤ)
    (hLc : Lc.length = N) (hUc : Uc.length = N)
    (hLl : ∀ c ∈ Lc, c.length = W) (hUl : ∀ c ∈ Uc, c.length = W)
    (hrcs : rcs.length = N) (b : List GaussianInt) (hb : b.length = N)
    (hfL : ∀ c ∈ Lc, ∀ x ∈ c, Fits w (⟨x,0⟩ : GaussianInt))
    (hfU : ∀ c ∈ Uc, ∀ x ∈ c, Fits w (⟨x,0⟩ : GaussianInt))
    (hfr : ∀ x ∈ rcs, Fits w (⟨x,0⟩ : GaussianInt))
    (hfit₁ : ∀ j < N, Fits w ((Mult.BandList.bandPend q Lc
      (b ++ List.replicate W 0) j).headD 0))
    (hfit₂ : ∀ j < N, Fits w ((Mult.BandList.bandPendB q Uc rcs
      ((Mult.BandList.fwdZC q Lc (b ++ List.replicate W 0)).reverse ++
        List.replicate W 0) j).headD 0))
    (hfit₃ : ∀ j < N, Fits w (tdivN q ((Mult.BandList.bandPendB q Uc rcs
      ((Mult.BandList.fwdZC q Lc (b ++ List.replicate W 0)).reverse ++
        List.replicate W 0) j).headD 0 * ⟨rcs.getD j 0,0⟩)))
    (hvk : σ .vk = cstream A w (b ++ List.replicate W 0))
    (hbo : σ .bo = cstream A w (Lc.map colC).flatten)
    (hhf : σ .hf = cstream A w (Uc.map colC).flatten)
    (hdf : σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt))) :
    RsbRuns body rg ι (bandLinePassP rg hι hT hQ) σ
      (Function.update (Function.update σ .vk []) .dout
        (cstream A w (bandSolveVec q W Lc Uc rcs b))) (bandLinePassCost w N W) := by
  apply band_linePass_runs hrg hdisj hι hT hQ hA σ h.ready hw hq
    Lc Uc rcs hLc hUc hLl hUl hrcs b hb hfL hfU hfr hfit₁ hfit₂ hfit₃ hvk hbo hhf hdf
  all_goals first
    | exact h.sn
    | exact h.m2n
    | exact h.mwn
    | exact h.empty _ (by simp [boundarySolveScratch])

/-- Pad and solve one gathered boundary RHS using the retained factors. -/
theorem boundary_foldedSolve_runs (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q w W N : ℕ} (σ : RsbR → List (Fin (A+4))) (h : BoundarySolveReady σ q w W N)
    (hw : 1 ≤ w) (hq : q ≤ w)
    (Lc Uc : List (List ℤ)) (rcs : List ℤ)
    (hLc : Lc.length = N) (hUc : Uc.length = N)
    (hLl : ∀ c ∈ Lc, c.length = W) (hUl : ∀ c ∈ Uc, c.length = W)
    (hrcs : rcs.length = N) (b : List GaussianInt) (hb : b.length = N)
    (hfL : ∀ c ∈ Lc, ∀ x ∈ c, Fits w (⟨x,0⟩ : GaussianInt))
    (hfU : ∀ c ∈ Uc, ∀ x ∈ c, Fits w (⟨x,0⟩ : GaussianInt))
    (hfr : ∀ x ∈ rcs, Fits w (⟨x,0⟩ : GaussianInt))
    (hfit₁ : ∀ j < N, Fits w ((Mult.BandList.bandPend q Lc
      (b ++ List.replicate W 0) j).headD 0))
    (hfit₂ : ∀ j < N, Fits w ((Mult.BandList.bandPendB q Uc rcs
      ((Mult.BandList.fwdZC q Lc (b ++ List.replicate W 0)).reverse ++
        List.replicate W 0) j).headD 0))
    (hfit₃ : ∀ j < N, Fits w (tdivN q ((Mult.BandList.bandPendB q Uc rcs
      ((Mult.BandList.fwdZC q Lc (b ++ List.replicate W 0)).reverse ++
        List.replicate W 0) j).headD 0 * ⟨rcs.getD j 0,0⟩)))
    (hvk : σ .vk = cstream A w b)
    (hbo : σ .bo = cstream A w (Lc.map colC).flatten)
    (hhf : σ .hf = cstream A w (Uc.map colC).flatten)
    (hdf : σ .df = cstream A w (rcs.map fun x => (⟨x,0⟩ : GaussianInt))) :
    RsbRuns body rg ι (.seq (boundaryPadRhs rg) (bandLinePassP rg hι hT hQ)) σ
      (Function.update (Function.update σ .vk []) .dout
        (cstream A w (bandSolveVec q W Lc Uc rcs b))) (4*N*w+4*W*w+8+bandLinePassCost w N W) := by
  let σ₁ := Function.update σ .vk (cstream A w (b ++ List.replicate W 0))
  have hpad := boundary_padRhs_runs (body := body) hrg hdisj σ h b hb hvk
  have hsolve := boundary_solve_runs (body := body) hrg hdisj hι hT hQ hA σ₁
    (h.update_vk _) hw hq Lc Uc rcs hLc hUc hLl hUl hrcs b hb hfL hfU hfr
    hfit₁ hfit₂ hfit₃ (by simp [σ₁])
    (by simpa [σ₁] using hbo) (by simpa [σ₁] using hhf) (by simpa [σ₁] using hdf)
  refine (RsbRuns.seq hdisj hpad hsolve).congr ?_
  funext r
  cases r <;> simp [σ₁]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
