module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSeedLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadSupplierEndpoints

/-! The origin reader installs the two changing ordinary scalar inputs. All
other generator inputs are retained across origins. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicSeedLayout
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {T A : ℕ}

/-- Registers whose contents the scalar generator retains between origins. -/
def retained (g : CyclicSeedLayout T) (k : Fin T) : Prop :=
  k ∈ [g.precision,g.packet,g.replicas,g.word,g.saved,g.tmp,g.queue,g.zero] ∨
    (∃ r, g.rg r = k) ∨ (∃ i, g.masters i = k) ∨
    (∃ i : Fin 6, g.source i.castSucc.castSucc = k)

/-- Only the two endpoints vary; readiness of every other input transports
through the reader's exact frame. -/
theorem Ready.with_endpoints (g : CyclicSeedLayout T)
    {B p u l target s t a n W N : ℕ} {S F : Stacks T A}
    (ready : g.Ready B p u l target s t 0 0 W N S)
    (hframe : ∀ k, g.retained k → F.R k = S.R k)
    (ha : (F.R (g.source 6)).length = a)
    (hb : (F.R (g.source 7)).length = a+n) :
    g.Ready B p u l target s t a n W N F := by
  have hm (k) (hk : k ∈ [g.precision,g.packet,g.replicas,g.word,g.saved,g.tmp,g.queue,g.zero]) :=
    hframe k (Or.inl hk)
  have hr (r) := hframe (g.rg r) (Or.inr (Or.inl ⟨r,rfl⟩))
  have hs (i) := hframe (g.masters i) (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩)))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hm _ (by simp)]; exact ready.precision
  · rw [hm _ (by simp)]; exact ready.packet
  · rw [hm _ (by simp)]; exact ready.replicas
  · intro i
    have hf (j : Fin 6) := hframe (g.source j.castSucc.castSucc)
      (Or.inr (Or.inr (Or.inr ⟨j,rfl⟩)))
    fin_cases i
    · simpa using (congrArg List.length (hf (0 : Fin 6))).trans (ready.values 0)
    · simpa using (congrArg List.length (hf (1 : Fin 6))).trans (ready.values 1)
    · simpa using (congrArg List.length (hf (2 : Fin 6))).trans (ready.values 2)
    · simpa using (congrArg List.length (hf (3 : Fin 6))).trans (ready.values 3)
    · simpa using (congrArg List.length (hf (4 : Fin 6))).trans (ready.values 4)
    · simpa using (congrArg List.length (hf (5 : Fin 6))).trans (ready.values 5)
    · exact ha
    · exact hb
  · rw [hr]; exact ready.width
  · intro k hk; rw [hr]; exact ready.workspace k hk
  · intro i; rw [hs]; exact ready.masters i
  · intro i hi
    rw [hm i (by simp only [List.mem_cons] at hi ⊢; tauto)]
    exact ready.scratch i hi
  · rw [hm _ (by simp)]; exact ready.zero

/-- Read an origin into the ordinary dimension bank, producing the exact
readiness premise consumed by the generated numerical callback. -/
theorem read_endpoints_exec {Q : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    (g : CyclicSeedLayout T) (width halo origins binary work saved tmp : Fin T)
    (hreg : [width,halo,origins,binary,g.source 6,g.source 7,work,saved,tmp].Nodup)
    (hoff : ∀ k, g.retained k → origins ≠ k ∧ g.source 6 ≠ k ∧ g.source 7 ≠ k)
    {B p u l target s t a n W N V : ℕ} (hfit : a < 2^V)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (ready : g.Ready B p u l target s t 0 0 W N S)
    (hwidth : (S.R width).length = V) (hhalo : (S.R halo).length = n)
    (horigins : S.R origins = binSyms V a++tail)
    (hblank : ∀ k ∈ [binary,g.source 6,g.source 7,work,saved,tmp], S.R k = []) :
    let E : Stacks T A := {S with R := (Function.update
      (Function.update (Function.update S.R origins tail)
        (g.source 6) (List.replicate a tick)) (g.source 7) (List.replicate (a+n) tick))}
    ∃ v' steps, v'.user = v.user ∧ steps ≤ readSupplierEndpointsCost V a n ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        3*readSupplierEndpointsCost V a n) 0
        (readSupplierEndpoints width halo origins binary (g.source 6) (g.source 7) work saved tmp)
        (Host.mk v S) steps (Host.mk v' E) ∧
      g.Ready B p u l target s t a n W N E := by
  dsimp only
  obtain ⟨v',steps,hu,ht,he⟩ := readSupplierEndpoints_exec_within
    (body := body) width halo origins binary (g.source 6) (g.source 7) work saved tmp
    hreg V a n hfit tail v S hwidth hhalo horigins hblank 0
  refine ⟨v',steps,hu,ht,he,Ready.with_endpoints g ready ?_ ?_ ?_⟩
  · intro k hk
    obtain ⟨ho,ha,hb⟩ := hoff k hk
    simp [Ne.symm ho,Ne.symm ha,Ne.symm hb]
  · have hr := hreg
    regs_ne hr
    simp [‹g.source 6 ≠ g.source 7›]
  · simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicSeedLayout
