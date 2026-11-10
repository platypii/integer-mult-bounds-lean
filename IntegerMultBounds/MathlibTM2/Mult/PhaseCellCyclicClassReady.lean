module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedOriginCyclicCaller

/-! The fitting class retains ordinary headers and empty workspace. Numerical
masters are generated and retired inside each callback, never an invariant. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {T A : ℕ}

def classProtected (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    (width binary work saved tmp r : Fin T) : Prop :=
  g.retained r ∨ r ∈ [g.source 6,g.source 7,width,binary,work,saved,tmp] ∨
    (∃ i, ports.bank i = r) ∨ r ∈ ports.fixedControls

structure ClassInputs (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    (width binary work saved tmp : Fin T) (B p u l target s t W V N n radius core : ℕ)
    (S : Stacks T A) : Prop where
  scalar : g.Ready B p u l target s t 0 0 W N S
  bank : ∀ i, S.L (ports.bank i) = [] ∧ S.R (ports.bank i) = []
  width : (S.R width).length = V
  reader : ∀ r ∈ [binary,g.source 6,g.source 7,work,saved,tmp], S.R r = []
  span : (S.R ports.span).length = n
  controls : ∀ i, (S.R (ports.controls i)).length = ![W,radius,core] i
  saved : S.R ports.saved = []
  tmp : S.R ports.tmp = []

structure ClassReady (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    (width binary work saved tmp : Fin T) (B p u l target s t W V N n radius core : ℕ)
    (S : Stacks T A) : Prop extends
    ClassInputs ports g width binary work saved tmp B p u l target s t W V N n radius core S where
  count : (S.R ports.count).length = N*n*W

/-- Ordinary read ports exclude the payload counter that setup generates. -/
def classInputProtected (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    (width binary work saved tmp r : Fin T) : Prop :=
  g.retained r ∨ r ∈ [g.source 6,g.source 7,width,binary,work,saved,tmp] ∨
    (∃ i, ports.bank i = r) ∨ r ∈ [ports.span,ports.saved,ports.tmp]++List.ofFn ports.controls

/-- A single frame transports every ordinary callback premise. -/
theorem ClassInputs.frame (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    {width binary work saved tmp : Fin T} {B p u l target s t W V N n radius core : ℕ}
    {S F : Stacks T A}
    (ready : ports.ClassInputs g width binary work saved tmp B p u l target s t W V N n radius core S)
    (hleft : F.L = S.L)
    (hframe : ∀ r, ports.classInputProtected g width binary work saved tmp r → F.R r = S.R r) :
    ports.ClassInputs g width binary work saved tmp B p u l target s t W V N n radius core F := by
  have hs (r) (hr : r ∈ [g.source 6,g.source 7,width,binary,work,saved,tmp]) := hframe r (Or.inr (Or.inl hr))
  have hc (r) (hr : r ∈ ([ports.span,ports.saved,ports.tmp]++List.ofFn ports.controls)) := hframe r (Or.inr (Or.inr (Or.inr hr)))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply CyclicSeedLayout.Ready.with_endpoints g ready.scalar
    · intro r hr; exact hframe r (Or.inl hr)
    · rw [hs _ (by simp)]; exact ready.scalar.values 6
    · rw [hs _ (by simp)]; exact ready.scalar.values 7
  · intro i
    rw [hleft,hframe _ (Or.inr (Or.inr (Or.inl ⟨i,rfl⟩)))]
    exact ready.bank i
  · rw [hs _ (by simp)]; exact ready.width
  · intro r hr
    rw [hs r (by simp only [List.mem_cons] at hr ⊢; tauto)]
    exact ready.reader r hr
  · rw [hc _ (by simp)]; exact ready.span
  · intro i
    rw [hc _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))]
    exact ready.controls i
  · rw [hc _ (by simp)]; exact ready.saved
  · rw [hc _ (by simp)]; exact ready.tmp

/-- The prepared consumer adds only the generated payload-count fact. -/
theorem ClassReady.frame (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    {width binary work saved tmp : Fin T} {B p u l target s t W V N n radius core : ℕ}
    {S F : Stacks T A}
    (ready : ports.ClassReady g width binary work saved tmp B p u l target s t W V N n radius core S)
    (hleft : F.L = S.L)
    (hframe : ∀ r, ports.classProtected g width binary work saved tmp r → F.R r = S.R r) :
    ports.ClassReady g width binary work saved tmp B p u l target s t W V N n radius core F := by
  refine ⟨ClassInputs.frame ports g ready.toClassInputs hleft ?_,?_⟩
  · intro r hr
    apply hframe r
    rcases hr with hr | hr | hr | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inl hr))
    · apply Or.inr ∘ Or.inr ∘ Or.inr
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ hr)
      · exact List.mem_append_right _ hr
  · rw [hframe _ (Or.inr (Or.inr (Or.inr (by simp [fixedControls]))))]
    exact ready.count

/-- Counter movement is invisible to the callback's retained inputs. -/
theorem ClassReady.counter (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    {width binary work saved tmp count loopSaved : Fin T} {B p u l target s t W V N n radius core : ℕ}
    {S : Stacks T A} (R : Regs T A)
    (hoff : ∀ r, ports.classProtected g width binary work saved tmp r → r ≠ count ∧ r ≠ loopSaved)
    (hR : ∀ r, r ≠ count → r ≠ loopSaved → R r = S.R r)
    (ready : ports.ClassReady g width binary work saved tmp B p u l target s t W V N n radius core S) :
    ports.ClassReady g width binary work saved tmp B p u l target s t W V N n radius core {S with R := R} := by
  apply ClassReady.frame ports g ready
  · rfl
  · intro r hr
    exact hR r (hoff r hr).1 (hoff r hr).2

/-- Consuming the origin/payload queues and appending output restores readiness
for the next origin in the class. -/
theorem ClassReady.consume (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    {width binary work saved tmp origins dst : Fin T} {B p u l target s t W V N n radius core : ℕ}
    {S : Stacks T A} (originTail tail word : List (Fin (A+4)))
    (hoff : ∀ r, ports.classProtected g width binary work saved tmp r →
      r ≠ origins ∧ r ≠ ports.archive ∧ r ≠ dst)
    (ready : ports.ClassReady g width binary work saved tmp B p u l target s t W V N n radius core S) :
    ports.ClassReady g width binary work saved tmp B p u l target s t W V N n radius core
      {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
        ports.archive tail) dst (word++S.R dst))} := by
  apply ClassReady.frame ports g ready
  · rfl
  · intro r hr
    obtain ⟨ho,ha,hd⟩ := hoff r hr
    simp only [Function.update_of_ne hd,Function.update_of_ne ha,Function.update_of_ne ho]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
