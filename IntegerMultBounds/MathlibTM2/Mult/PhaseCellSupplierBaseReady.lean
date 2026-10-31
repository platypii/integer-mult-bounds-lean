module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupplierClassReady

/-! Ordinary supplier readiness before changing numerical headers are generated. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierInputPlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T A s : ℕ} [NeZero s]

def baseSupport (input : SupplierInputPlan T) : List (Fin T) :=
  List.ofFn input.work ++ (List.ofFn input.parameters ++ (List.ofFn input.classDest ++
    [input.publication.retained 6,input.publication.retained 7,input.publication.retained 8,input.span,input.word]))

structure BaseReady (input : SupplierInputPlan T) (r : PackedNormalizedJob A s) (S : Stacks T A) : Prop where
  classHeaders : input.ClassReady r S
  blank : ∀ i, S.R (input.work i) = []
  left : ∀ i, S.L (input.work i) = []
  parameters : ∀ i, (S.R (input.parameters i)).length = ![r.p,r.u,r.l,r.targetOut,s,r.t,r.a,r.b] i
  payload : S.R (input.publication.retained 6) = cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten
  tmp : S.R (input.publication.retained 7) = []
  saved : S.R (input.publication.retained 8) = []
  span : S.R input.span = []
  word : S.R input.word = []

theorem BaseReady.complete {input : SupplierInputPlan T} {r : PackedNormalizedJob A s} {S : Stacks T A}
    (h : input.BaseReady r S) (hmasters : ∀ i, (S.R (input.masters i)).length = r.factoryMasters i)
    (hgeometry : (S.R (input.publication.retained 1)).length = r.V) : input.Ready r S :=
  ⟨h.blank,h.left,hmasters,h.classHeaders.radius,hgeometry,h.classHeaders.headers,h.payload,h.tmp,h.saved,
    h.span,h.parameters,h.classHeaders.width,h.classHeaders.core,h.word⟩

theorem BaseReady.of_frame {input : SupplierInputPlan T} {r : PackedNormalizedJob A s} {S F : Stacks T A}
    (h : input.BaseReady r S) (hR : ∀ k ∈ input.baseSupport, F.R k = S.R k) (hL : F.L = S.L) :
    input.BaseReady r F := by
  have hw (i : Fin 325) : F.R (input.work i) = S.R (input.work i) :=
    hR _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  have hp (i : Fin 8) : F.R (input.parameters i) = S.R (input.parameters i) :=
    hR _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))
  have hc (i : Fin 7) : F.R (input.classDest i) = S.R (input.classDest i) :=
    hR _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))))
  have hx (k : Fin T) (hk : k ∈ [input.publication.retained 6,input.publication.retained 7,
      input.publication.retained 8,input.span,input.word]) : F.R k = S.R k :=
    hR _ (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hk)))
  refine ⟨h.classHeaders.of_frame hc,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i; rw [hw]; exact h.blank i
  · intro i; rw [hL]; exact h.left i
  · intro i; rw [hp]; exact h.parameters i
  · rw [hx _ (by simp)]; exact h.payload
  · rw [hx _ (by simp)]; exact h.tmp
  · rw [hx _ (by simp)]; exact h.saved
  · rw [hx _ (by simp)]; exact h.span
  · rw [hx _ (by simp)]; exact h.word
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierInputPlan
