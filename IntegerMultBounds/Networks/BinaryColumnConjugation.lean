import IntegerMultBounds.Networks.BinaryColumnFrame
import IntegerMultBounds.Networks.BinaryWalshComplexConjugation

/-! Complex conjugation of the actual columnwise phase frames, including
zero columns. It changes a whole-array label frame into its genuine inverse. -/
namespace IntegerMultBounds.Networks.BinaryColumnConjugation
noncomputable section
open BinaryColumns BinaryColumnFrame
variable {h k : ℕ}

def conjugate (f : Arrays h k) : Arrays h k := fun x => star (f x)

@[simp] theorem conjugate_twice (f : Arrays h k) : conjugate (conjugate f)=f := by
  funext x
  exact star_star _

theorem lift_conjugate (j : Fin k)
    (T S : BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h)
    (hs : ∀ f,BinaryWalshComplexConjugation.conjugate (T f)=
      S (BinaryWalshComplexConjugation.conjugate f)) (f : Arrays h k) :
    conjugate (liftColumn j T f)=liftColumn j S (conjugate f) := by
  funext x
  exact congrFun (hs (fun y => f (Function.update x j y))) (x j)

theorem tensor_conjugate
    (T S : BinaryWalsh.Arrays h →ₗ[ℂ] BinaryWalsh.Arrays h)
    (hs : ∀ f,BinaryWalshComplexConjugation.conjugate (T f)=
      S (BinaryWalshComplexConjugation.conjugate f)) (f : Arrays h k) :
    conjugate (tensorColumns k T f)=tensorColumns k S (conjugate f) := by
  have hp (js : List (Fin k)) (g : Arrays h k) :
      conjugate ((js.map (fun j => liftColumn j T)).prod g)=
        (js.map (fun j => liftColumn j S)).prod (conjugate g) := by
    induction js with
    | nil => rfl
    | cons j js ih =>
      simp only [List.map_cons,List.prod_cons]
      change conjugate (liftColumn j T ((js.map (fun j => liftColumn j T)).prod g))=
        liftColumn j S ((js.map (fun j => liftColumn j S)).prod (conjugate g))
      rw [lift_conjugate j T S hs,ih]
  simpa only [tensorColumns,List.map_ofFn,Function.comp_def,id_eq] using hp (List.ofFn id) f

theorem frame_inverse (q : BinaryWalsh.Address h → ZMod 4) (f : BinaryWalsh.Arrays h) :
    (BinaryWalsh.frame q).symm f=BinaryWalsh.frame (fun x => -q x) f := by
  have he := BinaryWalsh.frame_edge q (fun _ => 0) f
  have hn : ((fun _ : BinaryWalsh.Address h => (0 : ZMod 4))-q)=(fun x => -q x) := by
    funext x
    simp
  rw [hn,BinaryWalsh.frame_zero] at he
  exact he

/-- Conjugate-forward-conjugate is the actual inverse phase frame, rather
than an arbitrary conjugated endpoint equivalence. -/
theorem frame_conjugate (q : BinaryWalsh.Address h → ZMod 4) (f : Arrays h k) :
    conjugate (frameEquiv k q f)=(frameEquiv k q).symm (conjugate f) := by
  change conjugate (tensorColumns k (BinaryWalsh.frame q).toLinearMap f)=
    tensorColumns k (BinaryWalsh.frame q).symm.toLinearMap (conjugate f)
  apply tensor_conjugate
  intro g
  change BinaryWalshComplexConjugation.conjugate (BinaryWalsh.frame q g)=
    (BinaryWalsh.frame q).symm (BinaryWalshComplexConjugation.conjugate g)
  rw [BinaryWalshComplexConjugation.frame_conjugate,frame_inverse]

theorem label_conjugate (hs : (Labels.binary h).IsSymm)
    (U : Submodule (ZMod 2) (BinaryWalsh.Address h)) (f : Arrays h k) :
    conjugate (labelFrame hs k U f)=(labelFrame hs k U).symm (conjugate f) :=
  frame_conjugate _ f

theorem rational_label_conjugate (hs : (Labels.binary h).IsSymm)
    (U : Submodule (ZMod 2) (BinaryWalsh.Address h)) (f : Arrays h k) :
    conjugate (rationalLabelFrame hs k U f)=
      (rationalLabelFrame hs k U).symm (conjugate f) := label_conjugate hs U f

end
end IntegerMultBounds.Networks.BinaryColumnConjugation
