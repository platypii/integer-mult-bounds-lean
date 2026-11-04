module

public import IntegerMultBounds.MathlibTM2.Host.RestoringSequence
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationPending

/-! Compose certified class executions on one ambient bank. Rows are witnesses
of each actual run; no fixed output-row bank is assumed for the class list. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A s width B : ℕ} [NeZero s] {P U : Type}

theorem restoringPublicationClasses_exec_within (body : P → Pr P T Q A U)
    (program : CorePublicationClass s width → Pr P T Q A U)
    (cost : CorePublicationClass s width → ℝ) (workspace : CorePublicationClass s width → ℕ)
    (gs : List (CorePublicationClass s width)) (q w : ℕ) (hw : 0 < width)
    (target : Fin B → ZMod s → ℂ) (error : ℝ)
    (hcover : ∀ k ∈ coreIndices s width, ∃ g ∈ gs, k ∈ g.indices)
    (output : Fin T) (outputTail : List (Fin (A+4))) (S : Stacks T A) (depth : ℕ)
    (hstep : ∀ g ∈ gs, ∀ (v : HS T Q A U) (ambient : Fin B → List (Fin (A+4))),
      (∀ j, (ambient j).length = s*w) →
      ∃ rows : Fin B → ℕ → List GaussianInt, ∃ v', ∃ n : ℕ,
        (∀ j k, k ∈ g.indices → (rows j k).length = g.length) ∧
        (∀ j k, k ∈ g.indices →
          let out := packedIntervalRead q w (coreStart width k) (cstream A w (rows j k))
          (∀ z ∈ ownedCore s width k, ‖out z‖ ≤ 1) ∧
            PhaseCellInterface.ErrorOn (ownedCore s width k) out (target j) error) ∧
        v'.user = v.user ∧ (n : ℝ) ≤ cost g ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v
            {S with R := Function.update S.R output ((List.ofFn ambient).flatten++outputTail)})+depth+workspace g)
          depth (program g)
          (mk v {S with R := Function.update S.R output ((List.ofFn ambient).flatten++outputTail)}) n
          (mk v' {S with R := (Function.update S.R output
            ((List.ofFn fun j => g.output w hw (rows j) (ambient j)).flatten++outputTail))}))
    (v : HS T Q A U) (ambient : Fin B → List (Fin (A+4)))
    (hambient : ∀ j, (ambient j).length = s*w) :
    ∃ v', ∃ n : ℕ, ∃ published : Fin B → List (Fin (A+4)),
      v'.user = v.user ∧ (n : ℝ) ≤ (gs.map cost).sum+1 ∧
      (∀ j, (published j).length = s*w) ∧
      (∀ j (i : ZMod s), ‖pairedCellRead q w (published j) i‖ ≤ 1) ∧
      (∀ j i, ‖pairedCellRead q w (published j) i-target j i‖ ≤ error) ∧
      mnSize (mk v' {S with R := Function.update S.R output ((List.ofFn published).flatten++outputTail)}) ≤
        mnSize (mk v {S with R := Function.update S.R output ((List.ofFn ambient).flatten++outputTail)}) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v
          {S with R := Function.update S.R output ((List.ofFn ambient).flatten++outputTail)})+depth+
            restoringSequenceWorkspace workspace gs) depth (restoringSequence program gs)
        (mk v {S with R := Function.update S.R output ((List.ofFn ambient).flatten++outputTail)}) n
        (mk v' {S with R := Function.update S.R output ((List.ofFn published).flatten++outputTail)}) := by
  let state (words : Fin B → List (Fin (A+4))) : Stacks T A :=
    {S with R := Function.update S.R output ((List.ofFn words).flatten++outputTail)}
  let Inv (remaining : List (CorePublicationClass s width)) (F : Stacks T A) : Prop :=
    remaining ⊆ gs ∧ ∃ words : Fin B → List (Fin (A+4)),
      (∀ j, (words j).length = s*w) ∧
      (∀ j, CorePublicationPending remaining q w (words j) (target j) error ∧
        CorePublicationPending remaining q w (words j) (fun _ => 0) 1) ∧ F = state words
  have hstage (g remaining) (u : HS T Q A U) F (hInv : Inv (g::remaining) F) :
      ∃ u' G, ∃ n : ℕ, u'.user = u.user ∧ (n : ℝ) ≤ cost g ∧ Inv remaining G ∧
        mnSize (mk u' G) ≤ mnSize (mk u F) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk u F)+depth+workspace g)
          depth (program g) (mk u F) n (mk u' G) := by
    rcases hInv with ⟨hmem,words,hlen,hpending,rfl⟩
    obtain ⟨rows,u',n,hrows,hgood,hu,hn,hx⟩ := hstep g (hmem (by simp)) u words hlen
    let next (j : Fin B) := g.output w hw (rows j) (words j)
    have hnext (j) : (next j).length = s*w := g.output_length w hw (rows j) (hrows j) (words j) (hlen j)
    have hnextPending (j) : CorePublicationPending remaining q w (next j) (target j) error ∧
        CorePublicationPending remaining q w (next j) (fun _ => 0) 1 := by
      constructor
      · exact CorePublicationPending.step g remaining q w hw (rows j) (hrows j) (words j) (hlen j)
          (target j) error (fun k hk => (hgood j k hk).2) (hpending j).1
      · apply CorePublicationPending.step g remaining q w hw (rows j) (hrows j) (words j) (hlen j)
          (fun _ => 0) 1 ?_ (hpending j).2
        intro k hk z hz
        simpa only [sub_zero] using (hgood j k hk).1 z hz
    have hlenWords : ((List.ofFn next).flatten++outputTail).length =
        ((state words).R output).length := by
      have ha : ∀ row ∈ List.ofFn words, row.length = s*w := by
        intro row hr
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
        exact hlen j
      have hb : ∀ row ∈ List.ofFn next, row.length = s*w := by
        intro row hr
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
        exact hnext j
      simp only [state,Function.update_self,List.length_append,length_flatten_const _ ha,
        length_flatten_const _ hb,List.length_ofFn]
    have hsize := mn_replace_right_size_of_length u u' (state words) output
      ((List.ofFn next).flatten++outputTail) hlenWords
    have hsize' : mnSize (mk u' (state next)) = mnSize (mk u (state words)) := by
      simpa only [state,Function.update_idem] using hsize
    refine ⟨u',state next,n,hu,hn,⟨?_,next,hnext,hnextPending,rfl⟩,hsize'.le,?_⟩
    · intro g' hg'
      exact hmem (by simp [hg'])
    · exact hx
  obtain ⟨v',F,n,hu,hn,hF,hs,hx⟩ := restoringSequence_exec_within body program Inv cost workspace depth hstage
    gs v (state ambient) ⟨by intro g hg; exact hg,ambient,hambient,
      (fun j => ⟨CorePublicationPending.of_cover gs q w (ambient j) (target j) error hcover,
        CorePublicationPending.of_cover gs q w (ambient j) (fun _ => 0) 1 hcover⟩),rfl⟩
  rcases hF.2 with ⟨published,hlen,hpending,rfl⟩
  refine ⟨v',n,published,hu,hn,hlen,?_,?_,hs,hx⟩
  · intro j
    simpa only [sub_zero] using CorePublicationPending.finish q w hw (published j) (fun _ => 0) 1 (hpending j).2
  · exact fun j => CorePublicationPending.finish q w hw (published j) (target j) error (hpending j).1

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
