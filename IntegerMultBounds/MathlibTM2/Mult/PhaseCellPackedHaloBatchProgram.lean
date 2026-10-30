module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloNextInputExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type}

def packedHaloBatchReg : Fin 248 → Fin 249 := Fin.castLE (by decide)

noncomputable def packedHaloBatchStep (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 249 Q A U :=
  let step : Pr P 248 Q A U := .seq packedFreshOutput (packedHaloPreparedInput hR hQ)
  embProg packedHaloBatchReg id step

/-- One fixed program; only the unary counter varies with the replica count. -/
noncomputable def packedHaloBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 249 Q A U :=
  countedLoop 248 (packedHaloBatchStep hR hQ)

def packedHaloBatchCost (replicas perInput : ℕ) : ℕ := replicas*(perInput+3)+2

/-- Lift the checked numerical step while preserving the external loop counter. -/
theorem packedHaloBatchStep_exec {body : P → Pr P 248 Q A U} {body' : P → Pr P 249 Q A U}
    (hbody : ∀ f, body' f = embProg packedHaloBatchReg id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {v v' : HS 248 Q A U} {S F : Stacks 248 A} {n : ℕ}
    (he : Exec body (.seq (packedFreshOutput (P := P) (U := U)) (packedHaloPreparedInput (P := P) (U := U) hR hQ)) (mk v S) n (mk v' F))
    (v₀ : HS 249 Q A U) (S₀ : Stacks 249 A)
    (hv : embDn packedHaloBatchReg v₀ = v) (hS : embStk packedHaloBatchReg S₀ = S) :
    ∃ v₁ F₁, v₁.user = v'.user ∧
      Exec body' (packedHaloBatchStep hR hQ) (mk v₀ S₀) n (mk v₁ F₁) ∧
      embStk packedHaloBatchReg F₁ = F ∧
      F₁.L 248 = S₀.L 248 ∧ F₁.R 248 = S₀.R 248 := by
  have hinj : Function.Injective packedHaloBatchReg := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin 249 => k.val) hij)
  obtain ⟨v₁,F₁,hex,hv₁,hu₁,hview,hframe⟩ := exec_emb hinj hbody he v₀ hv S₀ hS
  have hcounter := hframe 248 (by
    intro i heq
    have hv := congrArg Fin.val heq
    have hi := i.isLt
    change i.val = 248 at hv
    omega)
  exact ⟨v₁,F₁,hu₁,hex,hview,hcounter⟩

/-- Scheduling bridge for a structural numerical invariant on the solver bank.
The concrete one-input execution discharges `hstep`; the loop itself only
consumes its isolated counter and pays three control steps per input. -/
theorem packedHaloBatch_exec {body : P → Pr P 248 Q A U} {body' : P → Pr P 249 Q A U}
    (hbody : ∀ f, body' f = embProg packedHaloBatchReg id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (N cost : ℕ)
    (Inv : ℕ → Stacks 248 A → Prop)
    (hstep : ∀ j < N, ∀ (v : HS 248 Q A U) S, Inv j S →
      ∃ v' F n, v'.user = v.user ∧ n ≤ cost ∧
        Exec body (.seq packedFreshOutput (packedHaloPreparedInput hR hQ)) (mk v S) n (mk v' F) ∧ Inv (j+1) F)
    (v : HS 249 Q A U) (S : Stacks 249 A) (hcount : (S.R 248).length = N)
    (hInv : Inv 0 (embStk packedHaloBatchReg S)) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ packedHaloBatchCost N cost ∧
      Exec body' (packedHaloBatch hR hQ) (mk v S) n (mk v' F) ∧
      F.R 248 = [] ∧ Inv N (embStk packedHaloBatchReg F) := by
  apply countedLoop_exec 248 (packedHaloBatchStep hR hQ) N cost
    (fun j S => Inv j (embStk packedHaloBatchReg S)) ?_ ?_ v S hcount hInv
  · intro j S xs hI
    have hview : embStk packedHaloBatchReg {S with R := Function.update S.R 248 xs} =
        embStk packedHaloBatchReg S := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      have hne : packedHaloBatchReg i ≠ 248 := by
        intro he; have hv := congrArg (fun k : Fin 249 => k.val) he
        have hi := i.isLt; change i.val = 248 at hv; omega
      exact Function.update_of_ne hne _ _
    rw [hview]; exact hI
  · intro j hj v S hI
    obtain ⟨v₁,F,n,hu,hn,he,hnext⟩ := hstep j hj (embDn packedHaloBatchReg v)
      (embStk packedHaloBatchReg S) hI
    obtain ⟨v₂,F₂,hu₂,he₂,hview,hleft,hcounter⟩ := packedHaloBatchStep_exec hbody hR hQ he v S rfl rfl
    refine ⟨v₂,F₂,n,hu₂.trans hu,hn,he₂,hcounter,?_⟩
    rw [hview]; exact hnext

/-- Certificates retain the physical state at which each input was solved.
Later output prefixes therefore cannot invalidate an earlier accuracy claim. -/
inductive PackedHaloInputTrace {X : Type} (Result : X → Stacks 248 A → Stacks 248 A → Prop) :
    List X → Stacks 248 A → Stacks 248 A → Prop
  | nil (S) : PackedHaloInputTrace Result [] S S
  | cons {x xs S M F} : Result x S M → PackedHaloInputTrace Result xs M F →
      PackedHaloInputTrace Result (x::xs) S F

theorem PackedHaloInputTrace.append {X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop}
    {xs ys : List X} {S M F : Stacks 248 A}
    (h : PackedHaloInputTrace Result xs S M) (h' : PackedHaloInputTrace Result ys M F) :
    PackedHaloInputTrace Result (xs++ys) S F := by
  induction h with
  | nil => exact h'
  | cons hx _ ih => exact .cons hx (ih h')

/-- Forget auxiliary transition certificates without changing physical states. -/
theorem PackedHaloInputTrace.mono {X : Type}
    {Result Result' : X → Stacks 248 A → Stacks 248 A → Prop}
    (hresult : ∀ x S F, Result x S F → Result' x S F)
    {xs : List X} {S F : Stacks 248 A} (h : PackedHaloInputTrace Result xs S F) :
    PackedHaloInputTrace Result' xs S F := by
  induction h with
  | nil => exact .nil _
  | cons hx _ ih => exact .cons (hresult _ _ _ hx) ih

/-- Split a batch trace at an arbitrary input prefix, retaining its physical
boundary state rather than reconstructing that state from numerical outputs. -/
theorem PackedHaloInputTrace.split {X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop}
    (xs ys : List X) {S F : Stacks 248 A}
    (h : PackedHaloInputTrace Result (xs++ys) S F) :
    ∃ M, PackedHaloInputTrace Result xs S M ∧ PackedHaloInputTrace Result ys M F := by
  induction xs generalizing S with
  | nil => exact ⟨S,.nil S,h⟩
  | cons x xs ih =>
    cases h with
    | cons hx ht =>
      obtain ⟨M,hprefix,hsuffix⟩ := ih ht
      exact ⟨M,.cons hx hprefix,hsuffix⟩

/-- Thread a suffix-indexed readiness predicate along a physical trace.
The transition premise must come from execution; numerical accuracy alone does
not establish readiness of intermediate stores. -/
theorem PackedHaloInputTrace.ready {X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop}
    (Ready : List X → Stacks 248 A → Prop)
    (hstep : ∀ x xs S F, Result x S F → Ready (x::xs) S → Ready xs F)
    {xs ys : List X} {S F : Stacks 248 A}
    (h : PackedHaloInputTrace Result xs S F) (hready : Ready (xs++ys) S) :
    Ready ys F := by
  induction h with
  | nil => exact hready
  | cons hx ht ih => exact ih (hstep _ _ _ _ hx hready)

theorem PackedHaloInputTrace.ready_prefix {X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop}
    (Ready : List X → Stacks 248 A → Prop)
    (hstep : ∀ x xs S F, Result x S F → Ready (x::xs) S → Ready xs F)
    (xs ys : List X) {S F : Stacks 248 A}
    (h : PackedHaloInputTrace Result (xs++ys) S F) (hready : Ready (xs++ys) S) :
    ∃ M, PackedHaloInputTrace Result xs S M ∧ Ready ys M ∧
      PackedHaloInputTrace Result ys M F := by
  obtain ⟨M,hprefix,hsuffix⟩ := h.split xs ys
  exact ⟨M,hprefix,hprefix.ready Ready hstep hready,hsuffix⟩

/-- Any observation restored by each numerical input is restored by the batch.
Use a tuple observation to carry the host frame and retained registers together. -/
theorem PackedHaloInputTrace.frame {X Y : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop}
    (observe : Stacks 248 A → Y)
    (hresult : ∀ x S F, Result x S F → observe F = observe S)
    {xs : List X} {S F : Stacks 248 A} (h : PackedHaloInputTrace Result xs S F) :
    observe F = observe S := by
  induction h with
  | nil => rfl
  | cons hx _ ih => exact ih.trans (hresult _ _ _ hx)

/-- Account for the persistent output archive separately from temporary scratch. -/
theorem PackedHaloInputTrace.output_length {X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop} {L : ℕ}
    (hresult : ∀ x S F, Result x S F → (F.R 132).length = L+(S.R 132).length)
    {xs : List X} {S F : Stacks 248 A} (h : PackedHaloInputTrace Result xs S F) :
    (F.R 132).length = xs.length*L+(S.R 132).length := by
  induction h with
  | nil => simp
  | cons hx _ ih =>
    rw [ih,hresult _ _ _ hx]
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Every completed-input prefix fits in the final persistent archive budget. -/
theorem PackedHaloInputTrace.prefix_archive_le {X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop} {L : ℕ}
    (hresult : ∀ x S F, Result x S F → (F.R 132).length = L+(S.R 132).length)
    (xs ys : List X) {S F : Stacks 248 A}
    (h : PackedHaloInputTrace Result (xs++ys) S F) :
    ∃ M, PackedHaloInputTrace Result xs S M ∧ PackedHaloInputTrace Result ys M F ∧
      (M.R 132).length ≤ (F.R 132).length := by
  obtain ⟨M,hprefix,hsuffix⟩ := h.split xs ys
  refine ⟨M,hprefix,hsuffix,?_⟩
  have hlen := hsuffix.output_length hresult
  omega

/-- Execute an arbitrary input list with one fixed counted program. `Ready`
tracks the unconsumed queue and shared setup; `Result` retains each numerical
output certificate. Neither predicate mentions the external loop counter. -/
theorem packedHaloBatch_list_exec {X : Type}
    {body : P → Pr P 248 Q A U} {body' : P → Pr P 249 Q A U}
    (hbody : ∀ f, body' f = embProg packedHaloBatchReg id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (cost : ℕ)
    (Ready : List X → Stacks 248 A → Prop)
    (Result : X → Stacks 248 A → Stacks 248 A → Prop)
    (hstep : ∀ x xs (v : HS 248 Q A U) S, Ready (x::xs) S →
      ∃ v' F n, v'.user = v.user ∧ n ≤ cost ∧
        Exec body (.seq packedFreshOutput (packedHaloPreparedInput hR hQ))
          (mk v S) n (mk v' F) ∧ Ready xs F ∧ Result x S F)
    (xs : List X) (v : HS 249 Q A U) (S : Stacks 249 A)
    (hcount : (S.R 248).length = xs.length)
    (hready : Ready xs (embStk packedHaloBatchReg S)) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ packedHaloBatchCost xs.length cost ∧
      Exec body' (packedHaloBatch hR hQ) (mk v S) n (mk v' F) ∧
      F.R 248 = [] ∧ Ready [] (embStk packedHaloBatchReg F) ∧
      PackedHaloInputTrace Result xs (embStk packedHaloBatchReg S)
        (embStk packedHaloBatchReg F) ∧
      PackedHaloInputTrace (fun x S F => Result x S F ∧ ∃ todo, Ready todo F ∧ todo.length ≤ xs.length)
        xs (embStk packedHaloBatchReg S) (embStk packedHaloBatchReg F) := by
  let Inv := fun j T => ∃ done todo : List X,
    xs = done++todo ∧ done.length = j ∧ Ready todo T ∧
      PackedHaloInputTrace (fun x S F => Result x S F ∧ ∃ todo, Ready todo F ∧ todo.length ≤ xs.length) done (embStk packedHaloBatchReg S) T
  obtain ⟨v',F,n,hu,hn,he,hcounter,hI⟩ := packedHaloBatch_exec hbody hR hQ
    xs.length cost Inv (by
      intro j hj vi T hI
      obtain ⟨done,todo,hxs,hlen,hready,htrace⟩ := hI
      cases todo with
      | nil => simp only [List.append_nil] at hxs; subst xs; omega
      | cons x todo =>
        obtain ⟨vf,G,m,hu,hm,he,hr,hresult⟩ := hstep x todo vi T hready
        refine ⟨vf,G,m,hu,hm,he,done++[x],todo,?_,?_,hr,?_⟩
        · simpa only [List.append_assoc,List.singleton_append] using hxs
        · simp only [List.length_append,List.length_singleton,hlen]
        · exact htrace.append (.cons ⟨hresult,todo,hr,by
            have hh := congrArg List.length hxs
            simp only [List.length_append,List.length_cons] at hh
            omega⟩ (.nil G))) v S hcount
    ⟨[],xs,rfl,rfl,hready,.nil _⟩
  obtain ⟨done,todo,hxs,hlen,hr,htrace⟩ := hI
  have hnil : todo = [] := by
    have hlength := congrArg List.length hxs
    simp only [List.length_append] at hlength
    have : todo.length = 0 := by omega
    cases todo with
    | nil => rfl
    | cons x todo => simp only [List.length_cons] at this; omega
  subst todo
  simp only [List.append_nil] at hxs
  subst done
  exact ⟨v',F,n,hu,hn,he,hcounter,hr,htrace.mono (fun _ _ _ h => h.1),htrace⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
