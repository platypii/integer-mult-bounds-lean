module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBatchProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoopTrace

/-! The packed numerical loop pays one body workspace allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type}

theorem packedHaloBatch_exec_trace {body : P → Pr P 248 Q A U} {body' : P → Pr P 249 Q A U}
    (hbody : ∀ f, body' f = embProg packedHaloBatchReg id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (N cost H : ℕ)
    (Inv : ℕ → Stacks 248 A → Prop)
    (hstep : ∀ j < N, ∀ (v : HS 248 Q A U) S, Inv j S →
      ∃ v' F n, v'.user = v.user ∧ n ≤ cost ∧
        Exec body (.seq packedFreshOutput (packedHaloPreparedInput hR hQ)) (mk v S) n (mk v' F) ∧ Inv (j+1) F)
    (v : HS 249 Q A U) (S : Stacks 249 A) (hcount : (S.R 248).length = N)
    (hstock : ∀ j ≤ N, ∀ T, Inv j (embStk packedHaloBatchReg T) →
      T.L 248 = S.L 248 → (T.R 248).length ≤ N → ∀ vi : HS 249 Q A U, mnSize (mk vi T) ≤ H)
    (hInv : Inv 0 (embStk packedHaloBatchReg S)) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ (Finset.range N).sum (fun _ => cost+3)+2 ∧
      Exec body' (packedHaloBatch hR hQ) (mk v S) n (mk v' F) ∧
      F.R 248 = [] ∧ (Inv N (embStk packedHaloBatchReg F) ∧ F.L 248 = S.L 248) ∧
      ∀ c, mnProgPush (packedHaloBatchStep (P := P) (U := U) (A := A) hR hQ) ≤ c →
        (∀ f, mnProgPush (body' f) ≤ c) → ∀ depth,
        ExecWithin body' (fun d z => mnSize z+d ≤ H+depth+(c+1)*cost)
          depth (packedHaloBatch hR hQ) (mk v S) n (mk v' F) := by
  apply countedLoop_exec_trace 248 (packedHaloBatchStep hR hQ) N cost H
    (fun j T => Inv j (embStk packedHaloBatchReg T) ∧ T.L 248 = S.L 248) ?_ ?_ ?_ v S hcount ⟨hInv,rfl⟩
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
  · intro j hj v S hI _
    obtain ⟨v₁,F,n,hu,hn,he,hnext⟩ := hstep j hj (embDn packedHaloBatchReg v)
      (embStk packedHaloBatchReg S) hI.1
    obtain ⟨v₂,F₂,hu₂,he₂,hview,hleft,hcounter⟩ := packedHaloBatchStep_exec hbody hR hQ he v S rfl rfl
    refine ⟨v₂,F₂,n,hu₂.trans hu,hn,he₂,hcounter,?_⟩
    exact ⟨by rw [hview]; exact hnext,hleft.trans hI.2⟩

  · intro j hj T hI hc vi
    exact hstock j hj T hI.1 hI.2 hc vi

theorem packedHaloBatch_list_exec_trace {X : Type}
    {body : P → Pr P 248 Q A U} {body' : P → Pr P 249 Q A U}
    (hbody : ∀ f, body' f = embProg packedHaloBatchReg id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (cost H : ℕ)
    (Ready : List X → Stacks 248 A → Prop)
    (Result : X → Stacks 248 A → Stacks 248 A → Prop)
    (hstep : ∀ x xs (v : HS 248 Q A U) S, Ready (x::xs) S →
      ∃ v' F n, v'.user = v.user ∧ n ≤ cost ∧
        Exec body (.seq packedFreshOutput (packedHaloPreparedInput hR hQ))
          (mk v S) n (mk v' F) ∧ Ready xs F ∧ Result x S F)
    (xs : List X) (v : HS 249 Q A U) (S : Stacks 249 A)
    (hcount : (S.R 248).length = xs.length)
    (hready : Ready xs (embStk packedHaloBatchReg S))
    (hboundary : ∀ done todo T, xs = done++todo → Ready todo (embStk packedHaloBatchReg T) →
      PackedHaloInputTrace Result done (embStk packedHaloBatchReg S) (embStk packedHaloBatchReg T) →
      T.L 248 = S.L 248 → (T.R 248).length ≤ xs.length →
      ∀ vi : HS 249 Q A U, mnSize (mk vi T) ≤ H) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ packedHaloBatchCost xs.length cost ∧
      Exec body' (packedHaloBatch hR hQ) (mk v S) n (mk v' F) ∧
      F.R 248 = [] ∧ Ready [] (embStk packedHaloBatchReg F) ∧
      PackedHaloInputTrace Result xs (embStk packedHaloBatchReg S)
        (embStk packedHaloBatchReg F) ∧
      PackedHaloInputTrace (fun x S F => Result x S F ∧ ∃ todo, Ready todo F ∧ todo.length ≤ xs.length)
        xs (embStk packedHaloBatchReg S) (embStk packedHaloBatchReg F) ∧
      (∀ done suffix, xs = done++suffix → ∃ M,
        PackedHaloInputTrace Result done (embStk packedHaloBatchReg S) M ∧
        (∃ remaining, Ready remaining M ∧ remaining.length ≤ xs.length) ∧
        PackedHaloInputTrace Result suffix M (embStk packedHaloBatchReg F)) ∧ F.L 248 = S.L 248 ∧
      ∀ c, mnProgPush (packedHaloBatchStep (P := P) (U := U) (A := A) hR hQ) ≤ c →
        (∀ f, mnProgPush (body' f) ≤ c) → ∀ depth,
        ExecWithin body' (fun d z => mnSize z+d ≤ H+depth+(c+1)*cost)
          depth (packedHaloBatch hR hQ) (mk v S) n (mk v' F) := by
  let Inv := fun j T => ∃ done todo : List X,
    xs = done++todo ∧ done.length = j ∧ Ready todo T ∧
      PackedHaloInputTrace (fun x S F => Result x S F ∧ ∃ todo, Ready todo F ∧ todo.length ≤ xs.length) done (embStk packedHaloBatchReg S) T
  obtain ⟨v',F,n,hu,hn,he,hcounter,⟨hI,hleft⟩,hwithin⟩ := packedHaloBatch_exec_trace hbody hR hQ
    xs.length cost H Inv (by
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
    (by
      intro j hj T ⟨done,todo,hxs,hlen,hr,ht⟩ hl hc vi
      exact hboundary done todo T hxs hr (ht.mono (fun _ _ _ h => h.1)) hl hc vi)
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
  have hn' : n ≤ packedHaloBatchCost xs.length cost := by
    simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul,packedHaloBatchCost] using hn
  refine ⟨v',F,n,hu,hn',he,hcounter,hr,htrace.mono (fun _ _ _ h => h.1),htrace,?_,hleft,hwithin⟩
  intro done suffix hsplit
  have hfull := htrace
  rw [hsplit] at hfull
  obtain ⟨M,hprefix,hreadyM,hsuffix⟩ := hfull.prefix_boundary
    (fun T => ∃ remaining, Ready remaining T ∧ remaining.length ≤ xs.length)
    (fun _ _ _ h => by simpa only [← hsplit] using h.2) done suffix ⟨xs,hready,le_rfl⟩
  exact ⟨M,hprefix.mono (fun _ _ _ h => h.1),hreadyM,hsuffix.mono (fun _ _ _ h => h.1)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
