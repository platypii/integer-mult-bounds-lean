module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPayload
public import IntegerMultBounds.MathlibTM2.StackResources
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Generate a payload counter once and compose an independently bounded body. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem withPayloadCounter_exec_within (src count saved : Fin T)
    (hreg : [src,count,saved].Nodup) (V : ℕ) (ys : List (Fin (A+4)))
    (run : Pr P T Q A U) (runCost runStock depth : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hlen : (S.R src).length = V) (hcount : S.R count = []) (hsaved : S.R saved = [])
    (hrun : ∀ u : HS T Q A U, ∃ u' n, u'.user = u.user ∧ n ≤ runCost ∧
      ExecWithin body (fun z state => mnSize state+z ≤
        mnSize (mk u (payloadCountedState S count V))+depth+runStock) depth run (mk u (payloadCountedState S count V)) n
        (mk u' {payloadCountedState S count V with L := fun _ => [], R := (Function.update
          (Function.update (payloadCountedState S count V).R src ys) count [])})) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (4*V+4)+runCost ∧
      ExecWithin body (fun z state => mnSize state+z ≤
        mnSize (mk v S)+depth+2*(4*V+4)+runStock) depth (withPayloadCounter src count saved run) (mk v S) n
        (mk v' {S with L := fun _ => [], R := Function.update S.R src ys}) := by
  have hsc : src ≠ count := by intro he; exact (List.nodup_cons.mp hreg).1 (by simp [he])
  have hss : src ≠ saved := by intro he; exact (List.nodup_cons.mp hreg).1 (by simp [he])
  have hcs : count ≠ saved := by intro he; exact (List.nodup_cons.mp (List.nodup_cons.mp hreg).2).1 (by simp [he])
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) hsc hss hcs v S hsaved
  have he₁' : Exec body (ucopy src count saved) (mk v S) (4*V+4)
      (mk v₁ (payloadCountedState S count V)) := by
    simpa only [hlen,hcount,List.append_nil,payloadCountedState] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hrun v₁
  have hw₁ := mn_native_exec_within he₁' 2 (by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,whileR,moveStep,peekR,
      mnNativePushBound,mnActPush]) depth (mnSize (mk v S)+depth+2*(4*V+4)) (le_refl _)
  have hsetup := hw₁.final
  let bound := mnSize (mk v S)+depth+2*(4*V+4)+runStock
  have hw₁' := hw₁.mono (J := fun z state => mnSize state+z ≤ bound) (by
    intro z state hs
    exact hs.trans (Nat.le_add_right _ _))
  have hw₂ := he₂.mono (J := fun z state => mnSize state+z ≤ bound) (by
    intro z state hs
    exact hs.trans (Nat.add_le_add_right hsetup runStock))
  have hwhole := ExecWithin.seq hw₁' hw₂
  obtain ⟨vf,n,hu,hn,he⟩ := withPayloadCounter_exec src count saved hreg V ys run runCost v S
    hlen hcount hsaved (by
      intro u
      obtain ⟨u',n,hu,hn,he⟩ := hrun u
      exact ⟨u',n,hu,hn,he.toExec⟩)
  obtain ⟨hsteps,hfinal⟩ := hwhole.toExec.unique he
  rw [hsteps,hfinal] at hwhole
  exact ⟨vf,n,hu,hn,hwhole⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
