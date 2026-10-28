module

public import IntegerMultBounds.MathlibTM2.Fast.TableLoad
public import IntegerMultBounds.MathlibTM2.Host.UnaryBinaryHalving

/-! Table headers load by halving with additive unary-length and word-width cost. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {n : ℕ} {rg : TblR n → Fin T}

def tblLoadLinear (rg : TblR n → Fin T) (u : Fin T) (i : Fin n) : Pr P T Q A U :=
  .seq (bclear (rg (.v i)))
    (unaryBinaryWidth u (rg .wr) (rg (.v i)) (rg (.z 0)) (rg (.z 1))
      (rg (.z 2)) (rg (.z 3)) (rg (.z 4)) (rg (.z 5)))

theorem tbl_load_linear_runs (hrg : Function.Injective rg) {W : ℕ} (wl nl : List (Fin (A+4)))
    (hwl : wl.length = W) {u : Fin T} (hu : ∀ r, rg r ≠ u) (i : Fin n) (st : TblSt n A)
    (k : ℕ) (hfit : Nat.size k ≤ W) (v : HS T Q A U) (S : Stacks T A)
    (hlen : (S.R u).length = k) (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ 21*k+14*W+30 ∧
      Exec body (tblLoadLinear rg u i) (mk v S) m (mk v' S') ∧
      tblHolds rg S' (tblRho W wl nl ⟨Function.update st.val i k,st.acc⟩) ∧ tblFr rg S S' := by
  obtain ⟨v₁,hu₁,_,he₁⟩ := bclear_exec body (rg (.v i)) v S
  let S₁ : Stacks T A := {S with R := Function.update S.R (rg (.v i)) []}
  have hreg : [u,rg .wr,rg (.v i),rg (.z 0),rg (.z 1),rg (.z 2),rg (.z 3),rg (.z 4),rg (.z 5)].Nodup := by
    have hh := tbl_nodup hrg (l := [.wr,.v i,.z 0,.z 1,.z 2,.z 3,.z 4,.z 5]) (by simp)
    simp only [List.map_cons,List.map_nil] at hh
    exact List.nodup_cons.mpr ⟨by simp [Ne.symm (hu _)],hh⟩
  have hwr : (S₁.R (rg .wr)).length = W := by
    simp [S₁,Function.update_of_ne (hrg.ne (show (TblR.wr : TblR n) ≠ .v i by simp)),hS .wr,hwl]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := unaryBinaryWidth_exec (body := body) hreg k W hfit v₁ S₁
    (by simpa [S₁,Function.update_of_ne (Ne.symm (hu _))] using hlen) hwr (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [S₁]
      all_goals
        dsimp only [S₁]
        rw [Function.update_of_ne (by intro he; have hh := hrg he; cases hh)]
        rw [hS]
        rfl)
  refine ⟨v₂,_,_,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,?_,⟨rfl,rfl,rfl,fun r hr => ?_⟩⟩
  · rw [hS]
    simp only [tblRho_v,length_binSyms]
    omega
  · intro r
    dsimp only [S₁]
    rw [tbl_holds_upd hrg (tbl_holds_upd hrg hS (.v i) []) (.v i)]
    by_cases hr : r = .v i
    · subst hr; simp
    · rw [Function.update_of_ne hr,Function.update_of_ne hr]
      cases r <;> simp_all [Function.update_of_ne]
  · dsimp only [S₁]
    rw [Function.update_of_ne (Ne.symm (hr _)),Function.update_of_ne (Ne.symm (hr _))]

end IntegerMultBounds.MathlibTM2.Fast.TableVM
