module

public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! Count a bounded interval without constructing its initial index in unary. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM

/-- The current index is already installed; stop at the retained upper bound. -/
def tblForFrom {n : ℕ} (i nv : Fin n) (body : TblCode n) : TblCode n :=
  .loop i nv (.seq body (.ins (.inc i)))

theorem TblDo.forFrom {A W w n : ℕ} {i nv : Fin n} {body : TblCode n}
    {st : TblSt n A} {P : TblSt n A → Prop}
    (origin N Kb : ℕ) (hindex : st.val i = origin) (hN : st.val nv = origin+N)
    (hNW : origin+N < 2^W) (hi : i ≠ nv)
    (Inv : ℕ → TblSt n A → Prop) (h0 : Inv 0 st)
    (hstep : ∀ j < N, ∀ s, Inv j s → s.val i = origin+j → s.val nv = origin+N →
      TblDo A W w body s (fun s' => s'.val i = origin+j ∧ s'.val nv = origin+N ∧
        Inv (j+1) ⟨Function.update s'.val i (origin+j+1),s'.acc⟩) Kb)
    (hend : ∀ s, Inv N s → s.val i = origin+N → s.val nv = origin+N → P s) :
    TblDo A W w (tblForFrom i nv body) st P (N*(Kb+3)+2) := by
  unfold tblForFrom
  have hc : TblDo A W w (.loop i nv (.seq body (.ins (.inc i)))) st P (N*(Kb+1+2)+2) := by
    apply TblDo.loop (fun j s => Inv j s ∧ s.val i = origin+j ∧ s.val nv = origin+N) N (Kb+1)
    · exact ⟨h0,by simpa using hindex,hN⟩
    · intro j hj s ⟨hs,hsi,hsn⟩
      refine ⟨by rw [hsi,hsn]; omega,?_⟩
      refine (hstep j hj s hs hsi hsn).seq (fun s' ⟨h1,h2,h3⟩ => TblDo.ins (.inc i) ?_)
      have hm : (s'.val i+1) % 2^W = origin+j+1 := by
        rw [h1]; exact Nat.mod_eq_of_lt (by omega)
      refine ⟨by simpa [TblIns.run,hm,Nat.add_assoc] using h3,by simp [TblIns.run,hm,Nat.add_assoc],?_⟩
      simp [TblIns.run,Function.update_of_ne hi.symm,h2]
    · intro s ⟨hs,hsi,hsn⟩
      exact ⟨by rw [hsi,hsn]; exact lt_irrefl _,hend s hs hsi hsn⟩
  simpa only [Nat.add_assoc] using hc

end IntegerMultBounds.MathlibTM2.Fast.TableVM
