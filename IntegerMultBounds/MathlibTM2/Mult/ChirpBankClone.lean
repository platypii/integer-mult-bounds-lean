module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoad

/-! # Install consumer banks from computed parameter words

The source bank supplies its two length headers and retained binary variables.
Indices may repeat, so every unused consumer slot can copy a shared zero word.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A n m : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpBankClone (src : TblR n → Fin T) (dst : TblR m → Fin T) (index : Fin m → Fin n) : Pr P T Q A U :=
  chirpBankLoad dst (fun i => src (.v (index i))) (src .wr) (src .wn)

/-- Clone a computed bank into a fresh consumer bank, preserving the source and spectators. -/
theorem chirpBankClone_exec (src : TblR n → Fin T) (dst : TblR m → Fin T)
    (hsrc : Function.Injective src) (hdst : Function.Injective dst)
    (hsep : ∀ r s, dst r ≠ src s) (index : Fin m → Fin n)
    (W e : ℕ) (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = e)
    (st : TblSt n A) (hfit : ∀ i, st.val i < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds src S (tblRho W wl nl st))
    (hblank : ∀ r, S.R (dst r) = []) :
    ∃ v' R, v'.user = v.user ∧
      Exec body (chirpBankClone src dst index) (mk v S)
        (chirpBankLoadCost dst (fun i => src (.v (index i))) W e (fun _ => W)) (mk v' { S with R := R }) ∧
      tblHolds dst { S with R := R }
        (tblRho W (List.replicate W tick) (List.replicate e tick) ⟨fun i => st.val (index i), []⟩) ∧
      (∀ k, (∀ r, k ≠ dst r) → R k = S.R k) := by
  classical
  let source : Fin n → Fin T := fun i => src (.v i)
  have hinj : Function.Injective source := fun _ _ h => TblR.v.inj (hsrc h)
  let value : Fin T → ℕ := Function.extend source st.val (fun _ => 0)
  have hget (i : Fin n) : value (src (.v i)) = st.val i := hinj.extend_apply _ _ i
  obtain ⟨v', hu, he⟩ := chirpBankLoad_exec (body := body) dst hdst (fun i => src (.v (index i)))
    (src .wr) (src .wn) (fun r => hsep r .wr) (fun r => hsep r .wn)
    (fun i r => hsep r (.v (index i))) W e (fun _ => W) value
    (by intro i; rw [hget]; exact hfit _) (by intro i; exact le_rfl)
    v S (by rw [hS .wr]; exact hwl) (by rw [hS .wn]; exact hnl)
    (by intro i; rw [hget, hS (.v (index i))]; rfl) hblank
  refine ⟨v', _, hu, he, ?_, ?_⟩
  · have hh := chirpBankLoad_holds dst hdst (fun i => src (.v (index i))) W e value S hblank
    simpa only [hget] using hh
  · intro k hk
    exact chirpBankLoad_off dst _ W e value S.R k hk

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
