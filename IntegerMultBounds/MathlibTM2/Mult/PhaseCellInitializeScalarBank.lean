module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellZeroWordBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderLoad

/-! Allocate a scalar table from blank words and install ordinary binary inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def initializeScalarBank (rg : TblR n → Fin T) : Pr P T Q A U :=
  zeroWordBank (rg .wr) (rg (.z 0)) ((List.finRange n).map (fun i => rg (.v i)))

/-- Only the width register is initially populated. The zero-valued table view
is established by actual word allocation; it is not an input premise. -/
theorem initializeScalarBank_exec (rg : TblR n → Fin T) (hrg : Function.Injective rg)
    (W : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = W)
    (v : HS T Q A U) (S : Stacks T A) (hwidth : S.R (rg .wr) = wl)
    (hblank : ∀ r : TblR n, r ≠ .wr → S.R (rg r) = []) :
    ∃ v' F, v'.user = v.user ∧
      Exec body (initializeScalarBank rg) (mk v S) (n*(4*W+4)+1) (mk v' F) ∧
      tblHolds rg F (tblRho W wl [] ⟨fun _ => 0,[]⟩) ∧ tblFr rg S F := by
  let rs := (List.finRange n).map (fun i => rg (.v i))
  have hnd : rs.Nodup := (List.nodup_finRange n).map (by
    intro i j he
    exact TblR.v.inj (hrg he))
  have hwr : rg .wr ∉ rs := by simp [rs,List.mem_map,hrg.eq_iff]
  have htmp : rg (.z 0) ∉ rs := by simp [rs,List.mem_map,hrg.eq_iff]
  obtain ⟨v',hu,he⟩ := zeroWordBank_exec (body := body)
    (hrg.ne (by simp : (TblR.wr : TblR n) ≠ .z 0)) rs hnd hwr htmp W v S
    (by rw [hwidth,hwl]) (hblank (.z 0) (by simp)) (by
      intro r hr
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
      exact hblank (.v i) (by simp))
  let F : Stacks T A := {S with R := fun i => if i ∈ rs then binSyms W 0 else S.R i}
  refine ⟨v',F,hu,?_,?_,rfl,rfl,rfl,?_⟩
  · simpa only [initializeScalarBank,rs,List.length_map,List.length_finRange] using he
  · intro r
    cases r with
    | v i => simp [F,rs,List.mem_map,hrg.eq_iff,tblRho]
    | wr => simpa [F,hwr,tblRho] using hwidth
    | wn => simpa [F,rs,List.mem_map,hrg.eq_iff,tblRho] using hblank .wn (by simp)
    | acc => simpa [F,rs,List.mem_map,hrg.eq_iff,tblRho] using hblank .acc (by simp)
    | z i => simpa [F,rs,List.mem_map,hrg.eq_iff,tblRho] using hblank (.z i) (by simp)
  · intro i hoff
    have hi : i ∉ rs := by
      intro hi
      obtain ⟨j,hj,he⟩ := List.mem_map.mp hi
      exact hoff (.v j) he
    simp [F,hi]

def installScalarInputs (rg : TblR n → Fin T) (src : Fin T) (indices : List (Fin n)) : Pr P T Q A U :=
  .seq (initializeScalarBank rg) (loadBinaryHeaders rg src indices)

/-- Allocate a fresh table and consume its actual parameter-word packet.
The packet suffix and every other non-table stack are preserved. -/
theorem installScalarInputs_exec (rg : TblR n → Fin T) (hrg : Function.Injective rg)
    (src : Fin T) (hsep : ∀ r, rg r ≠ src) (rs : List (Fin n × ℕ))
    (W : ℕ) (wl : List (Fin (A+4))) (hwl : wl.length = W)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ r : TblR n, r ≠ .wr → S.R (rg r) = [])
    (hsrc : S.R src = rs.flatMap (fun r => binSyms W r.2)++tail) :
    ∃ v' F, v'.user = v.user ∧
      Exec body (installScalarInputs rg src (rs.map Prod.fst)) (mk v S)
        (n*(4*W+4)+rs.length*(8*W+8)+2) (mk v' F) ∧
      tblHolds rg F (tblRho W wl [] (loadedBinaryState rs ⟨fun _ => 0,[]⟩)) ∧
      F.R src = tail ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → (∀ r, rg r ≠ i) → F.R i = S.R i := by
  obtain ⟨v₁,S₁,hu₁,he₁,hh₁,hi₁,ho₁,hL₁,hf₁⟩ :=
    initializeScalarBank_exec (body := body) rg hrg W wl hwl v S hwidth hblank
  obtain ⟨v₂,S₂,hu₂,he₂,hh₂,hs₂,hi₂,ho₂,hL₂,hf₂⟩ := loadBinaryHeaders_exec (body := body)
    hrg src hsep rs W wl [] hwl _ tail v₁ S₁ hh₁ ((hf₁ src hsep).trans hsrc)
  refine ⟨v₂,S₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast (by omega) rfl,hh₂,hs₂,
    hi₂.trans hi₁,ho₂.trans ho₁,hL₂.trans hL₁,?_⟩
  intro i his hoff
  exact (hf₂ i his hoff).trans (hf₁ i hoff)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
