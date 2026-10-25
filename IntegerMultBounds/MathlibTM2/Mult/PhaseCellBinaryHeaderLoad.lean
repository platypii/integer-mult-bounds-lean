module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! Load fixed-width numeric words from an owned packet prefix into a table.
The packet suffix and all registers outside the source/table bank are preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A n : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def loadBinaryHeader (rg : TblR n → Fin T) (src : Fin T) (i : Fin n) : Pr P T Q A U :=
  .seq (uclear (rg (.v i))) (takePrefix (rg .wr) src (rg (.v i)) (rg (.z 0)) (rg (.z 1)))

theorem loadBinaryHeader_exec {rg : TblR n → Fin T} (hrg : Function.Injective rg)
    (src : Fin T) (hsep : ∀ r, rg r ≠ src) (i : Fin n) (W value : ℕ)
    (wl nl : List (Fin (A+4))) (hwl : wl.length = W) (st : TblSt n A)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) (hsrc : S.R src = binSyms W value ++ tail) :
    ∃ v' S', v'.user = v.user ∧
      Exec body (loadBinaryHeader rg src i) (mk v S) (8*W+8) (mk v' S') ∧
      tblHolds rg S' (tblRho W wl nl ⟨Function.update st.val i value, st.acc⟩) ∧
      S'.R src = tail ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ src → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  have hreg : [rg .wr, src, rg (.v i), rg (.z 0), rg (.z 1)].Nodup := by
    simp [List.nodup_cons, hrg.eq_iff, hsep, (hsep (.v i)).symm, (hsep (.z 0)).symm, (hsep (.z 1)).symm]
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body (rg (.v i)) v S
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg (.v i)) [] }
  have hlen : (S.R (rg (.v i))).length = W := by rw [hS (.v i)]; simp [tblRho, binSyms]
  obtain ⟨v₂, hu₂, he₂⟩ := takePrefix_exec (body := body) hreg v₁ S₁ (binSyms W value) tail
    (by simpa [S₁, (hsep (.v i)).symm] using hsrc)
    (by simp [S₁, hrg.ne (by simp : (TblR.wr : TblR n) ≠ .v i), hS .wr, tblRho, binSyms, hwl])
    (by simp [S₁, hrg.ne (by simp : (TblR.z 0 : TblR n) ≠ .v i), hS (.z 0), tblRho])
    (by simp [S₁, hrg.ne (by simp : (TblR.z 1 : TblR n) ≠ .v i), hS (.z 1), tblRho])
  let S₂ : Stacks T A := { S₁ with R := (Function.update (Function.update S₁.R src tail)
    (rg (.v i)) (binSyms W value)) }
  have he₂' : Exec body (takePrefix (rg .wr) src (rg (.v i)) (rg (.z 0)) (rg (.z 1)))
      (mk v₁ S₁) (6*W+6) (mk v₂ S₂) := by simpa [S₂, S₁, binSyms] using he₂
  refine ⟨v₂, S₂, hu₂.trans hu₁, (Exec.seq he₁ he₂').cast (by rw [hlen]; ring) rfl, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · intro r
    by_cases hr : r = .v i
    · subst r; simp [S₂, S₁, tblRho]
    have hn := hrg.ne hr
    cases r with
    | v j =>
      have hj : j ≠ i := by intro he; apply hr; simp [he]
      simpa [S₂, S₁, hsep (.v j), hn, tblRho, hj] using hS (.v j)
    | wr => simpa [S₂, S₁, hsep .wr, hn, tblRho] using hS .wr
    | wn => simpa [S₂, S₁, hsep .wn, hn, tblRho] using hS .wn
    | acc => simpa [S₂, S₁, hsep .acc, hn, tblRho] using hS .acc
    | z j => simpa [S₂, S₁, hsep (.z j), hn, tblRho] using hS (.z j)
  · simp [S₂, S₁, (hsep (.v i)).symm]
  · intro k hks hk
    simp [S₂, S₁, hks, (hk (.v i)).symm]

def loadBinaryHeaders (rg : TblR n → Fin T) (src : Fin T) : List (Fin n) → Pr P T Q A U
  | [] => .act .done
  | i::is => .seq (loadBinaryHeader rg src i) (loadBinaryHeaders rg src is)

def loadedBinaryState : List (Fin n × ℕ) → TblSt n A → TblSt n A
  | [], st => st
  | (i, value)::rs, st => loadedBinaryState rs ⟨Function.update st.val i value, st.acc⟩

theorem loadBinaryHeaders_exec {rg : TblR n → Fin T} (hrg : Function.Injective rg)
    (src : Fin T) (hsep : ∀ r, rg r ≠ src) (rs : List (Fin n × ℕ)) (W : ℕ)
    (wl nl : List (Fin (A+4))) (hwl : wl.length = W) (st : TblSt n A)
    (suffix : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st))
    (hsrc : S.R src = rs.flatMap (fun r => binSyms W r.2) ++ suffix) :
    ∃ v' S', v'.user = v.user ∧
      Exec body (loadBinaryHeaders rg src (rs.map Prod.fst)) (mk v S)
        (rs.length*(8*W+8)+1) (mk v' S') ∧
      tblHolds rg S' (tblRho W wl nl (loadedBinaryState rs st)) ∧
      S'.R src = suffix ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ src → (∀ r, rg r ≠ k) → S'.R k = S.R k := by
  induction rs generalizing st v S with
  | nil =>
    refine ⟨v, S, rfl, ?_, hS, by simpa using hsrc, rfl, rfl, rfl, fun _ _ _ => rfl⟩
    simpa [loadBinaryHeaders, Action.run] using Exec.act (body := body) .done (mk v S)
  | cons r rs ih =>
    obtain ⟨v₁, S₁, hu₁, he₁, hh₁, hs₁, hi₁, ho₁, hl₁, hf₁⟩ := loadBinaryHeader_exec (body := body)
      hrg src hsep r.1 W r.2 wl nl hwl st (rs.flatMap (fun r => binSyms W r.2) ++ suffix) v S hS
      (by simpa [List.append_assoc] using hsrc)
    obtain ⟨v₂, S₂, hu₂, he₂, hh₂, hs₂, hi₂, ho₂, hl₂, hf₂⟩ := ih _ v₁ S₁ hh₁ hs₁
    refine ⟨v₂, S₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by simp; ring) rfl, hh₂, hs₂,
      hi₂.trans hi₁, ho₂.trans ho₁, hl₂.trans hl₁, ?_⟩
    intro k hks hk
    exact (hf₂ k hks hk).trans (hf₁ k hks hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
