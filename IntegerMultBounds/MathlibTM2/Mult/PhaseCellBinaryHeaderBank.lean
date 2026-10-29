module

public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Structural conversion of a retained unary header bank to binary metadata.
Sources and scratch are restored; each header is charged once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def binaryHeaderBank (width tmp scratch carry : Fin T) : List (Fin T × Fin T) → Pr P T Q A U
  | [] => .act .done
  | (src,dst)::rs => .seq (toBinary src width dst tmp scratch carry)
      (binaryHeaderBank width tmp scratch carry rs)

def binaryHeaderBankR (V : ℕ) (value : Fin T → ℕ)
    (R : Fin T → List (Fin (A+4))) : List (Fin T × Fin T) → Fin T → List (Fin (A+4))
  | [] => R
  | (src,dst)::rs => binaryHeaderBankR V value (Function.update R dst (binSyms V (value src))) rs

def binaryHeaderBankCost (V : ℕ) (value : Fin T → ℕ) (rs : List (Fin T × Fin T)) : ℕ :=
  (rs.map (fun p => value p.1*(4*V+10)+4*V+8)).sum+1

theorem binaryHeaderBankR_off (V : ℕ) (value : Fin T → ℕ) (R : Fin T → List (Fin (A+4)))
    (rs : List (Fin T × Fin T)) (k : Fin T) (hk : ∀ p ∈ rs, k ≠ p.2) :
    binaryHeaderBankR V value R rs k = R k := by
  induction rs generalizing R with
  | nil => rfl
  | cons p rs ih =>
    rw [binaryHeaderBankR,ih _ (fun q hq => hk q (by simp [hq]))]
    exact Function.update_of_ne (hk p (by simp)) _ _

theorem binaryHeaderBankR_at (V : ℕ) (value : Fin T → ℕ) (R : Fin T → List (Fin (A+4)))
    (rs : List (Fin T × Fin T)) (hnd : (rs.map Prod.snd).Nodup)
    (p : Fin T × Fin T) (hp : p ∈ rs) :
    binaryHeaderBankR V value R rs p.2 = binSyms V (value p.1) := by
  induction rs generalizing R with
  | nil => simp at hp
  | cons q rs ih =>
    have hn := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hp with he | ht
    · subst p
      rw [binaryHeaderBankR,binaryHeaderBankR_off]
      · simp
      · intro p hp he
        exact hn.1 (List.mem_map.mpr ⟨p,hp,he.symm⟩)
    · exact ih _ hn.2 ht

theorem binaryHeaderBank_exec (width tmp scratch carry : Fin T)
    (rs : List (Fin T × Fin T)) (hnd : (rs.map Prod.snd).Nodup)
    (hreg : ∀ p ∈ rs, [p.1,width,p.2,tmp,scratch].Nodup)
    (hsource : ∀ p ∈ rs, ∀ q ∈ rs, p.2 ≠ q.1)
    (V : ℕ) (value : Fin T → ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hV : (S.R width).length = V) (hvalue : ∀ p ∈ rs, (S.R p.1).length = value p.1)
    (hblank : ∀ p ∈ rs, S.R p.2 = []) (htmp : S.R tmp = []) (hscratch : S.R scratch = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ binaryHeaderBankCost V value rs ∧
      Exec body (binaryHeaderBank width tmp scratch carry rs) (mk v S) n
        (mk v' {S with R := binaryHeaderBankR V value S.R rs}) := by
  induction rs generalizing v S with
  | nil => exact ⟨v,1,rfl,le_rfl,Exec.act (body := body) .done (mk v S)⟩
  | cons p rs ih =>
    have hr := hreg p (by simp)
    have hr' := hr
    rcases p with ⟨src,dst⟩
    dsimp only [Prod.fst,Prod.snd] at hr hr'
    regs_ne hr'
    have hn := List.nodup_cons.mp hnd
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toBinary_exec (body := body) hr carry v S
      (hblank (src,dst) (by simp)) htmp hscratch
    let B : Stacks T A := {S with R := Function.update S.R dst (binSyms V (value src))}
    have hs : (S.R src).length = value src := hvalue (src,dst) (by simp)
    have he₁' : Exec body (toBinary src width dst tmp scratch carry) (mk v S) n₁ (mk v₁ B) := by
      simpa only [hV,hs] using he₁
    have hb (k : Fin T) (hk : k ≠ dst) : B.R k = S.R k := Function.update_of_ne hk _ _
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ih hn.2
      (fun q hq => hreg q (by simp [hq]))
      (fun q hq r hr => hsource q (by simp [hq]) r (by simp [hr])) v₁ B
      (by rw [hb width ‹width ≠ dst›]; exact hV)
      (by intro q hq; rw [hb q.1 (hsource (src,dst) (by simp) q (by simp [hq])).symm]; exact hvalue q (by simp [hq]))
      (by intro q hq
          have hne : q.2 ≠ dst := by
            intro he
            exact hn.1 (List.mem_map.mpr ⟨q,hq,he⟩)
          rw [hb q.2 hne]; exact hblank q (by simp [hq]))
      (by rw [hb tmp ‹dst ≠ tmp›.symm]; exact htmp)
      (by rw [hb scratch ‹dst ≠ scratch›.symm]; exact hscratch)
    refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,Exec.seq he₁' he₂⟩
    simp only [binaryHeaderBankCost,List.map_cons,List.sum_cons] at hn₂ ⊢
    rw [hV,hs] at hn₁
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
