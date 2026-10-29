module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Complete interval geometry from binary ambient dimensions, cuts, origin and
row count. Derived fields are computed in binary without scanning ambient data. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def completeCouplingIntervalMetadata : Pr P 168 Q A U :=
  .seq (bzero 163 154 0) (.seq (bcopy 147 3 0 1)
    (.seq (badd 147 3 148 0 1 2 4) (.seq (uclear 3)
      (.seq (badd 155 165 156 0 1 2 4) (badd 156 148 164 0 1 2 4)))))

def completedCouplingIntervalR (R : Fin 168 → List (Fin (A+4))) (V band origin N : ℕ) :=
  Function.update (Function.update (Function.update (Function.update R
    154 (binSyms V 0)) 148 (binSyms V (2*band)))
    156 (binSyms V (origin+N))) 164 (binSyms V (origin+(N+2*band)))

theorem completeCouplingIntervalMetadata_exec {V s t band a b origin N : ℕ}
    (hfitV : origin+(N+2*band)+s < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A) (hV : (S.R 163).length = V)
    (hbase : ∀ k ∈ [(145 : Fin 168),146,147,149,151,155,165],
      S.R k = binSyms V (couplingIntervalValue s t band a b origin N k))
    (hblank : ∀ k ∈ [(0 : Fin 168),1,2,3,148,154,156,164], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body completeCouplingIntervalMetadata (mk v S) (36*V+36)
        (mk v' {S with R := completedCouplingIntervalR S.R V band origin N}) ∧
      CouplingIntervalMetadata V s t band a b origin N
        {S with R := completedCouplingIntervalR S.R V band origin N} := by
  have h147 : S.R 147 = binSyms V band := by simpa [couplingIntervalValue] using hbase 147 (by simp)
  have h155 : S.R 155 = binSyms V origin := by simpa [couplingIntervalValue] using hbase 155 (by simp)
  have h165 : S.R 165 = binSyms V N := by simpa [couplingIntervalValue] using hbase 165 (by simp)
  obtain ⟨v₁,hu₁,he₁⟩ := bzero_exec (body := body) (wR := 163) (c := 154) (t := 0)
    (by decide) v S (hblank 0 (by simp))
  let B : Stacks 168 A := {S with R := Function.update S.R 154 (binSyms V 0)}
  have he₁' : Exec body (bzero 163 154 0) (mk v S) (4*V+4) (mk v₁ B) := by
    simpa [B,hV,hblank 154 (by simp)] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := bcopy_exec (body := body) (a := 147) (c := 3) (t₁ := 0) (t₂ := 1)
    (by decide) v₁ B (by simpa [B] using hblank 0 (by simp)) (by simpa [B] using hblank 1 (by simp))
  let C : Stacks 168 A := {B with R := Function.update B.R 3 (binSyms V band)}
  have he₂' : Exec body (bcopy 147 3 0 1) (mk v₁ B) (6*V+6) (mk v₂ C) := by
    simpa [C,B,h147,hblank 3 (by simp)] using he₂
  obtain ⟨v₃,hu₃,_,_,he₃⟩ := badd_exec (body := body)
    (L := V) (x := band) (y := band) (a := 147) (b := 3) (c := 148) (tx := 0) (ty := 1) (tz := 2) (cy := 4)
    (by decide) (by decide) (by decide) (by omega) (by omega) v₂ C
    (by simpa [C,B] using h147) (by simp [C])
    (by simpa [C,B] using hblank 0 (by simp)) (by simpa [C,B] using hblank 1 (by simp))
    (by simpa [C,B] using hblank 2 (by simp))
  let D : Stacks 168 A := {C with R := Function.update C.R 148 (binSyms V (2*band))}
  have he₃' : Exec body (badd 147 3 148 0 1 2 4) (mk v₂ C) (8*V+8) (mk v₃ D) := by
    simpa [D,C,B,hblank 148 (by simp),show band+band = 2*band by omega,
      Nat.mod_eq_of_lt (show 2*band < 2^V by omega)] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 3 v₃ D
  let E : Stacks 168 A := {D with R := Function.update D.R 3 []}
  have he₄' : Exec body (uclear 3) (mk v₃ D) (2*V+2) (mk v₄ E) := by
    simpa [E,D,C] using he₄
  obtain ⟨v₅,hu₅,_,_,he₅⟩ := badd_exec (body := body)
    (L := V) (x := origin) (y := N) (a := 155) (b := 165) (c := 156) (tx := 0) (ty := 1) (tz := 2) (cy := 4)
    (by decide) (by decide) (by decide) (by omega) (by omega) v₄ E
    (by simpa [E,D,C,B] using h155) (by simpa [E,D,C,B] using h165)
    (by simpa [E,D,C,B] using hblank 0 (by simp)) (by simpa [E,D,C,B] using hblank 1 (by simp))
    (by simpa [E,D,C,B] using hblank 2 (by simp))
  let F : Stacks 168 A := {E with R := Function.update E.R 156 (binSyms V (origin+N))}
  have he₅' : Exec body (badd 155 165 156 0 1 2 4) (mk v₄ E) (8*V+8) (mk v₅ F) := by
    simpa [F,E,D,C,B,hblank 156 (by simp),Nat.mod_eq_of_lt (show origin+N < 2^V by omega)] using he₅
  obtain ⟨v₆,hu₆,_,_,he₆⟩ := badd_exec (body := body)
    (L := V) (x := origin+N) (y := 2*band) (a := 156) (b := 148) (c := 164) (tx := 0) (ty := 1) (tz := 2) (cy := 4)
    (by decide) (by decide) (by decide) (by omega) (by omega) v₅ F
    (by simp [F]) (by simp [F,E,D])
    (by simpa [F,E,D,C,B] using hblank 0 (by simp)) (by simpa [F,E,D,C,B] using hblank 1 (by simp))
    (by simpa [F,E,D,C,B] using hblank 2 (by simp))
  have hsum : origin+N+2*band = origin+(N+2*band) := by omega
  have he₆' : Exec body (badd 156 148 164 0 1 2 4) (mk v₅ F) (8*V+8)
      (mk v₆ {S with R := completedCouplingIntervalR S.R V band origin N}) := by
    refine he₆.cast rfl ?_
    apply congrArg (mk v₆)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h3 : k = 3 <;> by_cases h148 : k = 148 <;> by_cases h154 : k = 154 <;>
      by_cases h156 : k = 156 <;> by_cases h164 : k = 164 <;>
      simp [F,E,D,C,B,completedCouplingIntervalR,h3,h148,h154,h156,h164,
        hblank 3 (by simp),hblank 164 (by simp),hsum,
        Nat.mod_eq_of_lt (show origin+(N+2*band) < 2^V by omega)]
  refine ⟨v₆,hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))),
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅' he₆'))))).cast (by omega) rfl,?_⟩
  constructor
  · simpa [completedCouplingIntervalR] using hV
  · intro k hk
    simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
    | (simp [completedCouplingIntervalR,couplingIntervalValue]; done)
    | simpa [completedCouplingIntervalR] using hbase _ (by simp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
