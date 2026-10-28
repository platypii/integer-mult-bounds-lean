module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundHeaderBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRoundScalarRelease

/-! A closed binary-to-header stage restores its scalar input bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def generatedRoundHeaders (rg : TblR 8 → Fin T) (ports : Fin 4 → Fin T) : Pr P T Q A U :=
  .seq (installRoundHeaders rg ports) (tblCompile rg tblRoundRelease)

theorem generatedRoundHeaders_exec (rg : TblR 8 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports) (hsep : ∀ i r, rg r ≠ ports i)
    {W w q p j E : ℕ} (wl : List (Fin (A+4))) (hwl : wl.length = W)
    (st : TblSt 8 A) (h0 : st.val 0 = w) (h1 : st.val 1 = q) (h2 : st.val 2 = p)
    (h3 : st.val 3 = j) (h4 : st.val 4 = E)
    (h5 : st.val 5 = 0) (h6 : st.val 6 = 0) (h7 : st.val 7 = 0)
    (hp : p ≤ q) (hsize : q-p+j+(p+E+5) ≤ w) (hroom : w < 2^W)
    (hfit : ∀ i, st.val i < 2^W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl [] st)) :
    ∃ v' S' n, v'.user = v.user ∧ n ≤ 13*tblC W 0+12*w+44*W+25 ∧
      Exec body (generatedRoundHeaders rg ports) (mk v S) n (mk v' S') ∧
      tblHolds rg S' (tblRho W wl [] st) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i, S'.R (ports i) = List.replicate (roundHeaderValues w q p j E i) Node.tick++S.R (ports i)) ∧
      ∀ k, (∀ r, rg r ≠ k) → (∀ i, ports i ≠ k) → S'.R k = S.R k := by
  obtain ⟨v₁,S₁,n₁,z,hu₁,hn₁,he₁,hh₁,hkeep,hacc,hfitZ,hinp,hout,hL,hheaders,hframe⟩ :=
    installRoundHeaders_exec (body := body) rg hrg ports hports hsep wl hwl st
      h0 h1 h2 h3 h4 hp hsize hroom hfit v S hS
  have hc := tblRoundRelease_do (W := W) (e := 0) st z hkeep h5 h6 h7 hacc
  obtain ⟨out,heq,hrun⟩ := hc.host (body := body) hrg wl [] hwl rfl (Nat.zero_le W) hfitZ
  subst out
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hh₂,hframe₂⟩ := hrun v₁ S₁ hh₁
  simp only [List.length_nil] at hn₂
  rw [roundHeaderCost_eq W w q p j E ports hsize] at hn₁
  refine ⟨v₂,S₂,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,hh₂,
    hframe₂.1.trans hinp,hframe₂.2.1.trans hout,hframe₂.2.2.1.trans hL,?_,?_⟩
  · intro i
    rw [hframe₂.2.2.2 (ports i) (hsep i)]
    exact hheaders i
  · intro k hr hp
    exact (hframe₂.2.2.2 k hr).trans (hframe k hr hp)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
