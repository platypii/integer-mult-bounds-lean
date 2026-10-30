module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairBitPlanes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComponents
public import IntegerMultBounds.MathlibTM2.Host.Auto

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def realBitPair {A : ℕ} (x : Fin (A+4)) : Fin (A+4) := pairSym A (symBit x) false

def joinBitPlanes (count re im reRev imRev dst : Fin T) : Pr P T Q A U :=
  .seq (moveR re reRev realBitPair)
    (.seq (moveR im imRev realBitPair) (pairComponents count reRev imRev dst))

theorem pairComponentSymbol_bitPlanes (hA : 4 ≤ A) (xs ys : List Bool) :
    List.zipWith pairComponentSymbol (xs.map (fun b => pairSym A b false))
      (ys.map (fun b => pairSym A b false)) = List.zipWith (pairSym A) xs ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => cases ys <;> simp [pairComponentSymbol,pairRe_pairSym hA,ih]

/-- Reassemble routed bit planes in one counted pass after reversing each plane.
The two reversals cancel the pairing program's reverse output order. -/
theorem joinBitPlanes_exec (count re im reRev imRev dst : Fin T)
    (hreg : [count,re,im,reRev,imRev,dst].Nodup) (hA : 4 ≤ A)
    (xs ys : List Bool) (hlen : xs.length = ys.length)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : (S.R count).length = xs.length)
    (hre : S.R re = xs.map bitSymbol) (him : S.R im = ys.map bitSymbol)
    (hReRev : S.R reRev = []) (hImRev : S.R imRev = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 8*xs.length+6 ∧
      Exec body (joinBitPlanes count re im reRev imRev dst) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          re []) im []) dst (List.zipWith (pairSym A) xs ys++S.R dst)) count [])}) := by
  have hr := hreg
  regs_ne hr
  let pair := fun b => pairSym A b false
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body re reRev ‹re ≠ reRev› realBitPair v S
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R re []) reRev ((xs.map pair).reverse))}
  have he₁' : Exec body (moveR re reRev realBitPair) (mk v S) (2*xs.length+2) (mk v₁ M) := by
    simpa [M,movedR,hre,hReRev,realBitPair,Function.comp_def] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body im imRev ‹im ≠ imRev› realBitPair v₁ M
  let N : Stacks T A := {M with R := (Function.update (Function.update M.R im []) imRev ((ys.map pair).reverse))}
  have he₂' : Exec body (moveR im imRev realBitPair) (mk v₁ M) (2*ys.length+2) (mk v₂ N) := by
    simpa [N,M,movedR,him,hImRev,‹re ≠ im›.symm,‹im ≠ reRev›,‹re ≠ imRev›.symm,
      ‹reRev ≠ imRev›.symm,realBitPair,Function.comp_def] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := pairComponents_exec (body := body)
    (count := count) (x := reRev) (y := imRev) (dst := dst) (by regs_nodup)
    (xs.map pair).reverse (ys.map pair).reverse [] [] (by simp [hlen]) v₂ N
    (by simpa [N,M,‹count ≠ imRev›,‹count ≠ im›,‹count ≠ reRev›,‹count ≠ re›] using hc)
    (by simp [N,M,‹im ≠ reRev›.symm,‹reRev ≠ imRev›]) (by simp [N])
  have hzip : List.zipWith pairComponentSymbol (xs.map pair).reverse (ys.map pair).reverse =
      (List.zipWith (pairSym A) xs ys).reverse := by
    rw [←List.reverse_zipWith (by simp [hlen])]
    exact congrArg List.reverse (pairComponentSymbol_bitPlanes hA xs ys)
  simp only [List.length_reverse,List.length_map] at hn₃
  refine ⟨v₃,(2*xs.length+2)+((2*ys.length+2)+n₃),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  rw [hzip,List.reverse_reverse]
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hcount : i = count
  · subst i; simp
  by_cases hdst : i = dst
  · subst i; simp [N,M,‹imRev ≠ dst›.symm,‹im ≠ dst›.symm,‹reRev ≠ dst›.symm,‹re ≠ dst›.symm,hcount]
  by_cases hrev : i = reRev
  · subst i; simp [N,M,hcount,hdst,hReRev,‹reRev ≠ imRev›,‹im ≠ reRev›.symm,‹re ≠ reRev›.symm]
  by_cases himrev : i = imRev
  · subst i; simp [N,M,hcount,hdst,hrev,hImRev,‹im ≠ imRev›.symm,‹re ≠ imRev›.symm]
  · by_cases him' : i = im
    · subst i; simp [N,M,hcount,hdst,hrev,himrev]
    · simp [N,M,hcount,hdst,hrev,himrev,him']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
