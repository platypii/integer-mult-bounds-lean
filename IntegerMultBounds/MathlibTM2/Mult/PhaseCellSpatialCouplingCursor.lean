module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTransferCountedLine

/-! Advance and restore a cyclic coupling cursor without absolute-index seeks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 144 Q A U}

def advanceSpatialCouplingCursor : Pr P 144 Q A U := transfer 94 141 142 105

def restoreSpatialCouplingCursorFrom (count : Fin 144) : Pr P 144 Q A U :=
  transferCountedLine count 94 142 141 109 104 105

def restoreSpatialCouplingCursor : Pr P 144 Q A U := restoreSpatialCouplingCursorFrom 107

/-- Advancing the cursor depends only on its next word and remaining suffix. -/
theorem advanceSpatialCouplingCursor_cons_exec (x : GaussianInt) (xs : List GaussianInt)
    (w : ℕ) (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hw : (S.R 94).length = w) (h105 : S.R 105 = [])
    (hsource : S.R 141 = cstream A w (x::xs)++tail) :
    ∃ v', v'.user = v.user ∧
      Exec body advanceSpatialCouplingCursor (mk v S) (4*w+4)
        (mk v' {S with R := (Function.update (Function.update S.R
          141 (cstream A w xs++tail)) 142 ((csyms A w x).reverse++S.R 142))}) := by
  obtain ⟨v',hu,he⟩ := transfer_exec (body := body) (count := 94) (src := 141) (dst := 142)
    (tmp := 105) (by decide) v S (csyms A w x) (cstream A w xs++tail)
    (by simpa only [cstream_cons,List.append_assoc] using hsource) (by simpa using hw) h105
  exact ⟨v',hu,by simpa [advanceSpatialCouplingCursor] using he⟩

theorem advanceSpatialCouplingCursor_list_exec (xs : List GaussianInt) (j w : ℕ)
    (hj : j < xs.length) (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hw : (S.R 94).length = w) (h105 : S.R 105 = [])
    (hsource : S.R 141 = cstream A w (xs.drop j)++tail) :
    ∃ v', v'.user = v.user ∧
      Exec body advanceSpatialCouplingCursor (mk v S) (4*w+4)
        (mk v' {S with R := (Function.update (Function.update S.R
          141 (cstream A w (xs.drop (j+1))++tail)) 142 ((csyms A w xs[j]).reverse++S.R 142))}) := by
  apply advanceSpatialCouplingCursor_cons_exec (body := body) xs[j] (xs.drop (j+1)) w tail v S hw h105
  simpa only [List.drop_eq_getElem_cons hj] using hsource

theorem advanceSpatialCouplingCursor_exec {s : ℕ} [NeZero s]
    (F : ZMod s → GaussianInt) (band i w : ℕ) (hi : i < s)
    (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hw : (S.R 94).length = w) (h105 : S.R 105 = [])
    (hsource : S.R 141 = cstream A w ((cyclicPaddedLine F band).drop i)++tail) :
    ∃ v', v'.user = v.user ∧
      Exec body advanceSpatialCouplingCursor (mk v S) (4*w+4)
        (mk v' {S with R := (Function.update (Function.update S.R
          141 (cstream A w ((cyclicPaddedLine F band).drop (i+1))++tail))
            142 ((csyms A w (F ((i : ZMod s)-(band : ZMod s)))).reverse++S.R 142))}) := by
  have hip : i < (cyclicPaddedLine F band).length := by simp only [cyclicPaddedLine,List.length_map,List.length_range]; omega
  have hhead : (cyclicPaddedLine F band)[i]'hip = F ((i : ZMod s)-(band : ZMod s)) := by
    simp [cyclicPaddedLine]
  apply advanceSpatialCouplingCursor_cons_exec (body := body)
    (F ((i : ZMod s)-(band : ZMod s))) ((cyclicPaddedLine F band).drop (i+1)) w tail v S hw h105
  rw [hsource,List.drop_eq_getElem_cons hip,hhead]

theorem restoreSpatialCouplingCursorFrom_exec (count : Fin 144) (hreg : [count,94,142,141,109,104,105].Nodup) (rows w : ℕ)
    (visited savedTail : List (Fin (A+4))) (hlen : visited.length = rows*w)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hrows : (S.R count).length = rows) (hw : (S.R 94).length = w)
    (hsaved : S.R 142 = visited.reverse++savedTail)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ transferCountedLineCost rows w ∧
      Exec body (restoreSpatialCouplingCursorFrom count) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 142 savedTail) 141 (visited++S.R 141))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := transferCountedLine_exec (body := body)
    count 94 142 141 109 104 105 hreg rows w visited.reverse savedTail
    (by simpa only [List.length_reverse] using hlen) v S hrows hw hsaved h109 h104 h105
  exact ⟨v',n,hu,hn,by simpa only [restoreSpatialCouplingCursorFrom,List.reverse_reverse] using he⟩

theorem restoreSpatialCouplingCursor_exec (rows w : ℕ)
    (visited savedTail : List (Fin (A+4))) (hlen : visited.length = rows*w)
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hrows : (S.R 107).length = rows) (hw : (S.R 94).length = w)
    (hsaved : S.R 142 = visited.reverse++savedTail)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ transferCountedLineCost rows w ∧
      Exec body restoreSpatialCouplingCursor (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 142 savedTail) 141 (visited++S.R 141))}) := by
  exact restoreSpatialCouplingCursorFrom_exec (body := body) 107 (by decide) rows w
    visited savedTail hlen v S hrows hw hsaved h109 h104 h105

/-- Restore a bounded ribbon using the number of consumed rows, independent of ambient origin. -/
theorem restoreSpatialCouplingCursorFrom_list_exec (count : Fin 144)
    (hreg : [count,94,142,141,109,104,105].Nodup)
    (xs : List GaussianInt) (rows w : ℕ) (hlen : rows ≤ xs.length)
    (tail savedTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hcount : (S.R count).length = rows) (hw : (S.R 94).length = w)
    (hsource : S.R 141 = cstream A w (xs.drop rows)++tail)
    (hsaved : S.R 142 = (cstream A w (xs.take rows)).reverse++savedTail)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ transferCountedLineCost rows w ∧
      Exec body (restoreSpatialCouplingCursorFrom count) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 142 savedTail)
          141 (cstream A w xs++tail))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := restoreSpatialCouplingCursorFrom_exec (body := body) count hreg rows w
    (cstream A w (xs.take rows)) savedTail (by simp [List.length_take,Nat.min_eq_left hlen])
    v S hcount hw hsaved h109 h104 h105
  refine ⟨v',n,hu,hn,he.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [hsource,← List.append_assoc,← cstream_append,List.take_append_drop]

theorem restoreSpatialCouplingCursor_at {s : ℕ} [NeZero s]
    (F : ZMod s → GaussianInt) (band rows w : ℕ) (hrows : rows ≤ s)
    (tail savedTail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hcount : (S.R 107).length = rows) (hw : (S.R 94).length = w)
    (hsource : S.R 141 = cstream A w ((cyclicPaddedLine F band).drop rows)++tail)
    (hsaved : S.R 142 = (cstream A w ((cyclicPaddedLine F band).take rows)).reverse++savedTail)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ transferCountedLineCost rows w ∧
      Exec body restoreSpatialCouplingCursor (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 142 savedTail)
          141 (cstream A w (cyclicPaddedLine F band)++tail))}) := by
  have hlen : (cstream A w ((cyclicPaddedLine F band).take rows)).length = rows*w := by
    rw [length_cstream,List.length_take]
    have hfull : rows ≤ (cyclicPaddedLine F band).length := by
      simp only [cyclicPaddedLine,List.length_map,List.length_range]; omega
    rw [Nat.min_eq_left hfull]
  obtain ⟨v',n,hu,hn,he⟩ := restoreSpatialCouplingCursor_exec (body := body) rows w
    (cstream A w ((cyclicPaddedLine F band).take rows)) savedTail hlen v S hcount hw hsaved h109 h104 h105
  refine ⟨v',n,hu,hn,he.cast rfl ?_⟩
  apply congrArg (mk v')
  rw [hsource,← List.append_assoc,← cstream_append,List.take_append_drop]

def spatialCouplingInputsStep : Pr P 144 Q A U :=
  .seq copySpatialCouplingInputs advanceSpatialCouplingCursor

theorem spatialCouplingInputsStep_exec {s : ℕ} [NeZero s] (boundary : Bool)
    (t band a b i w : ℕ) (hi : i < s) (C : ZMod s → GaussianInt)
    (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hrows : (S.R 102).length = 2*band+1) (hw : (S.R 94).length = w)
    (h109 : S.R 109 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = []) :
    let T := if boundary then PhaseCellDiscreteGeometry.haloBoundary s t band a b else
      PhaseCellDiscreteGeometry.haloInterior s t band a b
    let F := fun j : ZMod s => if j ∈ T then C j else 0
    let source := cyclicPaddedLine F band
    S.R 141 = cstream A w (source.drop i)++tail →
    ∃ v' n, v'.user = v.user ∧ n ≤ copyCountedLineCost (2*band+1) w+(4*w+4) ∧
      Exec body spatialCouplingInputsStep (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          110 (cstream A w (spatialCouplingInputWords boundary t band a b i C)++S.R 110))
            141 (cstream A w (source.drop (i+1))++tail))
              142 ((csyms A w (F ((i : ZMod s)-(band : ZMod s)))).reverse++S.R 142))}) := by
  dsimp only
  intro hsource
  let T := if boundary then PhaseCellDiscreteGeometry.haloBoundary s t band a b else
    PhaseCellDiscreteGeometry.haloInterior s t band a b
  let F := fun j : ZMod s => if j ∈ T then C j else 0
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := copySpatialCouplingInputs_exec (body := body)
    boundary t band a b i w hi C tail v S hrows hw h109 h104 h105 hsource
  let S₁ : Stacks 144 A := {S with R := (Function.update S.R 110
    (cstream A w (spatialCouplingInputWords boundary t band a b i C)++S.R 110))}
  obtain ⟨v₂,hu₂,he₂⟩ := advanceSpatialCouplingCursor_exec (body := body) F band i w hi tail v₁ S₁
    (by simpa [S₁] using hw) (by simpa [S₁] using h105) (by simpa [S₁] using hsource)
  exact ⟨v₂,n₁+(4*w+4),hu₂.trans hu₁,Nat.add_le_add_right hn₁ _,Exec.seq he₁ he₂⟩

theorem spatialCouplingCursor_volume {s : ℕ} [NeZero s]
    (F : ZMod s → GaussianInt) (band rows w : ℕ)
    (tail savedTail : List (Fin (A+4))) (S : Stacks 144 A)
    (hsource : S.R 141 = cstream A w ((cyclicPaddedLine F band).drop rows)++tail)
    (hsaved : S.R 142 = (cstream A w ((cyclicPaddedLine F band).take rows)).reverse++savedTail) :
    (S.R 141).length+(S.R 142).length = (s+2*band)*w+tail.length+savedTail.length := by
  have hlen := congrArg List.length (List.take_append_drop rows (cyclicPaddedLine F band))
  have hfull : (cyclicPaddedLine F band).length = s+2*band := by
    simp only [cyclicPaddedLine,List.length_map,List.length_range]
  simp only [List.length_append,hfull] at hlen
  have hsize := congrArg (fun n => n*w) hlen
  rw [hsource,hsaved]
  simp only [List.length_append,List.length_reverse,length_cstream]
  nlinarith only [hsize]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
