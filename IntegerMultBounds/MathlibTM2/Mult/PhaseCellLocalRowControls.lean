module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedOriginControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRowCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLocalRowSelection

/-! Instantiate the shared enumeration lifecycle on actual nearest-row offsets.
No binary origin queue or unary gather controls are supplied ready. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellRationalArgs
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def localRowControls (A s t a n origin w : ℕ) :=
  match localRowOrigins s t a n origin w with
  | [] => []
  | p::ps => gatherControls A (p::windowAdvances p ps)

theorem localRowControls_eq (A s t a n origin w : ℕ) (hn : 0 < n) :
    gatherControls A (originAdvances w 0 (localRowOrigins s t a n origin 1)++[0]) =
      localRowControls A s t a n origin w := by
  have hmap : (localRowOrigins s t a n origin 1).map (·*w) = localRowOrigins s t a n origin w := by
    simp [localRowOrigins,List.map_map]
  rw [originAdvances_symbols,Nat.zero_mul,hmap]
  have hlen : (localRowOrigins s t a n origin w).length = n := by simp [localRowOrigins]
  cases he : localRowOrigins s t a n origin w with
  | nil => simp [he] at hlen; omega
  | cons p ps => simp [localRowControls,he,originAdvances,originAdvances_window]

def generatedLocalRowControls : Pr P 117 Q A U := generatedOriginControls localRowOriginsCode

def localRowControlsCost (W V span w n : ℕ) :=
  (11*n+3)*tblC W V+n*(8*V+6)+6+(62*W+63)+preparedOriginAdvanceCost V span w n

theorem generatedLocalRowControls_exec {W V s t a origin span w n : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (ha : st.val 2 = a)
    (ho : st.val 3 = origin) (hz : st.val 12 = 0) (hn : st.val 15 = n)
    (hspos : 0 < s) (hnpos : 0 < n) (hcount : n < 2^W)
    (hwide : a+n+2*t*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, origin ≤ nearestNatural s t (a+j) ∧ nearestNatural s t (a+j) < origin+span)
    (hwV : w < 2^V) (hspan : span < 2^V) (hvol : span*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate V tick) st))
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w)
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90], S.R k = []) :
    ∃ v' F m, v'.user = v.user ∧ m ≤ localRowControlsCost W V span w n ∧
      Exec body generatedLocalRowControls (mk v S) m (mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      F.R = fun k => if k.val < 31 then [] else
        if k = 91 then localRowControls A s t a n origin w++S.R 91 else
        if k = 109 then (localRowOrigins s t a n origin 1).flatMap (binSyms V)++S.R 109 else
        if k = 116 then List.replicate n tick else S.R k := by
  let xs := localRowOrigins s t a n origin 1
  have hle : ∀ x ∈ xs, x ≤ span := by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    have hh := hwindow j (List.mem_range.mp hj)
    simp only [Nat.mul_one]
    omega
  have hc := localRowOriginsCode_do (w := V) st hs ht ha ho hz hn hspos hcount
    (fun j hj => (hwindow j hj).1) hwide
  have hc' : TblDo A W V localRowOriginsCode st (fun F =>
      F.acc = (xs.flatMap (fun x => tblPairs A V x 0)).reverse++st.acc) (11*n+3) := by
    simpa only [xs,localRowOrigins,List.flatMap_map,Nat.mul_one] using hc
  have hh := generatedOriginControls_exec (body := body) xs localRowOriginsCode st hc' hwV hspan hvol
    (localRowOrigins_ordered s t a n origin 1) hle hVW hA hVpos hbound hacc v S hS hV hw
    h104 h106 h116 hfresh
  dsimp only [xs] at hh
  rw [localRowControls_eq A s t a n origin w hnpos] at hh
  simpa only [localRowOrigins,List.length_map,List.length_range,generatedLocalRowControls,
    localRowControlsCost] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
