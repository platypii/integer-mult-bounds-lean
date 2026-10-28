module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRunEmissionWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeOriginHeaders

/-! Generate binary run metadata from retained ordinary scalar headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloRunHeaders : List (Fin 117 × Fin 16) :=
  [(97,0),(98,1),(100,2),(101,13),(103,14)]

def haloRunRawState (A s t band a b : ℕ) : TblSt 16 A :=
  ⟨Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ => 0) 0 s) 1 t) 2 band) 13 a) 14 b,[]⟩

def haloRunMetadata (flags : Bool) (A W s t band a b : ℕ) : List (Fin (A+4)) :=
  let xs := IntervalRunMask.runs 0 s (haloRunIntervals s t band a b)
  if flags then xs.map (fun r => bitSymbol r.1) else xs.flatMap (fun r => binSyms W r.2)

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def haloRunsFromHeaders (flags : Bool) (out : Fin 117) : Pr P 117 Q A U :=
  .seq (initializeOriginHeaders haloRunHeaders)
    (.seq (setHaloRunEmissionWidth flags) (haloRunReleasedController flags out))

def haloRunsFromHeadersCost (flags : Bool) (W s t band a b : ℕ) : ℕ :=
  let w := haloRunEmissionWidth flags W
  (104*W+137)+((s+t+band+a+b)*(4*W+10)+30*W+51)+setHaloRunEmissionWidthCost flags W+
    ((40*(t-s+1)+13)*tblC W w+2*((2*(haloRunIntervals s t band a b).length+1)*w)+62*W+65)

theorem haloRunsFromHeaders_exec (flags : Bool) (out : Fin 117) (hout : 31 ≤ out.val)
    {W s t band a b : ℕ} [NeZero s] (hst : s < t) (has : a ≤ s) (hbs : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (hWsrc : (S.R 115).length = W) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ haloRunsFromHeadersCost flags W s t band a b ∧
      Exec body (haloRunsFromHeaders flags out) (mk v S) m
        (mk v' {S with R := Function.update S.R out (haloRunMetadata flags A W s t band a b++S.R out)}) := by
  let st := haloRunRawState A s t band a b
  let value := fun r : Fin 117 => (S.R r).length
  let w := haloRunEmissionWidth flags W
  have hsep : ∀ r ∈ haloRunHeaders, ∀ x, originReg x ≠ r.1 := by
    intro r hr x he
    have hv : 31 ≤ r.1.val := by
      simp only [haloRunHeaders,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    have hx := originReg_range x
    have hh := congrArg Fin.val he
    omega
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh₁,hf₁⟩ := initializeOriginHeaders_exec (body := body)
    haloRunHeaders hsep W value v S (by intros; rfl) hWsrc h106 hblank
  have hstate : loadedOriginState value haloRunHeaders ⟨fun _ => 0,[]⟩ = st := by
    simp [loadedOriginState,haloRunHeaders,st,haloRunRawState,value,hs,ht,hband,ha,hb]
  rw [hstate] at hh₁
  have hoff (r : Fin 117) (hr : 31 ≤ r.val) : S₁.R r = S.R r :=
    hf₁.2.2.2 r (fun x he => by have hx := originReg_range x; have hv := congrArg Fin.val he; omega)
  obtain ⟨v₂,hu₂,he₂⟩ := setHaloRunEmissionWidth_exec (body := body) flags W v₁ S₁ (hh₁ .wn)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 17 (List.replicate w tick)}
  have hh₂ : tblHolds originReg S₂ (tblRho W (List.replicate W tick) (List.replicate w tick) st) := by
    intro r
    by_cases hr : r = .wn
    · subst r; simp [S₂,originReg,tblRho]
    have hne : originReg r ≠ (17 : Fin 117) := originReg_injective.ne hr
    have hh := hh₁ r
    cases r <;> simp_all [S₂,tblRho]
  have hW : 1 ≤ W := by
    by_contra hn
    have he : W = 0 := by omega
    rw [he] at hwide
    norm_num at hwide
  have hw : w ≤ W := by cases flags <;> simp_all [w,haloRunEmissionWidth]
  have hbound : ∀ r, st.val r < 2^W := by
    have htW : t < 2^W := by nlinarith only [hwide]
    intro r
    simp only [st,haloRunRawState,Function.update_apply]
    split_ifs <;> omega
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := haloRunReleasedController_exec (body := body)
    flags out hout st (by simp [st,haloRunRawState]) (by simp [st,haloRunRawState])
    (by simp [st,haloRunRawState]) (by simp [st,haloRunRawState])
    (by simp [st,haloRunRawState]) (by simp [st,haloRunRawState])
    has hbs (NeZero.pos s) hst hwide hw hbound rfl v₂ S₂ hh₂
  have hmetadata : ((runPairStream flags A w (IntervalRunMask.runs 0 s (haloRunIntervals s t band a b))).map
      (fun sym => bitSymbol (a := A) (pairRe sym))) = haloRunMetadata flags A W s t band a b := by
    cases flags with
    | true => exact runPairStream_flags_real_bits hA _
    | false =>
      apply runPairStream_counts_real_bits hA
      intro r hr
      change r.2 < 2^W
      have hsum := IntervalRunMask.sum_runs (haloRunIntervals_ordered s t band a b)
      have hle : r.2 ≤ ((IntervalRunMask.runs 0 s (haloRunIntervals s t band a b)).map Prod.snd).sum :=
        List.le_sum_of_mem (List.mem_map.mpr ⟨r,hr,rfl⟩)
      have hsW : s < 2^W := by nlinarith only [hwide,hst]
      simp only [Nat.sub_zero] at hsum
      omega
  have hcost : loadOriginListCost W value haloRunHeaders =
      (s+t+band+a+b)*(4*W+10)+30*W+51 := by
    simp [loadOriginListCost,haloRunHeaders,value,hs,ht,hband,ha,hb]
    ring
  rw [hcost] at hn₁
  refine ⟨v₃,n₁+(setHaloRunEmissionWidthCost flags W+n₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · dsimp only [haloRunsFromHeadersCost]
    dsimp only [w] at hn₃
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext hf₁.1 hf₁.2.1 hf₁.2.2.1 ?_
    funext r
    by_cases hr : r.val < 31
    · have hro : r ≠ out := by intro he; subst r; omega
      simp [hr,hro,hblank r hr]
    have hr17 : r ≠ (17 : Fin 117) := by intro he; subst r; norm_num at hr
    have hr31 : 31 ≤ r.val := by omega
    by_cases hro : r = out
    · subst r; simp [hr,S₂,hr17,hoff out hr31,hmetadata]
    · simp [hr,hro,S₂,hr17,hoff r hr31]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
