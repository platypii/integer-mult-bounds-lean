module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloLengthCandidatesLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectSixPositiveLengths
public import IntegerMultBounds.NLogN.PhaseCellHaloLengthKeys

/-! Generate positive distinct halo keys using retained widths. The table is
released and all headers survive; no width is regenerated. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def haloPositiveLengthPackets (A V s t band a b : ℕ) : List (Fin (A+4)) :=
  (haloLengthKeys s t band a b).flatMap (binSyms V)

@[simp] theorem haloPositiveLengthPackets_length (A V s t band a b : ℕ) :
    (haloPositiveLengthPackets A V s t band a b).length = (haloLengthKeys s t band a b).length*V := by
  simp [haloPositiveLengthPackets, List.length_flatMap, binSyms]

def retainedHaloLengthKeys : Pr P₀ 117 Q A U :=
  .seq preparedHaloLengthCandidates selectSixPositiveLengths

def retainedHaloLengthKeysCost (s t band a b V : ℕ) :=
  preparedHaloLengthCandidatesCost s t band a b V+(43*tblC V V+262*V+291)

theorem retainedHaloLengthKeys_exec (P q w s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s)
    (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b)
    (hV : (S.R 115).length = weightWorkspaceWidth P q w t u)
    (hfresh : ∀ k ∈ [(104 : Fin 117),106,86], S.R k = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retainedHaloLengthKeysCost s t band a b (weightWorkspaceWidth P q w t u) ∧
      Exec body retainedHaloLengthKeys (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 87
          (haloPositiveLengthPackets A (weightWorkspaceWidth P q w t u) s t band a b++S.R 87))
          86 (List.replicate (haloLengthKeys s t band a b).length tick))}) := by
  let V := weightWorkspaceWidth P q w t u
  obtain ⟨v₃,S₃,n₃,hu₃,hn₃,he₃,hi₃,ho₃,hl₃,hr₃⟩ := preparedHaloLengthCandidates_exec (body := body)
    P q w s t u band a b hP hs hst hu hband has hbs hA v S
    hsSrc htSrc hbSrc haSrc hbEndSrc hV (hfresh 106 (by simp)) hblank
  have hS₃ : S₃ = {S with R := (Function.update S.R 87
      (haloLengthCandidatePackets A V s t band a b++S.R 87))} := Stacks.ext hi₃ ho₃ hl₃ hr₃
  subst S₃
  let S₃ : Stacks 117 A := {S with R := (Function.update S.R 87
    (haloLengthCandidatePackets A V s t band a b++S.R 87))}
  obtain ⟨hwide, _⟩ := weightWorkspaceWidth_control (q := q) (w := w) hP hs hst hu hband
  have hfit : ∀ L ∈ haloLengthCandidates s t band a b, L < 2^V := by
    intro L hL
    exact ((haloLengthCandidates_uniform hst band a b hL).trans ((Nat.sub_le _ _).trans (Nat.add_le_add_right (Nat.div_le_self _ _) 1))).trans_lt (by nlinarith only [hwide, hst])
  obtain ⟨v₄, S₄, n₄, hu₄, hn₄, he₄, hi₄, ho₄, hl₄, hr₄⟩ := selectSixPositiveLengths_exec (body := body)
    V (naturalLength s t band 0) (naturalLength s t band (t-s))
    (s/(t-s)-2*band) ((s/(t-s)+1)-2*band)
    (haloLength s t band a b (naturalPhase s t (a+band)))
    (haloLength s t band a b (naturalPhase s t (b-band-1)))
    (by dsimp [V, weightWorkspaceWidth, coefficientWorkspaceWidth]; omega)
    (hfit _ (by simp [haloLengthCandidates,naturalLengthCandidates])) (hfit _ (by simp [haloLengthCandidates,naturalLengthCandidates]))
    (hfit _ (by simp [haloLengthCandidates,naturalLengthCandidates])) (hfit _ (by simp [haloLengthCandidates,naturalLengthCandidates]))
    (hfit _ (by simp [haloLengthCandidates])) (hfit _ (by simp [haloLengthCandidates])) hA (S.R 87) v₃ S₃
    (by simpa [S₃,V] using hV) (by simpa [S₃] using hfresh 106 (by simp))
    (by simpa [S₃] using hfresh 104 (by simp))
    (by simpa [S₃] using hfresh 86 (by simp)) (by
      intro k hk
      have h87 : k ≠ (87 : Fin 117) := by intro he; subst k; norm_num at hk
      have h94 : k ≠ (94 : Fin 117) := by intro he; subst k; norm_num at hk
      have h115 : k ≠ (115 : Fin 117) := by intro he; subst k; norm_num at hk
      simpa [S₃, h87, h94, h115] using hblank k hk)
    (by simp [S₃, haloLengthCandidatePackets, haloLengthCandidates, naturalLengthCandidates])
  have hS₄ : S₄ = {S with R := (Function.update (Function.update S.R 87
      (haloPositiveLengthPackets A V s t band a b++S.R 87))
      86 (List.replicate (haloLengthKeys s t band a b).length tick))} := by
    refine Stacks.ext hi₄ ho₄ hl₄ ?_
    simpa [S₃,haloPositiveLengthPackets,haloLengthKeys,haloLengthCandidates,naturalLengthCandidates,
      Function.update_idem] using hr₄
  refine ⟨v₄,n₃+n₄,hu₄.trans hu₃,Nat.add_le_add hn₃ hn₄,?_⟩
  exact (Exec.seq he₃ he₄).cast rfl (congrArg (mk v₄) hS₄)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
