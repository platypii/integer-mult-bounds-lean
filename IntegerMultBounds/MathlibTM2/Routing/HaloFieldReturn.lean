module

public import IntegerMultBounds.MathlibTM2.Routing.GaussianHaloColumns
public import IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturnColumns

/-! Emit a current fiber's persistent halos and return the enlarged local field
through its complete spectator block. Both stages are actual fixed programs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloFieldReturn
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  HaloIntervalLayout PaddedFieldLayout GaussianHaloColumns
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def run : Pr P 117 Q A U :=
  .seq GeneratedPeriodicHalo.emit
    (MixedRadixReturn.returnField 43 44 45 46 47 48 49 50 51 52 53 39 40 41 42 92 (pairSym A false false))

def returned (A w B L H N : ℕ) (cols : List (List GaussianInt)) : List (Fin (A+4)) :=
  (HaloRecordLayout.windows L H N cols).flatMap (fun window =>
    (realColumns B (0 : GaussianInt) window).flatMap (fun row => row.flatMap (csyms A w)))

theorem returned_length (A w B L H N : ℕ) (cols : List (List GaussianInt))
    (hlen : cols.length = N*L) (hH : H ≤ cols.length) :
    (returned A w B L H N cols).length = N*(B*((L+2*H)*w)) := by
  have hshape := HaloRecordLayout.windows_row_length L H N cols hlen hH
  have hrow (row : List GaussianInt) : (row.flatMap (csyms A w)).length = row.length*w :=
    length_cstream row
  have hwindow : ∀ window ∈ HaloRecordLayout.windows L H N cols,
      ((realColumns B (0 : GaussianInt) window).flatMap (fun row => row.flatMap (csyms A w))).length =
        B*((L+2*H)*w) := by
    intro window hw
    have hh := HaloRecordLayout.length_flatMap (fun row : List GaussianInt => row.flatMap (csyms A w))
      ((L+2*H)*w) (realColumns B (0 : GaussianInt) window) (by
        intro row hr
        rw [hrow,RectangularColumns.realColumns_row_length B (0 : GaussianInt) window row hr,hshape window hw])
    simpa only [RectangularColumns.realColumns_length] using hh
  simpa only [returned,HaloRecordLayout.windows_length] using
    HaloRecordLayout.length_flatMap (fun window =>
      (realColumns B (0 : GaussianInt) window).flatMap (fun row => row.flatMap (csyms A w)))
      (B*((L+2*H)*w)) (HaloRecordLayout.windows L H N cols) hwindow

theorem run_exec (w V B L H N k : ℕ) (cols : List (List GaussianInt))
    (hwpos : 0 < w) (hBpos : 0 < B) (hN : 0 < N) (hgap : 2*H ≤ L)
    (hlen : cols.length = N*L) (hB : ∀ col ∈ cols, col.length = B)
    (hfit : (N*L+2*H)*(B*w) < 2^V) (hwide : N+2 < 2^V) (hA : 4 ≤ A) (hcapacity : L+2*H ≤ 2^k)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hM : (S.R 31).length = cols.flatten.length) (hH : (S.R 32).length = H*B) (hw : (S.R 33).length = w)
    (hV : (S.R 115).length = V) (hNb : S.R 97 = binSyms V N)
    (hLb : S.R 98 = binSyms V (L*(B*w))) (hBb : S.R 100 = binSyms V (2*(H*(B*w)))) (hz : S.R 116 = [])
    (hk : (S.R 43).length = k) (hp : (S.R 44).length = N) (hb : (S.R 45).length = B)
    (hm : (S.R 46).length = L+2*H) (hr : (S.R 47).length = w)
    (hsrc : S.R 39 = cstream A w cols.flatten++tail)
    (hblank : ∀ i : Fin 117, i.val < 31 ∨ i ∈ [34,35,36,96,95,94,37,38,40,41,42,93,92,114,48,49,50,51,52,53] → S.R i = []) :
    let C := GeneratedPeriodicHalo.cost (N*L*B) (H*B) w N V (L*B)
    let W := N*(B*(2^k*w))
    ∃ vf n, vf.user = v.user ∧ n ≤ C+k*(64*W+3)+384*W+2 ∧
      Exec body run (mk v S) n (mk vf {S with R := Function.update S.R 39 (returned A w B L H N cols++tail)}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(3*C+1000*W)) depth run
        (mk v S) n (mk vf {S with R := Function.update S.R 39 (returned A w B L H N cols++tail)})) := by
  dsimp only
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := emit_columns_exec (body := body) w V B L H N cols
    hN hgap hlen hB hfit hwide hA tail v S hM hH hw hV hNb hLb hBb hz hsrc (by
      intro i hi
      rcases hi with hi | hi
      · exact hblank i (Or.inl hi)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact hblank _ (by simp))
  let F : Stacks 117 A := {S with R := (Function.update S.R 39
    ((HaloRecordLayout.windows L H N cols).flatMap (fun window => window.flatMap (cstream A w))++tail))}
  have hHfit : H ≤ cols.length := by
    have hh := Nat.le_mul_of_pos_left L hN
    omega
  have hshape := column_windows_shape B L H N cols hlen hHfit hB
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,hs₂⟩ := MixedRadixReturnColumns.returnColumns_exec (body := body)
    43 44 45 46 47 48 49 50 51 52 53 39 40 41 42 92 (by decide)
    (csyms A w) w B (L+2*H) k hwpos hBpos (by intro x; simp) (0 : GaussianInt)
    (pairSym A false false) (by simp [csyms,coeffSyms,red,List.ofFn_const]) (HaloRecordLayout.windows L H N cols)
    (by simpa only [HaloRecordLayout.windows_length] using hN) hshape.1 hshape.2 hcapacity tail v₁ F
    (by simpa [F] using hk) (by simpa [F,HaloRecordLayout.windows_length] using hp)
    (by simpa [F] using hb) (by simpa [F] using hm) (by simpa [F] using hr) (by rfl) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [F] using hblank _ (by simp))
  let out := returned A w B L H N cols++tail
  have hfinal : {F with R := Function.update F.R 39 out} = {S with R := Function.update S.R 39 out} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = 39
    · subst i; simp
    · simp [F,hi]
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) hfinal),?_⟩
  · simp only [HaloRecordLayout.windows_length] at hn₂
    omega
  · intro depth
    have hs₁ := GeneratedPeriodicHalo.emit_within_stock he₁ hn₁ depth
    have hs := mn_seq_within_add hs₁ (hs₂ depth)
    refine (hs.mono ?_).cast rfl (congrArg (mk v₂) hfinal)
    intro d z hz
    simpa only [HaloRecordLayout.windows_length] using hz

end IntegerMultBounds.MathlibTM2.Routing.HaloFieldReturn
