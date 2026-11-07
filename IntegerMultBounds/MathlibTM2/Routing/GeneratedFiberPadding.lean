module

public import IntegerMultBounds.MathlibTM2.Routing.FiberPadding
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPadding
public import IntegerMultBounds.MathlibTM2.Routing.FieldBoundaryStock
public import Mathlib.Data.Nat.Log

/-! Derive only the current field's missing-symbol count from retained ordinary
headers, execute an ordered stream operation, then retire the derived header. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.GeneratedFiberPadding
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  FiberPadding SmallFieldMove
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def paddingState (S : Stacks T A) (pad : Fin T) (k R V : ℕ) : Stacks T A :=
  {S with R := Function.update S.R pad (List.replicate (2^k*R-V) tick)}

def withPadding (exponent width volume pad saved work : Fin T) (p : Pr P T Q A U) : Pr P T Q A U :=
  .seq (padding exponent width volume pad saved work) (.seq p (uclear pad))

theorem withPadding_exec (exponent width volume pad saved work clock src : Fin T)
    (hreg : [exponent,width,volume,pad,saved,work,clock,src].Nodup)
    (p : Pr P T Q A U) (k R V c : ℕ) (output : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = k) (hw : (S.R width).length = R)
    (hv : (S.R volume).length = V) (hpad : S.R pad = [])
    (hsaved : S.R saved = []) (hwork : S.R work = [])
    (hoperation : ∀ vi : HS T Q A U, ∃ vf n, vf.user = vi.user ∧ n ≤ c ∧
      Exec body p (mk vi (paddingState S pad k R V)) n
        (mk vf {paddingState S pad k R V with R := (Function.update
          (Function.update (paddingState S pad k R V).R src output) clock [])})) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ (4*R+4*(2^k*R)+9*k+4*V+12)+c+(2*(2^k*R-V)+2) ∧
      Exec body (withPadding exponent width volume pad saved work p) (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R src output) clock [])}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := padding_exec (body := body)
    (lR := exponent) (wR := width) (src := volume) (pad := pad) (t₁ := saved) (t₂ := work)
    (by regs_nodup) v S hpad hsaved hwork
  have he₁' : Exec body (padding exponent width volume pad saved work) (mk v S) n₁
      (mk v₁ (paddingState S pad k R V)) := by simpa only [hk,hw,hv,paddingState] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hoperation v₁
  let M : Stacks T A := {paddingState S pad k R V with R := (Function.update
    (Function.update (paddingState S pad k R V).R src output) clock [])}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) pad v₂ M
  refine ⟨v₃,n₁+(n₂+(2*(M.R pad).length+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hk,hw,hv] at hn₁
    simp only [M,Function.update_of_ne ‹pad ≠ clock›,Function.update_of_ne ‹pad ≠ src›,
      paddingState,Function.update_self,List.length_replicate]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hip : i = pad
    · subst i; simp [‹pad ≠ src›,‹pad ≠ clock›,hpad]
    · simp [M,paddingState,Function.update_apply,hip]

def generatedPadFibers (exponent width volume pad saved work clock src archive tmp : Fin T)
    (zero : Fin (A+4)) : Pr P T Q A U :=
  withPadding exponent width volume pad saved work (padFibers clock volume pad src archive tmp zero)

theorem generatedPadFibers_exec (exponent width volume pad saved work clock src archive tmp : Fin T)
    (hreg : [exponent,width,volume,pad,saved,work,clock,src,archive,tmp].Nodup)
    (zero : Fin (A+4)) (rows : List (List (Fin (A+4)))) (k R V : ℕ)
    (hlen : ∀ xs ∈ rows, xs.length = V) (hfit : V ≤ 2^k*R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = k) (hw : (S.R width).length = R)
    (hv : (S.R volume).length = V) (hclock : (S.R clock).length = rows.length)
    (hsrc : S.R src = rows.flatten++tail)
    (hpad : S.R pad = []) (hsaved : S.R saved = []) (hwork : S.R work = [])
    (harchive : S.R archive = []) (htmp : S.R tmp = []) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ (4*R+4*(2^k*R)+9*k+4*V+12)+(rows.length*(6*(2^k*R)+11)+4)+(2*(2^k*R-V)+2) ∧
      Exec body (generatedPadFibers exponent width volume pad saved work clock src archive tmp zero)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update S.R src
          (rows.flatMap (fun xs => xs++List.replicate (2^k*R-V) zero)++tail)) clock [])}) := by
  have hr := hreg
  regs_ne hr
  apply withPadding_exec (body := body) exponent width volume pad saved work clock src
    (by regs_nodup) _ k R V _ _ v S hk hw hv hpad hsaved hwork
  intro vi
  let M := paddingState S pad k R V
  have hoff (i : Fin T) (hi : i ≠ pad) : M.R i = S.R i := by simp [M,paddingState,hi]
  obtain ⟨vf,n,hu,hn,he⟩ := padFibers_exec (body := body) clock volume pad src archive tmp (by regs_nodup)
    zero rows V (2^k*R-V) hlen tail vi M
    (by rw [hoff clock ‹pad ≠ clock›.symm]; exact hclock)
    (by rw [hoff volume ‹volume ≠ pad›]; exact hv)
    (by simp [M,paddingState])
    (by rw [hoff src ‹pad ≠ src›.symm]; exact hsrc)
    (by rw [hoff archive ‹pad ≠ archive›.symm]; exact harchive)
    (by rw [hoff tmp ‹pad ≠ tmp›.symm]; exact htmp)
  exact ⟨vf,n,hu,by simpa only [Nat.add_sub_of_le hfit] using hn,he⟩

def generatedCropFibers (exponent width volume pad saved work clock src archive trash tmp : Fin T) :
    Pr P T Q A U :=
  withPadding exponent width volume pad saved work (cropFibers clock volume pad src archive trash tmp)

theorem generatedCropFibers_exec (exponent width volume pad saved work clock src archive trash tmp : Fin T)
    (hreg : [exponent,width,volume,pad,saved,work,clock,src,archive,trash,tmp].Nodup)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (k R V : ℕ)
    (hlen : ∀ r ∈ rows, r.1.length = V ∧ r.2.length = 2^k*R-V) (hfit : V ≤ 2^k*R)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = k) (hw : (S.R width).length = R)
    (hv : (S.R volume).length = V) (hclock : (S.R clock).length = rows.length)
    (hsrc : S.R src = pairStream rows++tail)
    (hpad : S.R pad = []) (hsaved : S.R saved = []) (hwork : S.R work = [])
    (harchive : S.R archive = []) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ (4*R+4*(2^k*R)+9*k+4*V+12)+(rows.length*(6*(2^k*R)+13)+4)+(2*(2^k*R-V)+2) ∧
      Exec body (generatedCropFibers exponent width volume pad saved work clock src archive trash tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update S.R src
          (rows.flatMap Prod.fst++tail)) clock [])}) := by
  have hr := hreg
  regs_ne hr
  apply withPadding_exec (body := body) exponent width volume pad saved work clock src
    (by regs_nodup) _ k R V _ _ v S hk hw hv hpad hsaved hwork
  intro vi
  let M := paddingState S pad k R V
  have hoff (i : Fin T) (hi : i ≠ pad) : M.R i = S.R i := by simp [M,paddingState,hi]
  obtain ⟨vf,n,hu,hn,he⟩ := cropFibers_exec (body := body) clock volume pad src archive trash tmp (by regs_nodup)
    rows V (2^k*R-V) hlen tail vi M
    (by rw [hoff clock ‹pad ≠ clock›.symm]; exact hclock)
    (by rw [hoff volume ‹volume ≠ pad›]; exact hv)
    (by simp [M,paddingState])
    (by rw [hoff src ‹pad ≠ src›.symm]; exact hsrc)
    (by rw [hoff archive ‹pad ≠ archive›.symm]; exact harchive)
    (by rw [hoff trash ‹pad ≠ trash›.symm]; exact htrash)
    (by rw [hoff tmp ‹pad ≠ tmp›.symm]; exact htmp)
  exact ⟨vf,n,hu,by simpa only [Nat.add_sub_of_le hfit] using hn,he⟩

theorem withPadding_pushBound (exponent width volume pad saved work : Fin T) (p : Pr P T Q A U)
    (hp : mnNativePushBound 2 p) : mnNativePushBound 2 (withPadding exponent width volume pad saved work p) := by
  simp only [withPadding,mnNativePushBound]
  refine ⟨?_,hp,?_⟩
  · simp [padding,ucopy,umulSym,scanR,keepIn,drainR,popDo,pushN,upow2,scanP,popPush,udbl,
      usub,dropTop,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  · simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem generatedPadFibers_pushBound (exponent width volume pad saved work clock src archive tmp : Fin T)
    (zero : Fin (A+4)) :
    mnNativePushBound 2 (generatedPadFibers (P := P) (Q := Q) (U := U)
      exponent width volume pad saved work clock src archive tmp zero) :=
  withPadding_pushBound _ _ _ _ _ _ _ (padFibers_pushBound _ _ _ _ _ _ _)

theorem generatedCropFibers_pushBound (exponent width volume pad saved work clock src archive trash tmp : Fin T) :
    mnNativePushBound 2 (generatedCropFibers (P := P) (Q := Q) (A := A) (U := U)
      exponent width volume pad saved work clock src archive trash tmp) :=
  withPadding_pushBound _ _ _ _ _ _ _ (cropFibers_pushBound _ _ _ _ _ _ _)

/-- Setup, padding generation and retirement are absorbed by a nonempty complete
row stream. Cropping uses the larger of the two per-row constants. -/
theorem generatedPaddingCost_le {n N k R V : ℕ} (hR : 0 < R) (hN : 0 < N) (hfit : V ≤ 2^k*R)
    (hn : n ≤ (4*R+4*(2^k*R)+9*k+4*V+12)+(N*(6*(2^k*R)+13)+4)+(2*(2^k*R-V)+2)) :
    n ≤ 64*(N*(2^k*R)) := by
  let C := 2^k*R
  have hC : 0 < C := Nat.mul_pos (Nat.two_pow_pos k) hR
  have hk : k ≤ C := by
    simpa only [Nat.one_mul] using FieldBoundaryStock.bits_le_volume k 1 1 R (by decide) (by decide) hR
  have hR' : R ≤ C := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right R (Nat.one_le_two_pow (n := k))
  have hNC : C ≤ N*C := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right C (show 1 ≤ N by omega)
  have hN' : N ≤ N*C := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N (show 1 ≤ C by omega)
  have hpos : 0 < N*C := Nat.mul_pos hN hC
  have hsub : C-V ≤ C := Nat.sub_le _ _
  change V ≤ C at hfit
  change n ≤ (4*R+4*C+9*k+4*V+12)+(N*(6*C+13)+4)+(2*(C-V)+2) at hn
  change n ≤ 64*(N*C)
  nlinarith only [hn,hR',hk,hfit,hsub,hNC,hN',hpos]

/-- Only the currently moved field is rounded up; its dyadic capacity is less
than twice its real positive length. -/
theorem dyadic_capacity_bounds (M : ℕ) (hM : 0 < M) :
    M ≤ 2^(Nat.clog 2 M) ∧ 2^(Nat.clog 2 M) < 2*M := by
  refine ⟨Nat.le_pow_clog (by decide) M,?_⟩
  by_cases hm : M = 1
  · subst M; simp
  have hm' : 1 < M := by omega
  have hk := Nat.clog_pos (by decide : 1 < 2) hm'
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hm'
  have he : Nat.clog 2 M = (Nat.clog 2 M).pred+1 := (Nat.succ_pred_eq_of_pos hk).symm
  rw [he,Nat.pow_succ]
  omega

theorem padded_volume_lt_twice (N M R : ℕ) (hN : 0 < N) (hM : 0 < M) (hR : 0 < R) :
    N*(2^(Nat.clog 2 M)*R) < 2*(N*(M*R)) := by
  have h := Nat.mul_lt_mul_of_pos_left
    (Nat.mul_lt_mul_of_pos_right (dyadic_capacity_bounds M hM).2 hR) hN
  convert h using 1; ring

/-- With the least dyadic capacity, even generated setup and retirement are
linear in the real input volume, independent of all other field lengths. -/
theorem generatedPaddingCost_le_input {n N M R : ℕ} (hN : 0 < N) (hM : 0 < M) (hR : 0 < R)
    (hn : n ≤ (4*R+4*(2^(Nat.clog 2 M)*R)+9*(Nat.clog 2 M)+4*(M*R)+12)+
      (N*(6*(2^(Nat.clog 2 M)*R)+13)+4)+(2*(2^(Nat.clog 2 M)*R-M*R)+2)) :
    n ≤ 128*(N*(M*R)) := by
  have hc := generatedPaddingCost_le hR hN
    (Nat.mul_le_mul_right R (dyadic_capacity_bounds M hM).1) hn
  have hv := padded_volume_lt_twice N M R hN hM hR
  nlinarith only [hc,hv]

theorem generatedPadFibers_within_stock
    {exponent width volume pad saved work clock src archive tmp : Fin T} {zero : Fin (A+4)}
    {v vf : HS T Q A U} {S F : Stacks T A} {n N k R V : ℕ}
    (hex : Exec body (generatedPadFibers exponent width volume pad saved work clock src archive tmp zero)
      (mk v S) n (mk vf F))
    (hn : n ≤ (4*R+4*(2^k*R)+9*k+4*V+12)+(N*(6*(2^k*R)+11)+4)+(2*(2^k*R-V)+2))
    (hR : 0 < R) (hN : 0 < N) (hfit : V ≤ 2^k*R) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+128*(N*(2^k*R)))
      depth (generatedPadFibers exponent width volume pad saved work clock src archive tmp zero)
      (mk v S) n (mk vf F) := by
  have hc := generatedPaddingCost_le hR hN hfit (n := n) (by nlinarith only [hn])
  exact mn_native_exec_within hex 2 (generatedPadFibers_pushBound _ _ _ _ _ _ _ _ _ _ _)
    depth _ (by omega)

theorem generatedCropFibers_within_stock
    {exponent width volume pad saved work clock src archive trash tmp : Fin T}
    {v vf : HS T Q A U} {S F : Stacks T A} {n N k R V : ℕ}
    (hex : Exec body (generatedCropFibers exponent width volume pad saved work clock src archive trash tmp)
      (mk v S) n (mk vf F))
    (hn : n ≤ (4*R+4*(2^k*R)+9*k+4*V+12)+(N*(6*(2^k*R)+13)+4)+(2*(2^k*R-V)+2))
    (hR : 0 < R) (hN : 0 < N) (hfit : V ≤ 2^k*R) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+128*(N*(2^k*R)))
      depth (generatedCropFibers exponent width volume pad saved work clock src archive trash tmp)
      (mk v S) n (mk vf F) := by
  have hc := generatedPaddingCost_le hR hN hfit hn
  exact mn_native_exec_within hex 2 (generatedCropFibers_pushBound _ _ _ _ _ _ _ _ _ _ _)
    depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Routing.GeneratedFiberPadding
