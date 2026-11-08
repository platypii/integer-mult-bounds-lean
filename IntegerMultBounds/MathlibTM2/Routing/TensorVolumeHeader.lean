module

public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderSetup
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock
public import IntegerMultBounds.MathlibTM2.NativePushBoundMono

/-! Generate a four-factor byte volume once and retire its two intermediate
products. All ordinary dimension masters and shared scratch are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.TensorVolumeHeader
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv FieldHeaderSetup
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def product4 (count height length width rows bytes dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (resetProduct count height rows saved tmp)
    (.seq (resetProduct length width bytes saved tmp)
      (.seq (resetProduct rows bytes dst saved tmp) (clearWords [rows,bytes])))

theorem product4_native (count height length width rows bytes dst saved tmp : Fin T) :
    mnNativePushBound 2 (product4 (P := P) (Q := Q) (A := A) (U := U)
      count height length width rows bytes dst saved tmp) :=
  ⟨resetProduct_pushBound _ _ _ _ _,resetProduct_pushBound _ _ _ _ _,resetProduct_pushBound _ _ _ _ _,
    mnNativePushBound_mono (by omega) (clearWords_native _)⟩

theorem product4_exec (count height length width rows bytes dst saved tmp : Fin T)
    (hreg : [count,height,length,width,rows,bytes,dst,saved,tmp].Nodup)
    (N B M w : ℕ) (hN : 0 < N) (hB : 0 < B) (hM : 0 < M) (hw : 0 < w)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : (S.R count).length = N) (hh : (S.R height).length = B)
    (hl : (S.R length).length = M) (hr : (S.R width).length = w)
    (hblank : ∀ i ∈ [rows,bytes,dst,saved,tmp], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ 43*(N*B*(M*w))+23 ∧
      Exec body (product4 count height length width rows bytes dst saved tmp) (mk v S) n
        (mk vf {S with R := Function.update S.R dst (List.replicate (N*B*(M*w)) tick)}) := by
  have hd := hreg
  regs_ne hd
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := resetProduct_exec (body := body) count height rows saved tmp
    (by regs_nodup) v S (hblank _ (by simp)) (hblank _ (by simp))
  simp only [hc,hh] at he₁
  have hn₁' : n₁ ≤ N*(4*B+9)+6 := by simp [hc,hh,hblank] at hn₁; omega
  let F : Stacks T A := {S with R := Function.update S.R rows (List.replicate (N*B) tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := resetProduct_exec (body := body) length width bytes saved tmp
    (by regs_nodup) v₁ F (by simp [F,‹rows ≠ saved›.symm,hblank]) (by simp [F,‹rows ≠ tmp›.symm,hblank])
  have hn₂' : n₂ ≤ M*(4*w+9)+6 := by
    simp [F,‹length ≠ rows›,‹width ≠ rows›,‹rows ≠ bytes›.symm,hl,hr,hblank] at hn₂
    omega
  let G : Stacks T A := {F with R := Function.update F.R bytes (List.replicate (M*w) tick)}
  have he₂' : Exec body (resetProduct length width bytes saved tmp) (mk v₁ F) n₂ (mk v₂ G) := by
    simpa [F,‹length ≠ rows›,‹width ≠ rows›,hl,hr] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := resetProduct_exec (body := body) rows bytes dst saved tmp
    (by regs_nodup) v₂ G (by simp [G,F,‹bytes ≠ saved›.symm,‹rows ≠ saved›.symm,hblank])
    (by simp [G,F,‹bytes ≠ tmp›.symm,‹rows ≠ tmp›.symm,hblank])
  have hn₃' : n₃ ≤ (N*B)*(4*(M*w)+9)+6 := by
    simp [G,F,‹rows ≠ bytes›,‹bytes ≠ dst›.symm,‹rows ≠ dst›.symm,hblank] at hn₃
    omega
  let J : Stacks T A := {G with R := Function.update G.R dst (List.replicate (N*B*(M*w)) tick)}
  have he₃' : Exec body (resetProduct rows bytes dst saved tmp) (mk v₂ G) n₃ (mk v₃ J) := by
    simpa [G,F,‹rows ≠ bytes›] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [rows,bytes] (by regs_nodup) v₃ J
  have hrows : (J.R rows).length = N*B := by simp [J,G,F,‹rows ≠ dst›,‹rows ≠ bytes›]
  have hbytes : (J.R bytes).length = M*w := by simp [J,G,‹bytes ≠ dst›]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,hrows,hbytes] at he₄
  refine ⟨v₄,n₁+(n₂+(n₃+(2*(N*B+(M*w+0))+2*(0+1+1)+1))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' he₄))).cast rfl ?_⟩
  · have hNB := Nat.le_mul_of_pos_right (N*B) (Nat.mul_pos hM hw)
    have hMw := Nat.le_mul_of_pos_left (M*w) (Nat.mul_pos hN hB)
    have hN' := Nat.le_mul_of_pos_right N hB
    have hM' := Nat.le_mul_of_pos_right M hw
    nlinarith only [hn₁',hn₂',hn₃',hNB,hMw,hN',hM']
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hir : i = rows
    · subst i; simp [hblank,‹rows ≠ dst›]
    by_cases hib : i = bytes
    · subst i; simp [hblank,‹bytes ≠ dst›]
    by_cases hid : i = dst
    · subst i; simp [J,hir,hib]
    · simp [J,G,F,hir,hib,hid]

end IntegerMultBounds.MathlibTM2.Routing.TensorVolumeHeader
