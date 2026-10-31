module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWindows

/-! Prepare scatter controls for any disjoint window class from retained gather
advances. The existing converter restores its source, count and scratch; a
runtime count test skips empty classes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def windowPublicationControls (count savedCount control savedControl counter window zero acc dst trash tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR count)) (.cond (·.flag)
    (publicationControls count savedCount control savedControl counter window zero acc dst trash tmp) (.act .done))

theorem windowPublicationGaps (windows : PublicationWindows s L) (w : ℕ) :
    publicationGaps (L*w) (originAdvances w 0 windows.origins) = windows.gaps w := by
  rw [originAdvances_symbols]
  simpa only [Nat.zero_mul,PublicationWindows.gaps,PublicationWindows.symbolOrigins] using
    (windowGaps_publicationGaps (L*w) (windows.origins.map (·*w))).symm

/-- The complete retained gather control stream, including its terminator,
supplies the publication controls. No execution premise is required. -/
theorem windowPublicationControls_exec
    (count savedCount control savedControl counter window zero acc dst trash tmp : Fin T)
    (hreg : [count,savedCount,control,savedControl,counter,window,zero,acc,dst,trash,tmp].Nodup)
    (windows : PublicationWindows s L) (w : ℕ) (hw1 : 1 ≤ w)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R count = List.replicate windows.origins.length tick)
    (hs : S.R control = gatherControls A (originAdvances w 0 windows.origins++[0])++borrowed)
    (hw : (S.R window).length = L*w)
    (hz : ∀ i ∈ [savedCount,savedControl,counter,zero,acc,trash,tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 33*s*w+23 ∧
      Exec body (windowPublicationControls count savedCount control savedControl counter window zero acc dst trash tmp)
        (mk v S) n (mk v' {S with R := (Function.update S.R dst
          (gatherControls A (windows.gaps w)++S.R dst))}) := by
  let v₀ : HS T Q A U := {v with flag := (S.R count).head?.isSome}
  have he₀ : Exec body (.act (peekR count)) (mk v S) 1 (mk v₀ S) := by
    simpa only [peekR_run,v₀] using Exec.act (body := body) (peekR count) (mk v S)
  cases he : windows.origins with
  | nil =>
    have hf : v₀.flag = false := by simp [v₀,hc,he]
    have hd : Exec body (.act (.done : Act T Q A U)) (mk v₀ S) 1 (mk v₀ S) := Exec.act _ _
    refine ⟨v₀,3,rfl,by omega,?_⟩
    have hex := Exec.seq he₀ (Exec.cond_false (p := publicationControls count savedCount control savedControl counter window zero acc dst trash tmp) hf hd)
    simpa only [windowPublicationControls,PublicationWindows.gaps,PublicationWindows.symbolOrigins,he,
      List.map_nil,windowGaps,gatherControls,List.nil_append,Function.update_eq_self] using hex
  | cons p ps =>
    let ds := originAdvances w p ps
    have hds : ds.length = ps.length := originAdvances_length w p ps
    have hadv : originAdvances w 0 windows.origins = p*w::ds := by simp [he,originAdvances,ds]
    have hdisjoint : (p::ps).Pairwise (fun p q => p+L ≤ q) := by rw [←he]; exact windows.disjoint
    have hLd : ∀ d ∈ ds, L*w ≤ d := originAdvances_lower L w p ps hdisjoint
    have hsource : S.R control = gatherControls A (p*w::ds)++([blank]++borrowed) := by
      rw [hs,hadv,gatherControls_append]
      simp [gatherControls,List.append_assoc]
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := publicationControls_exec (body := body) hreg (L*w) (p*w) ds hLd
      tick (List.replicate ps.length tick) ([blank]++borrowed) (by simp [hds]) v₀ S
      (by simpa only [he,List.length_cons,List.replicate_succ] using hc) hsource hw hz
    have hgaps : p*w::ds.map (·-L*w) = windows.gaps w := by
      have hg := windowPublicationGaps windows w
      rw [hadv] at hg
      exact hg
    have hvol : (originAdvances w 0 windows.origins).sum ≤ s*w := by
      have ho : (0::windows.origins).Pairwise (· ≤ ·) :=
        List.pairwise_cons.mpr ⟨by simp,windows.disjoint.imp (fun h => by omega)⟩
      simpa only [Nat.zero_mul,Nat.zero_add] using originAdvances_sum_le w 0 s windows.origins ho (Nat.zero_le _)
        (fun origin ho => Nat.le_trans (Nat.le_add_right origin L) (windows.fits origin ho))
    rw [hadv,List.sum_cons] at hvol
    have hcount : ps.length+1 ≤ s := by simpa only [he,List.length_cons] using windows.count_le
    have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw1
    have hf : v₀.flag = true := by simp [v₀,hc,he]
    refine ⟨v₁,1+(n₁+1),hu₁,?_,?_⟩
    · rw [hds] at hn₁
      nlinarith only [hn₁,hvol,hcount,hsw]
    · simpa only [windowPublicationControls,hgaps] using Exec.seq he₀ (Exec.cond_true (q := .act .done) hf he₁)

theorem windowPublicationControls_length_le (windows : PublicationWindows s L) (w : ℕ) (hw1 : 1 ≤ w) :
    (gatherControls A (windows.gaps w)).length ≤ 2*s*w := by
  have hv := windows.gaps_volume w
  have hc := windows.count_le
  have hs : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw1
  simp only [scatterVolume,PublicationWindows.gaps_length] at hv
  have hv' : (windows.gaps w).sum ≤ s*w := by omega
  simp only [length_gatherControls,PublicationWindows.gaps_length]
  nlinarith only [hv',hc,hs]

/-- Release the owned control tape after all replicas, restoring its initial
blank state. Borrowed advance controls are outside this release. -/
theorem releaseWindowPublicationControls_exec (dst : Fin T) (windows : PublicationWindows s L)
    (w : ℕ) (hw1 : 1 ≤ w) (v : HS T Q A U) (S : Stacks T A)
    (hdst : S.R dst = gatherControls A (windows.gaps w)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 4*s*w+2 ∧
      Exec body (uclear dst) (mk v S) n (mk v' {S with R := Function.update S.R dst []}) := by
  obtain ⟨v',hu,he⟩ := uclear_exec (body := body) dst v S
  have hl := windowPublicationControls_length_le (A := A) windows w hw1
  refine ⟨v',2*(S.R dst).length+2,hu,?_,he⟩
  rw [hdst]
  nlinarith only [hl]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
