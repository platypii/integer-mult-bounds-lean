module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Structural crop-and-retire execution for arbitrary interval storage.
Full ambient S3 lines and clipped halos share the same fixed archive program. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- A fixed publication loop: the archive is consumed block by block. -/
def packedCoreArchiveLoop (clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T) : Pr P T Q A U :=
  countedLoop clock (packedCoreArchiveStep skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)



theorem packedCoreArchiveLoop_interval_exec
    (clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (w a L offset length : ℕ)
    (hfit : a+L ≤ s) (hpart : offset+length ≤ L)
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (hsrc : S.R src = (Ds.map (fun D => cstream A w
      (packedInterval a L D))).flatten++tail)
    (hclock : (S.R clock).length = Ds.length)
    (hskip : (S.R skip).length = offset*w)
    (hcount : (S.R count).length = length*w)
    (hrows : (S.R rows).length = L)
    (hwidth : (S.R width).length = w)
    (hclean : ∀ i ∈ [savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ Ds.length*(packedCoreArchiveStepCost offset length
        L w+3)+2 ∧
      Exec body (packedCoreArchiveLoop clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' F) ∧
      F.R src = tail ∧ F.R dst = (Ds.reverse.map (fun D => cstream A w (packedInterval (a+offset) length D))).flatten++S.R dst ∧
      F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i := by
  have hr := hreg
  regs_ne hr
  have h12 : [skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup := hreg.tail
  let halo := fun D : ZMod s → GaussianInt => cstream A w
    (packedInterval a L D)
  let core := fun D : ZMod s → GaussianInt => cstream A w (packedInterval (a+offset) length D)
  let Inv := fun j (R : Stacks T A) => ∃ done todo : List (ZMod s → GaussianInt),
    Ds = done++todo ∧ done.length = j ∧ R.inp = S.inp ∧ R.out = S.out ∧ R.L = S.L ∧
    (∀ i, i ≠ src → i ≠ dst → i ≠ clock → R.R i = S.R i) ∧
    R.R src = (todo.map halo).flatten++tail ∧ R.R dst = (done.reverse.map core).flatten++S.R dst
  obtain ⟨v',F,n,hu,hn,he,hclock',hI⟩ := countedLoop_exec (body := body) clock
    (packedCoreArchiveStep skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
    Ds.length (packedCoreArchiveStepCost offset length L w)
    Inv (by
      intro j R xs hI
      obtain ⟨done,todo,hDs,hlen,hi,ho,hl,hframe,hsrc,hdst⟩ := hI
      refine ⟨done,todo,hDs,hlen,hi,ho,hl,?_,?_,?_⟩
      · intro i hi hd hc
        simpa only [Function.update_of_ne hc] using hframe i hi hd hc
      · simpa only [Function.update_of_ne ‹clock ≠ src›.symm] using hsrc
      · simpa only [Function.update_of_ne ‹clock ≠ dst›.symm] using hdst)
    (by
      intro j hj vi R hI
      obtain ⟨done,todo,hDs,hlen,hi,ho,hl,hframe,hsrc,hdst⟩ := hI
      cases todo with
      | nil => simp only [List.append_nil] at hDs; subst Ds; omega
      | cons D todo =>
        have hcontrol : ∀ i ∈ [skip,count,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp], R.R i = S.R i := by
          intro i hi
          apply hframe i
          all_goals
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            all_goals first | assumption | (apply Ne.symm; assumption)
        obtain ⟨vf,m,hu,hm,hex⟩ := packedCoreArchiveStep_interval_exec (body := body)
          skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp h12
          vi R w a L offset length hfit hpart D ((todo.map halo).flatten++tail)
          (by simpa only [List.map_cons,List.flatten_cons,List.append_assoc] using hsrc)
          (by rw [hcontrol skip (by simp)]; exact hskip)
          (by rw [hcontrol count (by simp)]; exact hcount)
          (by rw [hcontrol rows (by simp)]; exact hrows)
          (by rw [hcontrol width (by simp)]; exact hwidth)
          (by
            intro i hi
            have hc : i ∈ [skip,count,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp] := by
              simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
              rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
            rw [hcontrol i hc]
            exact hclean i hi)
        let R' : Stacks T A := {R with R := (Function.update (Function.update R.R dst (core D++R.R dst))
          src ((todo.map halo).flatten++tail))}
        refine ⟨vf,R',m,hu,hm,hex,?_,done++[D],todo,?_,?_,hi,ho,hl,?_,?_,?_⟩
        · simp [R',‹clock ≠ src›,‹clock ≠ dst›]
        · simpa only [List.append_assoc,List.singleton_append] using hDs
        · simp only [List.length_append,List.length_singleton,hlen]
        · intro i his hid hic
          simpa only [R',Function.update_of_ne his,Function.update_of_ne hid] using hframe i his hid hic
        · simp [R']
        · simp only [R',Function.update_of_ne ‹src ≠ dst›.symm,Function.update_self]
          rw [hdst]
          simp only [List.reverse_append,List.reverse_singleton,List.map_cons,List.map_nil,List.map_append,
            List.flatten_cons,List.flatten_nil,List.flatten_append,List.nil_append,List.append_assoc])
    v S hclock ⟨[],Ds,rfl,rfl,rfl,rfl,rfl,(by intros; rfl),hsrc,by simp⟩
  obtain ⟨done,todo,hDs,hlen,hi,ho,hl,hframe,hsrc',hdst⟩ := hI
  have ht : todo = [] := by
    have hlenDs := congrArg List.length hDs
    simp only [List.length_append] at hlenDs
    cases todo with
    | nil => rfl
    | cons D todo => simp only [List.length_cons] at hlenDs; omega
  subst todo
  simp only [List.append_nil] at hDs
  subst done
  exact ⟨v',F,n,hu,hn,he,by simpa using hsrc',hdst,hclock',hi,ho,hl,hframe⟩

/-- Crop full ambient solver outputs and retire each complete line. The destination
receives blocks in reverse input order; every traversal is included in the cost. -/
theorem fullLineCoreArchive_exec
    (clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp : Fin T)
    (hreg : [clock,skip,count,src,dst,savedSkip,saved,tmp,rows,width,retireCount,trash,retireTmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (w coreWidth k : ℕ)
    (hstart : coreStart coreWidth k ≤ s)
    (Ds : List (ZMod s → GaussianInt)) (tail : List (Fin (A+4)))
    (hsrc : S.R src = cstream A w (Ds.map (chirpLine s)).flatten++tail)
    (hclock : (S.R clock).length = Ds.length)
    (hskip : (S.R skip).length = coreStart coreWidth k*w)
    (hcount : (S.R count).length = coreLength s coreWidth k*w)
    (hrows : (S.R rows).length = s)
    (hwidth : (S.R width).length = w)
    (hclean : ∀ i ∈ [savedSkip,saved,tmp,retireCount,trash,retireTmp], S.R i = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ Ds.length*(packedCoreArchiveStepCost (coreStart coreWidth k) (coreLength s coreWidth k)
        (s) w+3)+2 ∧
      Exec body (packedCoreArchiveLoop clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp)
        (mk v S) n (mk v' F) ∧
      F.R src = tail ∧ F.R dst = (Ds.reverse.map (fun D => cstream A w (ownedCoreWords coreWidth k D))).flatten++S.R dst ∧
      F.R clock = [] ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → i ≠ clock → F.R i = S.R i := by
  have hblocks : (Ds.map (fun D => cstream A w (packedInterval 0 s D))).flatten =
      cstream A w (Ds.map (chirpLine s)).flatten := by
    clear hsrc hclock
    have hfull (D : ZMod s → GaussianInt) : packedInterval 0 s D = chirpLine s D := by
      unfold packedInterval
      rw [List.drop_zero]
      exact List.take_of_length_le (by simp)
    induction Ds with
    | nil => rfl
    | cons D Ds ih =>
      simp only [hfull] at ih
      simpa only [List.map_cons,List.flatten_cons,hfull,cstream_append] using
        congrArg (fun xs => cstream A w (chirpLine s D)++xs) ih

  obtain ⟨v',F,n,hu,hn,he,hsrc',hdst,hclock',hi,ho,hl,hframe⟩ := packedCoreArchiveLoop_interval_exec
    clock skip count src dst savedSkip saved tmp rows width retireCount trash retireTmp hreg
    v S w 0 s (coreStart coreWidth k) (coreLength s coreWidth k) (by omega)
    (by dsimp only [coreLength]; have := Nat.min_le_right coreWidth (s-coreStart coreWidth k); omega)
    Ds tail (by simpa only [hblocks] using hsrc) hclock hskip hcount hrows hwidth hclean
  refine ⟨v',F,n,hu,hn,he,hsrc',?_,hclock',hi,ho,hl,hframe⟩
  simpa only [Nat.zero_add,packedInterval,ownedCoreWords] using hdst

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
