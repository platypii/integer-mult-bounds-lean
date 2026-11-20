module

public import IntegerMultBounds.Networks.Certificates.PR589.Word

@[expose] public section
namespace IntegerMultBounds.Networks.Certificates.PR589

private theorem separateD : sectionD.all (fun g : RawGate => !g.sources.contains g.target) = true := by
  simp only [sectionD,List.all_append,Bool.and_eq_true]
  repeat' constructor
  all_goals decide +kernel

private theorem separateA : sectionA.all (fun g : RawGate => !g.sources.contains g.target) = true := by
  simp only [sectionA,List.all_append,Bool.and_eq_true]
  repeat' constructor
  all_goals decide +kernel

private theorem separatescatter : sectionscatter.all (fun g : RawGate => !g.sources.contains g.target) = true := by
  simp only [sectionscatter,List.all_append,Bool.and_eq_true]
  repeat' constructor
  all_goals decide +kernel

private theorem separateB : sectionB.all (fun g : RawGate => !g.sources.contains g.target) = true := by
  simp only [sectionB,List.all_append,Bool.and_eq_true]
  repeat' constructor
  all_goals decide +kernel

private theorem separateC : sectionC.all (fun g : RawGate => !g.sources.contains g.target) = true := by
  simp only [sectionC,List.all_append,Bool.and_eq_true]
  repeat' constructor
  all_goals decide +kernel

theorem target_not_mem_sources (g : RawGate) (scheduled : g ∈ program) : g.target ∉ g.sources := by
  have allSeparate : program.all (fun g : RawGate => !g.sources.contains g.target) = true := by
    simp only [program,List.all_append,separateD,separateA,separatescatter,separateB,separateC]
    rfl
  simpa using List.all_eq_true.mp allSeparate g scheduled

end IntegerMultBounds.Networks.Certificates.PR589
