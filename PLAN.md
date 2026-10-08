# Plan and progress

A detailed breakdown of the [README](README.md) status table. Each section
matches one README row and splits it into subcomponents. *Mathematics* means
the statements the algorithm relies on are proved in Lean. *Tape* means a
program in the literal machine model is proved correct with a runtime bound.
See [COMPONENTS.md](COMPONENTS.md) for what each file proves.

✅ done · 🟡 partial · ⬜ not started · 🚧 drafted, not yet in the build

## Overview

| Part of the proof | Source | Mathematics | Tape |
| --- | --- | --- | --- |
| Machine model and target statement | §2 | ✅ | ✅ |
| Composition, loops, frames, elementary streams | §2 | 🟡 | 🟡 |
| Finite networks with a rank saving | §3 | ✅ | ⬜ |
| Faster interchange of address chunks | §4 | ✅ | ⬜ |
| Simultaneous butterfly layers with compact control | §5, §11, CrocSwap | ✅ | 🟡 |
| Synthetic transforms and their tape layout | §6 | ✅ | ⬜ |
| Gaussian resampling | §7 | ✅ | ⬜ |
| `O(n log n)` subroutine | Harvey–van der Hoeven | 🟡 | ⬜ |
| Exact multiplication, parameters, time bound | §8 | 🟡 | ⬜ |
| End-to-end theorem `EndToEnd` | — | 🟡 | ⬜ |

## 1. Machine model and target statement (§2)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Multi-tape machine semantics | `Machine.lean` | ✅ | ✅ | Finite alphabet, fixed tapes, local transitions |
| Target proposition `EndToEnd` | `Machine.lean` | ✅ | ✅ | Stated, not proved |
| Axiom audit | `AxiomAudit.lean` | ✅ | — | Only `propext`, `Quot.sound`, `Classical.choice` |

## 2. Composition, loops, frames, elementary streams (§2)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Sequential composition and Hoare contracts | `Composition`, `Hoare` | ✅ | ✅ | Exact one-transition join |
| While loops with potential-based costs | `Loop` | ✅ | ✅ | Clients supply invariants |
| Tape extension and reindexing | `Frame` | ✅ | ✅ | No random access to fields within a tape |
| Alphabet widening and protected regions | `Alphabet`, `Protected` | ✅ | ✅ | Foreign markers need a locality invariant |
| Scan, rewind, copy, move | `Execution`, `Rewind`, `WordTape`, `Copy` | ✅ | ✅ | One transition per symbol |
| Binary counters | `Counter`, `BitTape`, `CounterTape` | ✅ | ✅ | `8n + 2·width` for `n` increments |
| Terminating binary-counted raw transfer | `CountdownData`, `CountedCopy` | ✅ | ✅ | Literal three-tape, five-state copy, including all borrow scans, returns and final halt; runtime at most five times the count plus twice the clock width plus two. Prepared clock is explicit; descriptor preparation/reset remains separate |
| Counted backwards payload copy | `Reflection`, `CountedReverse` | ✅ | ✅ | Literal reflected transition tables preserve exact runtime; backwards source traversal outputs the reversed word within the linear countdown bound. Reusable variant includes clock setup/cleanup; initial positioning and descriptor construction remain separate |
| Ordered-affine payload semantics | `BlockRotationData`, `BlockNegationData`, `ScalingPieces`, `ScalingControl` | ✅ | ⬜ | Exact block-shift and negation payload indices, flat split and reversal recipe; unique scaling-piece merge, inverse reconstruction, monotone streams, fixed residue selection and exact contiguous piece lengths. Literal split/merge scheduling remains open |
| Sequential scaling merge and literal dispatch | `ScalingMergeData`, `Dispatch` | ✅ | 🟡 | FIFO cursor correctness, non-underflow and full consumption proved; literal finite-family dispatch costs one step. Connecting block copies, residue updates and counted iteration remains open |
| Literal scaling split with buffer rewinds | `ScalingSplitRewind` | ✅ | ✅ | Copies exact contiguous pieces then physically returns each buffer head to its merge-ready origin, preserving all descriptors and clocks. Actual canonical bound is twenty-four times volume plus forty-eight times fixed piece count plus one |
| Literal inverse-piece concatenation | `ScalingConcatenate`, `ScalingPartitionData` | ✅ | ✅ | All physical source rewinds/copies and joins charged; exact family concatenation and inverse block-address identity proved. Assembly with scatter/cleanup remains separate |
| Fully reusable positive-unit scaling | `ScalingExecutionReuse` | ✅ | ✅ | Actual residue initialization, split, rewinds, merge and buffer cleanup compose with full source/scratch/control guarantees and linear-volume runtime. Canonical B/Q/piece descriptors remain explicit inputs |
| Fully reusable inverse-unit scaling | `ScalingInverseExecution` | ✅ | ✅ | Actual initialized scatter, rewind/concatenate and buffer cleanup have exact inverse block semantics and linear-volume runtime. Canonical binary descriptors remain supplied |
| Actual signed-affine payload semantics | `ScalingAffineBridge` | ✅ | 🟡 | Positive/inverse scaling plus sign negation exactly implement every actual rational scale at all prime-power widths. Literal signed-stage composition remains separate |
| Repeated reusable inverse scaling | `ScalingInverseStream` | ✅ | ✅ | Full initialized inverse-scaling routine repeats with shared restored scratch and immutable descriptors; exact per-fiber inverse payload and linear total-volume execution |
| Whole-fiber repositioning and cleanup | `CountedSpanSeek`, `CountedSpanReset` | ✅ | ✅ | Literal five-tape routines use only separate B/Q descriptors, preserve all outside cells and restore controls. Canonical rewind/cleanup costs are linear in volume; no product-length descriptor needed |
| Literal scaling-piece descriptor synthesis | `ScalingDescriptorData`, `ScalingDescriptors` | ✅ | ✅ | Generates canonical exact piece lengths from blank descriptor tapes using supplied Q/B descriptors; all sentinels, residue setup, increments and cleanup charged, with bound seventy times Q*B plus fifty-one. Assembly with scaling remains separate |
| Scaling with generated piece descriptors | `ScalingPreparedExecution` | ✅ | ✅ | Actual synthesis from blank work tapes composes with full reusable one-fiber scaling, bound197*volume+120*c+106. Only canonical Q/B descriptors supplied; repeated-family and inverse descriptor assembly remain separate |
| Literal unsigned rational scale composition | `SignedScalingExecution.unsignedProgram` | ✅ | ✅ | Numerator scaling, physical intermediate rewind, denominator inversion and intermediate cleanup compose with exact payload semantics and linear-volume runtime. Coefficient descriptors remain supplied and optional sign is separate |
| Literal signed rational scale composition | `SignedScalingSign`, `BinaryOneInit` | ✅ | ✅ | Actual sign-selected numerator/denominator scaling, optional negation and full intermediate cleanup have exact signed payload semantics and linear-volume bounds. Coefficient and negative-tail descriptors remain explicit supplied data |
| Actual network scalar tape realization | `ActualAffineScaling` | ✅ | ✅ | One fixed machine per actual rational scale realizes its OrderedAffine target update uniformly in radix width with proved linear-volume cost. Coefficient/tail descriptors and blank scratch remain explicit prerequisites |
| Literal shift descriptor construction | `BinarySubReuse`, `TranslationProduct`, `TranslationDescriptors` | ✅ | ✅ | Actual subtraction and nested counted products construct exact canonical split lengths from Q,a,B with linear-volume cost. Inputs preserved; metadata reuse cleanup and payload composition remain separate |
| Reusable shift metadata | `TranslationDescriptorsReuse` | ✅ | ✅ | Exact marked-bank synthesis plus physical erasure/reset of generated lengths and subtraction scratch, including sentinel removal. Q,a,B survive; linear-volume synthesis/cleanup bounds proved for iteration with new offsets |
| Negation tail descriptors from dimensions | `NegationDescriptors` | ✅ | ✅ | Writes constant one and constructs canonical tail length/count from Q/B with all arithmetic and setup charged. Fixed11tape160state machine costs216*Q*B+121; signed-wrapper assembly remains separate |
| Translation with generated split lengths | `TranslationPreparedExecution` | ✅ | ✅ | Actual descriptor synthesis and rotation compose into exact y→y+a modulo Q, preserving source and advancing payload heads, with bound199*Q*B+212. Only canonical Q/a/B supplied; reusable metadata cleanup is separately proved |
| Signed scaling with generated coefficient descriptors | `FamilyPlacement`, `SignedScalingPrepared` | ✅ | ✅ | Physically synthesizes numerator/denominator descriptor families from Q/B, shares tapes by static placement and executes exact signed scaling in linear volume. Negative-tail descriptors and fixed split sentinel remain supplied |
| Signed scaling from dimension descriptors | `SignedScalingDimensions` | ✅ | ✅ | Composes actual negative-tail and coefficient-family synthesis with signed execution; only Q/B numeric inputs, exact full-bank output and bound(1950+120*(a+d))*Q*B. Scratch and inherited fixed sentinels explicit; network specialization and stream scheduler separate |
| Actual network scalars from dimensions | `ActualAffineScalingDimensions` | ✅ | ✅ | Each actual Shared50 scalar has a width-independent machine with exact full-bank and ordered-affine output and linear runtime; Q/B numeric inputs only. Fixed sentinel/scratch requirements remain; full stream/network scheduling separate |
| Reusable signed rational scaling stream | `SignedScalingStream` | ✅ | ✅ | Real counted iteration with exact full-bank boundaries, restored scratch and physical head advancement; bound(1381+120*(a+d))*volume+23. Descriptor families remain prepared; once-only dimension setup composition separate |
| Actual signed scaling streams from dimensions | `SignedScalingDimensionsStream`, `ActualAffineScalingStream` | ✅ | ✅ | Synthesizes descriptors once and executes actual network scalars on every represented fiber; exact symbols/full-bank output and linear volume plus setup costs. Arbitrary whole-field layout and network scheduling remain separate |
| Reusable translation with generated descriptors | `TranslationExecutionReuse` | ✅ | ✅ | Actual synthesis, rotation and derived-metadata cleanup restore exact recurring bank; initial program starts writable metadata blank. Bound207*Q*B+243 for initial call; changing offsets requires physical preparation |
| Common-offset stream with generated descriptors | `TranslationStream` | ✅ | ✅ | Fixed fourteen-tape machine starts writable metadata blank and performs repeated shifts with all synthesis and cleanup charged; exact final bank and bound461*volume+25. Offset is shared across the family |
| Varying-offset physical preparation composition | `TranslationPreparedFamily` | ✅ | ✅ | Conditional on one actual fixed preparation machine with complete bank contracts; counted execution charges its full preparation sum plus462*volume+23. Concrete offset/spectator preparation remains open |
| Polynomial offset-cost absorption | `OffsetPreparationCost` | ✅ | — | Converts a proved polynomial preparation bound into O(q^width*B), including arbitrary positive varying suffix lengths; does not supply preparation correctness or runtime premises |
| Physical offset descriptor replacement | `BinaryReplace`, `TranslationOffsetReplace` | ✅ | ✅ | Erases old offset, copies physical scheduler output, restores heads and frames; instantiates translation family with all scans charged. Actual control-field scheduler remains a premise |
| Concrete rational scalar offset preparation | `MarkedWordCleanup`, `BinaryDescriptorReset`, `RadixRationalBinary`, `RadixRationalBinaryReuse`, `RationalOffsetPrepare` | ✅ | ✅ | Actual arithmetic, canonical conversion, recurring cleanup and descriptor replacement cost at most67*QB; marked physical source preserved. Denominator below prime q; multi-control combinations and prefix scheduling separate |
| Reusable radix addition | `FamilyPlacementAlphabet`, `RadixAddReusable` | ✅ | ✅ | Physical modular sum with marker setup/removal and restored heads costs2*width+5; consuming temporary operands costs6*width+19. Multi-control expression assembly remains separate |
| Fixed rational linear-combination compiler | `RadixLinearCombination` | ✅ | ✅ | Actual expression/list arithmetic and scratch cleanup, exact modular sum and bound(34*termCount+7)*q^b. Supplied marked source copy per leaf; binary endpoint and physical scheduler refresh remain separate |
| Canonical binary multi-control offset | `RadixLinearCombinationBinary` | ✅ | ✅ | Actual arithmetic→conversion→radix cleanup; exact modular sum, canonical binary and restored scratch. Bound(34*termCount+47)*q^b. Supplied leaf copies and recurring-output preparation remain explicit |
| Physical radix source-copy refresh | `MarkedRadixRefresh` | ✅ | ✅ | Erases stale marked copy, copies physical source and restores both heads; source preserved, bound2*oldWidth+2*sourceWidth+8. Shared-bank expression refresh assembly separate |
| Shared-bank expression source refresh | `SharedPlacementAlphabet`, `RadixLinearCombinationRefresh` | ✅ | ✅ | Actual bounded-reference copies from one preserved control bank; exact leaf synchronization, runtime+1≤leafCount*(4*width+9). Arithmetic/output-reset composition separate |
| Shared-source canonical offset computation | `RadixLinearCombinationShared` | ✅ | ✅ | Actual refresh→arithmetic→binary conversion with exact source/scratch preservation and O(q^b) bound. Finite physical source bank; leaf sentinels and blank output remain explicit preconditions |
| Blank-workspace multi-control preparation | `RadixLinearCombinationBootstrap` | ✅ | ✅ | Physically initializes every leaf sentinel and computes canonical binary offset from shared controls; all expression/converter scratch starts blank, with charged O(q^b) bound. Source bank and recurring-output composition separate |
| Concrete rational-controlled fiber translation | `RationalTranslationExecution` | ✅ | ✅ | Sixteen-tape arithmetic→conversion→replacement→rotation→cleanup with exact recurring bank and bound516*QB. Physical radix control preserved; varying-prefix stream and multi-control combinations separate |
| Concrete cyclic-control translation stream | `RationalTranslationStream` | ✅ | ✅ | Actual rational preparation, translation and radix increment inside counted execution; exact bank and cyclic offset semantics, bound534*volume+23. Explicit marked initial bank; mixed-prefix/layout assembly separate |
| Translation with multi-field prefix increment | `RationalPrefixTranslationExecution` | ✅ | ✅ | Concrete offset/translation plus actual carry scheduler, arbitrary fixed nonempty duplicate-free field order and spectator widths; exact bank and516*QB+1+stepCost. Repeated-family/layout assembly separate |
| Mixed-prefix rational translation stream | `RationalPrefixTranslationStream` | ✅ | ✅ | Real repeated translation and amortized multi-field carries; full prefix period restores fields with bound(536+4*c)*volume+23. Arbitrary radix-word spectator widths; initialization/whole-array layout assembly separate |
| Physical controlled-shift address bridge | `RationalTranslationAffineBridge` | ✅ | ✅ | Exact transported symbols and OrderedAffine.shift semantics for represented cyclic-control fibers, specialized to actual Shared50 coefficients. Whole multidimensional layout construction remains separate |
| Whole-array fiber/address semantics | `PrefixAddressData`, `FiberLayoutData` | ✅ | — | Constructs fibers from a flat array, proves exact flattening and suffix-preserving shifts; actual zero-start prefix counters agree with lex addresses and selected controls. Runtime/layout composition remains separate |
| Physical flat-array controlled shift | `FlatControlledShift` | ✅ | ✅ | Constructs actual fibers from the flat array; concrete rational/control/carry execution transports every symbol with bound(536+4*c)*volume+23. Canonical dimensions and marked zero prefix/work bank remain prepared inputs |
| Initialized prefix-to-flat-shift execution | `PrefixCounterInitPlacement`, `RationalPrefixTranslationInit` | ✅ | ✅ | Physically initializes blank prefix fields/clocks and runs whole-array shift on shared tapes; exact symbols and linear volume plus fixed setup. Canonical dimensions and fixed translation metadata markers remain supplied |
| Radix control enumeration | `RadixCounterData`, `RadixCounter` | ✅ | ✅ | Literal increment with restored head, exact enumeration/wraparound and preserved frames; full finite traversal at most8*q^width steps. Initialization and mixed-field scheduler remain separate; cyclic controller is not a halting program |
| Multi-field radix prefix enumeration | `PrefixCounterData`, `PrefixCounter` | ✅ | ✅ | Concrete carry/rewind scheduler for fixed field count and arbitrary radix widths; exact lexicographic enumeration, preserved frames, cost(4*c+2)*n+2*sum(widths). Initialization, arbitrary non-power range sizes and translation-loop assembly separate |
| Radix field initialization | `RadixZeroFill` | ✅ | ✅ | Constructs a zero field on blank tape from a physical binary width, including all marker writes and head returns; bound15*width+28 for canonical descriptor. Multi-field placement is separate |
| Prefix field-bank initialization | `PrefixCounterInit` | ✅ | ✅ | Constructs every zero prefix field from canonical tape widths, preserving descriptors; exact physical projection to scheduler bank and cost15*sum(widths)+29*fieldCount. Full translation-bank assembly separate |
| Counted iteration with radix alphabets | `CountedLoopAlphabet`, `CountedLoopReuseAlphabet` | ✅ | ✅ | Actual arbitrary-alphabet body, isolated binary controls, exact full-bank loop contract; preparation/countdown/cleanup charged. Enables radix scheduler composition without decoding foreign body symbols |
| Radix-to-binary amortization | `RadixToBinaryData` | ✅ | ⬜ | Countdown borrow potential and binary carry work bounded by12*q^width+2, with exact canonical output value. Literal conversion machine and its charged execution remain separate |
| Literal radix-to-binary conversion | `RadixToBinary` | ✅ | ✅ | Three-tape eighteen-state converter starts work blank, restores source and scratch, produces canonical binary and charges setup/countdown/cleanup. Bound16*q^width+14; fixed-rational/translation pipeline assembly remains separate |
| Repeated scaling with generated descriptors | `ScalingPreparedStream` | ✅ | ✅ | Actual descriptor synthesis runs once, followed by a complete reusable fiber-family scaling machine; only canonical Q/B/family-count inputs supplied. Volume-linear bound for nonempty families includes all setup |
| Repeated reusable positive-unit scaling | `ScalingStream` | ✅ | ✅ | Exact uniform-fiber scaling with shared restored buffers and real reinitialization, fixed control and linear total-volume execution. Binary descriptors remain prepared |
| Literal inverse-unit scatter | `ScalingScatter` | ✅ | 🟡 | Actual selected-buffer block routing has exact inverse-scaling piece semantics and linear-volume execution. Physical concatenation and full reusable inverse wrapper remain open |
| Complete literal positive-unit scaling | `ScalingExecution`, `ScalingBuffersReset` | ✅ | 🟡 | Split, real rewinds and merge compose into exact multiplication of block addresses with linear volume cost and fixed control. Buffer restoration is separately proved; initializer/cleanup wrapper and descriptor construction remain open |
| Repeated reusable coordinate negation | `NegationStream` | ✅ | ✅ | Literal uniform-fiber negation restores shared scratch and all controls; exact map-negate payload and linear-volume bound proved. Derived descriptors remain prepared |
| Actual scaling residue initialization | `OneHotCount`, `ScalingControlInit` | ✅ | ✅ | Constructs modulus and zero-current residue banks from arbitrary cells with charged linear-Q execution and restored clock; the binary Q descriptor remains prepared |
| Fully reusable coordinate negation | `BlockNegationReuse` | ✅ | ✅ | Literal single-fiber machine restores scratch including its head and both clocks, preserves descriptors and has actual bound 210 times volume plus 219. Repetition across fibers and descriptor synthesis remain separate |
| Literal positive-unit split and merge | `ScalingSplit`, `ScalingMerge`, `ScalingPieceBridge` | ✅ | 🟡 | Each fixed-coefficient machine has proved linear-volume execution, and exact payload representations match. Actual split-to-merge head rewinds, assembly and descriptor preparation remain separate |
| Literal residue control and scratch cleanup | `OneHot`, `CountedErase` | ✅ | ✅ | Fixed one-hot residue increment takes one real step; delimiter-free scratch erasure has linear cost with full clock cleanup. Integration into scaling and reusable negation remains open |
| Reusable block reversal and scratch reset | `BlockReverseStreamReuse`, `ScratchReset` | ✅ | ✅ | Blockwise reversal preserves both immutable descriptors and clears both clocks. Scratch erasure also physically restores its head; linear volume bounds include all seeks and joins. Composition into coordinate negation remains open |
| Literal single-fiber controlled block shift | `CountedRotate` | ✅ | ✅ | Six tapes, sixty-four states; exact shifted payload with source/descriptor preservation and empty final clock. All moves and joins bounded by fifteen times payload volume plus descriptor widths; descriptor synthesis and multi-fiber scheduling remain open |
| Repeated common-offset fiber shifts | `CountedRotateAdvance`, `WordSegments`, `FiberShift` | ✅ | ✅ | Fixed seven-tape controller, source preservation, heads advance full volume, inner controls restored. Actual time at most 177 times volume plus four for canonical prepared descriptors and nonempty fibers; varying offsets and outer clock setup/cleanup remain open |
| Actual affine coefficient unit recipes | `Shared50AffineCoefficients` | ✅ | 🟡 | Every coefficient has a verified exact-width arithmetic kernel; every actual scale has proved signed numerator/denominator unit recipe at the chosen prime. Positive unit-scaling payload split/merge remains open |
| Literal block-preserving coordinate negation | `BlockReverseAdvance`, `BlockReverseStream`, `BlockNegation` | ✅ | ✅ | Full first-block-preserving negation through two actual reversals; runtime at most 200 times volume plus 128. Source/descriptors preserved, dirty scratch and consumed outer count tracked; repetition and their cleanup remain separate |
| Reusable fiber shifts with full clock cleanup | `CountedLoopReuse`, `FiberShiftReuse`, `FiberShiftAddress` | ✅ | ✅ | Literal outer-clock preparation/erasure and immutable descriptor preservation. Repeated common-offset target-coordinate translation has actual cost at most 182 times volume plus twenty-three; derived descriptors and varying offsets remain open |
| Actual scalar-affine physical schedules | `AffineFieldProgram`, `Shared50AffineControl` | ✅ | ⬜ | Fixed rational expanded schedules specialize at every width, preserve every physical edge and exact recursive call count, and have proved diagonal-unit legality. Tape routines and scheduling remain open |
| Canonical length descriptor bootstrap | `GrowingCounterData`, `GrowingCounter`, `BinaryLength`, `BinaryLengthInit` | ✅ | ✅ | Growing counter needs no preset width; blank-work-tape setup and source scanning cost at most eight times source length plus two. Includes standard multiplication input; nonblank source segment required |
| Literal binary-counted body loop | `CountedLoop` | ✅ | ✅ | Fixed finite control executes arbitrary proved body chains; all body costs plus linear iteration/clock overhead, including true terminal halt. Outer clock preparation/cleanup remains explicit |
| Ordered-affine matrix decomposition | `OrderedAffine` | ✅ | ⬜ | Descending row schedule of diagonal units and earlier-control shifts exactly realizes every invertible lower-triangular transform; coefficient reduction preserves order and introduces no new coefficients |
| Counted positioning and general tape placement | `CountedSeek`, `Placement` | ✅ | ✅ | Raw forward/backward head movement preserves every payload cell and restores reusable controls; generic selected tape-bank lifting preserves exact runtime and the complete frame |
| Reusable binary-counted raw transfer | `CountedCopyReuse` | ✅ | ✅ | Immutable descriptor preserved; clock preparation, full erasure, control-head resets and all joins charged. Runtime at most five times count plus seven times width plus sixteen; descriptor construction remains separate |
| Literal binary addition | `BinaryAdd` | ✅ | ✅ | Three tapes and three states; exact sum in at most width plus one transitions; equally padded operands required |
| Literal binary subtraction | `BinarySub` | ✅ | ✅ | Three tapes and two states; exact width runtime, modular difference and final borrow; equally padded operands required |
| Binary operand padding | `BinaryPad` | ✅ | ✅ | Two tapes, one state, exact maximum-width runtime; values preserved; heads finish at common end |
| Addition with operand preparation | `BinaryArithmetic` | ✅ | ✅ | Raw unequal widths; physical padding, rewind and addition with both joins; runtime ≤ three times maximum width plus five |
| Literal fixed-radix modular addition and subtraction | `RadixDigits`, `RadixAdd`, `RadixSub` | ✅ | ✅ | Finite digit alphabet and two carry/borrow states, three tapes; exact width runtime and halt, canonical modular output and final carry/borrow, complete source preservation; equally padded operands required |
| Literal fixed-coefficient scaling and modular division | `RadixUnary`, `RadixScaleData`, `RadixScale`, `RadixDivisionData`, `RadixDivide` | ✅ | ✅ | Fixed finite-state two-tape digit transducers, exact one transition per digit, actual halt and complete source preservation. Natural scaling and positive-denominator division below a fixed prime radix have proved modular arithmetic and final carry; full rational coefficients are proved separately; matrix composition remains open |
| Literal rational-coefficient multiplication | `RadixRationalData`, `RadixRational` | ✅ | ✅ | Arbitrary signed rational coefficient below the fixed prime denominator bound; fixed finite carry states, two tapes, exactly one transition per digit. Output equals the network coefficient ratMod times the input at the exact word modulus; halting/source preservation proved. Matrix composition and address-array permutation scheduling remain open |
| Actual network coefficient kernels | `Shared50CoefficientMachines` | ✅ | ✅ | Every actual transform coefficient meets the chosen prime denominator bound; literal exact-width kernels implement its reduced entry. Full matrix sweeps and implicit-address payload permutations remain open |
| Leading-bit stable partition | `Partition`, `PartitionMarked` | ✅ | ✅ | Sentinel-marked variant composes |
| Concatenation and record reinsertion | `Concatenate`, `Reinsert` | ✅ | ✅ | Source positioning is a precondition |
| One complete radix pass | `PartitionPass` | ✅ | ✅ | Runtime `3·len + 8` |
| Radix sort (list level) | `RadixSort`, `PartitionSort` | ✅ | — | Stable LSB sort, volume identity |
| Key-bit selection for later passes | `KeySelectData`, `KeySelect` | ✅ | ✅ | Unary tape selects arbitrary valid index; exact runtime ≤ three input volumes |
| Flag removal and source erasure | `DropFlag` | ✅ | ✅ | Exact flagged volume; arbitrary records; restores empty marked source |
| Arbitrary-key flagged stable pass | `KeyPartition` | ✅ | ✅ | Six tapes, fifteen states; exact runtime ≤ eleven raw volumes plus twelve |
| Arbitrary-key raw stable pass | `KeyPass` | ✅ | ✅ | Seven tapes; output flags removed; exact runtime ≤ seventeen raw volumes plus nineteen |
| Reusable stable pass and cleanup | `Erase`, `KeyPassReuse` | ✅ | ✅ | Exact fresh physical bank restored; runtime ≤ twenty-six raw volumes plus forty-one |
| Full tape radix sort | `UnarySelector`, `TapeRadixSort` | ✅ | ✅ | Fixed eight-tape machine, exact sort, runtime ≤ 74 × width × volume; prepared width/markers are preconditions |
| Terminating stream scheduler | `CountedLoop`, `CountedLoopReuse`, `FiberShiftReuse` | 🟡 | 🟡 | Actual counted bodies and repeated common-offset fibers halt with full clock cleanup; derived descriptor arithmetic and the recursive network scheduler remain open |

## 3. Finite networks with a rank saving (§3)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Scalar cancellation schedule and bank identity | `Scalar` | ✅ | ⬜ | Eight-step dirty scratch, signed exchange |
| Executable linear circuits | `Circuit`, `CircuitRouting` | ✅ | ⬜ | Instruction counts, not wire counts |
| Complex (rational) motif matrices | `CircuitTriples` | ✅ | ⬜ | Exact matrices; dyadic coefficient bounds in `GaussianCircuit` |
| Binary motif matrices over `ZMod 2` | `CircuitBits` | ✅ | ⬜ | Original motif; optimized h=50 replacement is separate |
| Neighbor and wire counts | `NeighborCounts`, `Wires` | ✅ | — | Matches manuscript totals at ground size 100 |
| Degree-one label spaces | `Labels` | ✅ | — | Rational form nondegenerate for size ≠ 9 |
| Tensor-cube label spaces | `TensorLabels` | ✅ | — | Nondegeneracy, dimension, terminal line/complement decomposition |
| Framed circuit compilation | `FramedCircuit` | ✅ | ⬜ | Full finite-circuit common-frame identity, including spectators; exact operators |
| Global circuit with per-invocation scratch | `GlobalCircuit`, `GlobalCircuitBits` | ✅ | ⬜ | Complete three-coordinate scalar schedule and restoration; grouped topology separate |
| Sparse grouped motif gates | `GroupedCircuit` | ✅ | ⬜ | Exact support, eight-row semantics and framed refinement; full grouped exchange separate |
| Binary orthonormalization | `BinaryOrthonormal` | ✅ | — | Nonalternating nondegenerate forms; local witnesses and full global edge coverage proved |
| Local grouped inverse and exchange | `GroupedRouting` | ✅ | ⬜ | Bit/rational semantics and exact support transport; globally embedded by `GlobalGrouped` |
| Neighbor residuals and binary units | `NeighborResidual` | ✅ | — | Actual pair-complement dimension and bases; coordinate witnesses for tensor-line complements |
| Global grouped schedule | `GlobalGrouped` | ✅ | ⬜ | Physical scratch per invocation, middle inverse, sparse support transport and counts |
| Embedded tensor subspaces | `TensorSubspace` | ✅ | — | Actual dimensions, nondegeneracy, orthogonality and sum/inclusion laws |
| Binary diagonal phase decomposition | `BinaryPhase` | ✅ | ⬜ | Rank-one residual and weight-mod-four factorization; Walsh conjugation separate |
| Binary tensor coordinate bridge | `TensorCoordinates`, `LabelTransport` | ✅ | — | Actual isometry to h³ bits; transports labels, residuals and projections |
| Local nested gate labels | `MotifLabels` | ✅ | — | Actual tensor subspaces and unique central decrease; future factor and scratch endpoints included |
| Projection-rank trace accounting | `RankTrace` | ✅ | — | Actual edge ranks telescope; global physical instantiation in `GlobalProjectionRank` |
| Binary one-column translation interface | `BinaryWalsh` | ✅ | ⬜ | Exact finite Walsh conjugation and residual-dimension kernel sequence |
| Full grouped frame compiler | `GroupedFrames` | ✅ | ⬜ | Scalar array identity and actual label history linked to projection-rank balance |
| Stage boundaries and terminal labels | `StageLabels` | ✅ | — | Actual isometries and all X/Y interstage and source/sink identities |
| Sparse physical motif incidences | `MotifSupport` | ✅ | — | Concrete nonzero coefficient/owner tests and central support |
| Binary multi-column interface | `BinaryColumns` | ✅ | ⬜ | Concrete slice operators and exact residual-dimension factor count; unit premise explicit |
| Local residual formulas and binary units | `MotifResiduals`, `BinaryMotifResiduals` | ✅ | — | Thirteen local comparisons plus future/sink at all three stages; physical sparse-history coverage in `GlobalBinaryResiduals` |
| Exact Gaussian-dyadic arithmetic | `GaussianDyadic`, `GaussianCircuit` | ✅ | ⬜ | Concrete motif coefficients, grouped updates, and both binary edge directions; denominator growth proved, numerator bounds in `GaussianPrecision`; tape costs open |
| Binary interface numerator bounds | `GaussianPrecision` | ✅ | ⬜ | Actual kernels and both projection-edge directions; explicit scale and integer numerator bounds |
| Physical local label histories and loss | `LabeledMotif` | ✅ | — | Forward/opposite sparse histories; comparable nondegenerate edges, loss ≤ central count × current dimension, including sinks |
| Rational negative-source correction | `SignedProjection` | ✅ | — | Exact extra source rank for arbitrary nested first label, including skipped vertices |
| Global physical label attachment | `GlobalLabels`, `GlobalLabelsNondegenerate` | ✅ | — | Exact schedule erasure, physical endpoints/stage boundaries, all vertex labels nondegenerate |
| Sparse skipped-edge binary units | `GlobalLabelsResiduals` | ✅ | — | Actual witnesses for xIn→full, yIn→yOut, bot→full, including future factor |
| Physical invocation rank loss | `GlobalRank` | ✅ | — | Actual embedded histories, comparable edges and loss bound; supports weaker input labels left by sparse predecessors |
| Full labeled trace assembly | `GlobalRankStages`, `ProjectionTrace`, `GlobalProjectionRank` | ✅ | ⬜ | Actual global comparable nondegenerate edges, loss bound and projection-rank balance, including terminal alignment |
| Terminal dimension and budget arithmetic | `NetworkBudget` | ✅ | — | Actual source/sink sums and h=25 role count; trace balance/loss premises discharged for h=25 by `ComplexRank25` |
| Orthogonal residual and projection rank | `ProjectionRank` | ✅ | — | Nested nondegenerate labels give actual projection-difference rank |
| Residual rank saving | `ComplexRank25`, `GlobalBinaryResiduals`, `ComplexPhaseBudget` | ✅ | — | Actual h=25 rank sum, full binary residual-factor coverage and uniform complex edge-factor budget proved; optimized h=50 rank bound is proved in Shared50GlobalShear |
| Improved h=50 bit network | `SharedPointMap`, `SharedPointKey`, `SharedPointIntern`, `DisjointCircuit`, `DisjointPruning`, `DisjointBuilder`, `ReversibleFanout` | ✅ | ⬜ | Exact shared-point map, compressed-key interning, output-preserving active-node pruning, DAG primitives and reversible fanout proved; full literal paired-exclusion recursion and concrete 49-vertex input/output semantics proved; the independent checked local witness has 9,813 additions and 1,176 outputs; global sharing counts and actual finite scalar execution are now certified; full global rank, signed physical shear and modular execution are proved for the selected tau; literal tape costs remain open |
| Exclusion-circuit building blocks | `DisjointBalanced`, `DisjointExclusion`, `DisjointPaired` | ✅ | ⬜ | Literal balanced totals, shared prefix/suffix leave-one-out sums and weighted base-case query batches; exact support/value preservation and node upper bounds, not the optimized certificate count |
| Paired-exclusion reconstruction | `PairedPartition`, `PairGrouping`, `PairedReconstruct` | ✅ | ⬜ | Literal pair grouping and recursive decrease; actual single/pair smart-add reconstruction with exact supports and node bounds; full recursive DAG assembly is proved in PairedBlockCorrect; optimized counts remain open |
| Literal paired recursion and query semantics | `PairedCircuit`, `PairedGraphSpec`, `PairedVectorCorrect`, `SupportInterpretation`, `PairedCoarseSupport`, `PairedCoarseCorrect`, `PairedQuerySupport`, `PairedCoarseQuery`, `PairedStripCorrect`, `PairedStripSupport`, `PairedCircuitCorrect`, `PairedReconstructionSupport`, `PairedReconstructionKeys`, `PairedBlockCorrect`, `PairedInitialGraph` | ✅ | ⬜ | Full literal recursion proved correct by strong induction; concrete 49-vertex graph has exact output sums and 1,176 inputs/outputs; active addition and global sharing counts remain separate |
| Interning invariants and certificate checking | `DisjointUnique`, `PairedUnique`, `DuplicateBudget`, `SharedPointMatching`, `MaskDAG`, `MaskSignature`, `MaskUnique`, `PairMask` | ✅ | — | Full recursive support uniqueness; matching-based sharing bound and sound bitmask/signature/uniqueness checkers; concrete local counts, signatures and all 40,256 global duplicate witnesses kernel-checked |
| Checked local 49-vertex witness | `Paired49Certificate`, `Certificates/Paired49/*` | ✅ | ⬜ | All pair-exclusion outputs, 9,813 additions, unique supports, exact endpoint signatures and at most 10,989 compiled scalar roles; independent certificate, not a proof of generator trace equality |
| Actual common-point support family | `SharedPointLift`, `SharedPointFamily` | ✅ | — | Exact local-to-global core/union formulas and 490,650 actual local additions across fifty copies; matching structural hypotheses and all 40,256 genuine duplicate witnesses proved |
| Actual globally interned circuit | `DAGReplay`, `DAGReplayBudget`, `SharedPointOutputMap`, `SharedPointReplay`, `SharedPointExecution`, `SharedPointOutputIndex`, `Shared50Certificate`, `Shared50Finite`, `BoundedCircuit`, `DAGFiniteCompile` | ✅ | ⬜ | Actual fifty-copy DAG and finite scalar program with 58,800 exact outputs, at most 450,394 additions, 509,194 roles and 959,588 XOR updates; every finite-count premise discharged |
| Reversible DAG role allocation | `DAGAllocator`, `DAGAllocatorCount`, `DAGAllocatorFrontier`, `DAGConsumers`, `DAGAllocatorRun`, `DAGCompileCorrect`, `DAGAllocatorBudget`, `DAGValueTransfer`, `DAGInstructionCount`, `Paired49Execution` | ✅ | ⬜ | Actual compiler has exact role and scalar-instruction counts, valid bounded shared-pivot layouts, executable reverse and proved output values from actual input initialization; forward support-frame nesting is proved; reverse/global assembly is proved; tape execution remains open |
| Shared-point source spans | `SharedPointLabels` | ✅ | — | Actual rational spans are positive definite and nested; no nondegeneracy hypothesis |
| Actual forward shared-point frames | `FanoutFrames`, `DAGSupportTrace`, `SharedPointOutputLabels`, `Shared50Frames`, `DAGFramedExecution` | ✅ | ⬜ | Actual interleaved frame/scalar execution on arbitrary module states; increasing nondegenerate support labels and zero forward loss, with exact orthogonal output spans; complementary reverse middle frames proved separately; full motif and global rank assembly proved separately |
| Actual complementary inverse frames | `DAGComplementTrace`, `DAGComplementExecution` | ✅ | ⬜ | Exact reversed-complement labels, increasing edges, zero loss and arbitrary-module inverse execution; actual sinks, full invocation and global assembly proved separately |
| Shared circuit stage frames and physical attachments | `DAGSourceRoles`, `Shared50InitialLabels`, `Shared50OutputRoles`, `Shared50ComplementFrames`, `Shared50StageFrames`, `Shared50FiniteTrace` | ✅ | ⬜ | Actual finite forward/reverse middle traces lift into stage tensor labels with exact endpoints, nondegeneracy and zero loss; input/output physical owners and attachment inclusions are proved; whole invocation and global rank assembly proved separately |
| Actual finite physical middle schedules | `BoundedFramedCircuit`, `Shared50FiniteFramed`, `Shared50FiniteReverseTrace` | ✅ | ⬜ | Physical forward and complementary inverse instructions on the certified finite bank preserve exact scalar erasure and arbitrary-module frame identities; full invocation/global physical assembly remains separate |
| Complete optimized local label histories | `Shared50LabeledInvocation`, `Shared50InvocationRank`, `Shared50OppositeLabels`, `Shared50OppositeRank` | ✅ | ⬜ | Actual forward/opposite finite middle traces plus all sparse-block boundary alignments; exact endpoints, nested nondegenerate edges and loss exactly 2,500 each, including common-input scratch. Exact physical-wrapper linkage is proved; global rank assembly remains separate |
| Complete optimized physical local wrappers | `FramedBlocks`, `FramedEdgeTrace`, `Shared50BlockFrames`, `Shared50FramedInvocation`, `Shared50PhysicalEdges`, `Shared50InvocationPhysicalEdges`, `Shared50OppositeBlockFrames`, `Shared50FramedOpposite` | ✅ | ⬜ | Literal forward/opposite physical programs have exact sparse scalar erasure, arbitrary-module frame identities and exactly the ordered edges of the local rank histories; global physical assembly and tape costs remain open |
| Actual optimized projector operators and global boundaries | `Shared50InvocationProjectionRank`, `Shared50GlobalTrace` | ✅ | ⬜ | Every local physical edge is certified by its genuine rational projector-difference matrix and actual range-rank balance; all reused global boundary attachments have exact endpoints, nondegeneracy and zero loss. Full global trace assembly is proved separately |
| Complete optimized global projection-rank trace | `Shared50GlobalTracePlacement`, `Shared50GlobalTraceNondegenerate`, `Shared50GlobalTraceStages`, `Shared50GlobalProjectionRank` | ✅ | ⬜ | Actual reused three-stage trace reaches the prescribed sinks with nested nondegenerate edges and exact total loss; genuine projector range ranks plus the source correction meet the exact improved rank budget and strict branching bound. Full signed physical interface is proved separately; tape realization remains open |
| Complete optimized signed physical shear | `Shared50GlobalFramed`, `Shared50SignedBoundary`, `Shared50ShearEndpoints`, `Shared50GlobalShear` | ✅ | ⬜ | Actual signed physical two-bank program has exact scalar erasure, uniform full rational address shear on arbitrary binary arrays including dirty scratch, and ordered genuine projector-matrix certificates. The exact total range-rank budget satisfies strict branching; finite-radix realization and tape costs remain open |
| Actual optimized modular edge schedule | `Shared50OperatorPairs`, `Shared50ModularOperators`, `ModularFrameSchedule`, `ModularProgramShape`, `Shared50ModularSchedule` | ✅ | ⬜ | Concrete basis and actual matrix pairs; one good prime works at every radix exponent, preserving routed endpoint identities and exact interchange budget. Each edge reduces one fixed rational program with exact field-operation count; full modular physical assembly is proved separately; tape costs remain open |
| Complete optimized modular physical execution | `Shared50SignedFramed`, `Shared50ModularExecution`, `Shared50ModularControl` | ✅ | ⬜ | One fixed prime, every radix exponent, arbitrary finite arrays including dirty scratch: exact routed full shear, actual ordered field programs and the certified interchange budget. Canonical controls reduce fixed rational instructions with exact field-operation counts and lower-triangular transforms; literal tape execution remains open |
| Complete optimized finite address interchange | `Shared50FiniteInterchange` | ✅ | ⬜ | Literal pre/post field programs around the actual network give full coordinate-group interchange on every routed array including dirty scratch. Ordered physical field certificates, exactly the improved recursive interchange count, and fixed rational instruction shape are proved; tape execution remains open |
| Actual optimized dirty invocation | `DirtyLinearCircuit`, `Shared50Dirty`, `Shared50Invocation`, `Shared50Exchange` | ✅ | ⬜ | The actual shared program plus fifty central sums executes the twelve-block identity shear, its inverse and local three-invocation exchange, restoring arbitrary scratch; global reused scalar schedule is proved separately; rank assembly is proved separately |
| Sparse optimized invocation | `SparseCircuit`, `Shared50SparseIO`, `Shared50SparseCentral`, `Shared50SparseInvocation` | ✅ | ⬜ | Actual source/readout/central XOR lists with exact incidences and dense-matrix equivalence; sparse twelve-block shear, inverse and local exchange restore dirty scratch; at most 5,209,540 scalar instructions per invocation, not tape steps |
| Optimized stage-reuse matching and labels | `TripleNeighborPermutation`, `Shared50ReuseLabels` | ✅ | ⬜ | Hall-selected actual neighbor bijection, nested nondegenerate stage boundary joins, zero join loss and exact 125,000 rank saving per joined role; reused scalar schedule proved in Shared50GlobalCircuit; global rank trace is proved in Shared50GlobalTraceStages |
| Optimized two-bank endpoint and numerical budgets | `Shared50GlobalBudget`, `Shared50Parameters` | ✅ | — | Actual padded two-bank world count and rational terminal dimension totals; strict branching inequality for the numerical rank budget. Actual trace balance and loss premises are discharged in Shared50GlobalProjectionRank |
| Actual optimized two-bank global program | `Shared50GlobalCircuit` | ✅ | ⬜ | Literal sparse three-coordinate schedule, exact first/third scratch reuse, injective per-stage placements, full data-bank exchange and arbitrary scratch restoration; exact scalar list counts. Physical projector-rank assembly is proved in Shared50GlobalShear; tape costs remain open |
| Rational address-shear interface | `ProjectionRank`, `ShearFrame` | ✅ | ⬜ | Projection ranks, full signed physical frames, finite-radix realization and actual total budget proved; tape realization remains open |
| Phase interfaces and tape compilation | `BinaryRankFactors`, `ComplexPhaseBudget`, `BinaryColumnFrame`, `GroupedModuleFrames`, `FramedFactorExecution`, `ComplexFramedExecution`, `TensorTerminalWeight`, `ComplexEndpoints`, `ComplexCorrections` | ✅ | ⬜ | Complete physically placed array-factor run with explicit character/phase corrections equals the full coordinate transform on data and dirty scratch, uniformly in columns; internal instruction count includes all scalar gates; the corrections are literal single-wire instructions (27 sign factors per X input, 28 per Y output, one negation per X output, i.e. 28 per data wire beyond the rank total) and every vector factor expands into its per-column Gaussian-dyadic kernels `aI + bX_v` (k per factor, 54k+2 corrections per address); literal tape costs remain open |

## 4. Faster interchange of address chunks (§4)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Interchange recurrence and padding arithmetic | `Recurrence` | ✅ | — | `F k ≤ K (m^k)^τ` from `s/W ≤ m^τ`; digit pieces `O(e^τ)`; row, row-range, and radix padding bounds |
| Lower triangular factorization (Lemma 4.1) | `LowerTriangular`, `PivotRank` | ✅ | — | `A = E₁ Π E₂` with lower triangular two-sided inverses and a partial permutation `Π` with exactly `rank A` ones |
| Rational matrix shear (Lemma 4.2) | `Shear`, `Modular` | ✅ | ⬜ | Pivot programs, descending triangular updates, prime modulus beyond all denominators, shear modulo `q^b` with exactly `rank A` interchanges; tape cost of the linear operations open |
| Power-width interchange (Prop 4.3) | `Interchange` | ✅ | ⬜ | Three-step interchange, routed frame identity under the shear contract, edge schedule with `Σ rank` interchanges, recursion `O(V (m^k)^τ)`; role-stream split and fixed-tape schedule open |
| Arbitrary-width interchange (Lemma 4.4) | `Recurrence`, `ArbitraryWidth` | ✅ | ⬜ | Row-range digits, row padding, radix padding, and the total `O(u^τ)` per unit volume with an explicit constant; field-order bookkeeping open |

## 5. Simultaneous butterfly layers with compact control (§5, §11, CrocSwap)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Radix packing and signed packed additions | `Radix` | ✅ | ⬜ | |
| Dirty-temporary control identities | `DirtyControl` | ✅ | — | Universal integer statements |
| Packed control gadgets | `PackedControl` | ✅ | ⬜ | Slot embedding and tape costs open |
| Ideal toggle permutation and invertibility | `Ideal`, `Permutations` | ✅ | — | Every address, including bad ones |
| Exact destination repair | `Repair`, `ExactRepair` | ✅ | ⬜ | |
| Exceptional-address counts and density | `Counting`, `Density`, `RepairBounds` | ✅ | — | Bound `5 / (128 p³)` |
| Row layout and reservation capacities | `Layout` | ✅ | ⬜ | |
| Extract, sort, reinsert repair records | `Partition`, `Reinsert`, `StripPrefix`, `ReturnOrigin`, `RepairStage`, `FlagCopy`, `MarkedReturn`, `LoopChain`, `RepairScan` | ✅ | ✅ | Extraction/sorting/reinsertion primitives done; the list-level composition is `RepairPipeline`; one fixed fourteen-tape machine scans the stream with a binary rank counter, flags each record from a key tape, extracts flagged records in the raw keyed format, returns both heads, then sorts, strips and reinserts, with an exact-run contract; the per-record key routine (membership test and destination-rank bits) is a program parameter with a per-rank contract, and the whole costs its key cost plus ten per record, three stream volumes, `74k+5` extracted volumes, `2k+3` per extracted record and `k+14` |
| Assembled repair pipeline with cost | `RepairPipeline`, `TapeRepairStage`, `TapeRepair` | ✅ | 🟡 | Flag, extract with destination ranks, radix sort, reinsert gives the ideal stream for both packed programs; extracted count is the exceptional fraction times the volume; cost expression at most three volumes; the full scan-sort-reinsert machine runs on literal tapes from the unflagged actual stream and leaves the ideal stream on the output slot within `M·(c_K+10)` plus three stream volumes plus `(74k+5)·|ℬ|·(k+2+w)` plus `(2k+3)·|ℬ|` plus `k+14`, where `c_K` bounds the key routine; the key routine's arithmetic on tapes (membership in `ℬ`, reversal of the eight modular additions, rank differences) is the open content |

## 6. Synthetic transforms and their tape layout (§6)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Principal roots and synthetic ring | `Synthetic`, `SynthConv` | ✅ | — | `ℂ[y]/(yʳ + 1)` |
| Synthetic FFT with shift twiddles | `SynthFFT`, `SynthMultiD` | ✅ | ⬜ | One and `d` dimensions, error `n ε` |
| Complex-to-synthetic embedding | `SynthEmbed` | ✅ | — | Twist is an isometry |
| Bluestein reduction | `Bluestein`, `BluesteinApprox` | ✅ | ⬜ | |
| Tape layout and costs | `LayoutCost` | ✅ | ⬜ | Prefix slots `≤ dK`, chunk reorder by `≤ Dq−1` exchanges costing `≤ dℓK^(τ−1)`, exactly `ℓ` rounds with error `ℓ√2·2^(-p)` in the disk, descriptor length `≤ C_desc p`, bracket equals four cost-table rows; `K < ℓ` eventually |

## 7. Gaussian resampling (§7)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Gaussian sums and Poisson summation | `Gaussian` | ✅ | — | |
| Resampling identity (Thm 4.2) | `Resampling`, `ResamplingCLM` | ✅ | — | |
| Norm bound on `S` (Lemma 4.5) | `ResamplingNorm` | ✅ | — | `‖S‖ ≤ 1 + 1/α` |
| Inversion of `T` (Lemma 4.6, Prop 4.7(i)) | `ResamplingInverse`, `ResamplingAssembly`, `Neumann` | ✅ | — | `F_s = 2^γ B F_t A`, `‖A‖, ‖B‖ ≤ 1` |
| `d`-dimensional resampling (Thm 4.1) | `ResamplingMulti` | ✅ | — | |
| Truncation and Neumann errors (Lemmas 4.8–4.12) | `ResamplingApprox`, `OffDiagApprox`, `OffDiagApproxSqrt`, `NeumannApprox` | ✅ | — | Square-root windows as in the paper |
| Numerical `Ã`, `B̃` (Prop 4.7(ii)) | `ResamplingNumeric`, `ResamplingMultiNumeric`, `ExplicitNumeric` | ✅ | ⬜ | Explicit maps with error below `p²` in one dimension and `d p²` in `d`, no side conditions |
| Permutation-left variant | `ResamplingPermuted`, `ResamplingPermutedNumeric` | ✅ | ⬜ | `P_s F_s = 2^γ B₀ P_t F_t A` in one and `d` dimensions with explicit clamped `Ã`, `B̃₀` of error below `p²` per coordinate; weighted chirp for the retained frequency permutation; source permutation cancels in convolutions |
| Tensor interface line counts (Lemma 7.2 costs) | `LineCost` | ✅ | ⬜ | Linewise sums give `d C T X`, the Gaussian row times `T p`; at most `2 d T / r` lines; polynomial setup per line is `o(T p)` |

## 8. `O(n log n)` subroutine (Harvey–van der Hoeven)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| DFT, convolution theorem, inversion | `DFT`, `Multidim`, `MultidimD`, `CRTMulti` | ✅ | — | |
| Radix-2 FFT and normalized FFT | `FFT`, `NormFFT` | ✅ | ⬜ | Ring-operation counts only |
| Fixed-point framework and error budget | `FixedPoint`, `FixedOps`, `Approx`, `ErrorBudget` | ✅ | — | |
| Tensor approximation lemma | `TensorApprox`, `TensorApproxD`, `TensorApproxV` | ✅ | — | Rectangular composition law open |
| Plain FFT multiplier | `Pipeline`, `Multiplier`, `Kronecker`, `Carry` | ✅ | ⬜ | Exact on bit strings |
| Negacyclic Kronecker substitution (Lemma 2.5) | `NegacyclicKronecker` | ✅ | ⬜ | Exact arithmetic; bit costs open |
| Power-of-two transforms (Thm 3.1) | `SynthEmbed`, `SynthMultiD`, `PowerOfTwoExact`, `PowerOfTwoExactD`, `PowerOfTwoNumeric`, `PowerOfTwoNumericD`, `SynthConvApprox`, `SynthConvApproxD` | ✅ | ⬜ | Exact chain and numerical error `T′ (3S + 2εa + 4) + εa + 2` in every dimension; packaging as the recursive step's `F̃_t` in progress |
| Steps 1–3 of the recursion (Props 5.2–5.4) | `MainReduction`, `MainStep`, `Section5Approx` | ✅ | ⬜ | |
| Parameter selection and precision | `MainParams`, `PrecisionCheck` | ✅ | — | |
| Final recurrence (Cor 5.5) | `MainRecurrence`, `Recurrence`, `RecurrenceParams` | ✅ | — | Parameter facts at `d = 1729` proved; the recursive inequality for an actual cost is a hypothesis |
| Moduli selection (Lemma 5.1) | `Primes`, `PrimeSelection`, `ModuliConstruction` | ✅ | — | Elementary two-prime-power moduli via pigeonhole, no Chebyshev input; the Chebyshev-bound route is kept as an alternative |
| Assembled numerical transform (Prop 5.2) | `ResamplingMultiNumeric`, `MainTransform`, `ExplicitNumeric`, `ContractPrep`, `PowerOfTwoContract` | ✅ | ⬜ | `F̃_s = 2^γ B̃ F̃_t Ã` with error `2^(γ+4) T log₂ T`; the explicit power-of-two transform meets the `8 T log₂ T` bound |
| Headline recursive-step contract | `Contract`, `ContractSqrt`, `ContractFinal`, `PrimeSelection`, `ModuliConstruction`, `Capstone` | ✅ | ⬜ | The explicit numerical step with the paper's windows is exact with no hypothesis beyond the threshold `n ≥ 2^(2^(1000 d³))`; the capstone ties correctness and the `O(n log n)` operation count to one choice of grids and moduli |
| Operation counts | `CostModel`, `CostBound`, `ResamplingOps`, `SmallMultiplierCost`, `ExpEval`, `ExpCostBound`, `JointRecurrence`, `CostFinal` | ✅ | ⬜ | A full step is `(12 T/r) M(3rp) + O(n log n)` operations with the paper's windows; small products by the plain FFT multiplier, weights by binary splitting; the recurrence closes to `O(n log n)` above `2^(2^624)` |
| Unit-ball clamping | `Clamp` | ✅ | — | Removes the ball side conditions of the composition lemmas |
| Bit costs and tape compilation | — | ⬜ | ⬜ | |

## 9. Exact multiplication, parameters, time bound (§8)

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Parameter slacks and assembly margins | `Parameters` | ✅ | — | Log enclosure proved in Lean |
| Asymptotics and finite-depth recurrence | `Asymptotics` | ✅ | — | |
| Prime existence | `Primes` | 🟡 | — | Short-interval primes open |
| Exact coefficient arithmetic, rounding, carries | `Carry`, `MainReduction`, `ExactRecovery` | ✅ | ⬜ | Carries and packing at the list level; the §8 precision chain from transform errors `E_s` to the exact product, with the margins from the size relations for all large `k` |
| Complete time bound | `TimeBound`, `Sizes`, `CostTable` | 🟡 | ⬜ | Size relations, every table row as a multiple of `p^(1-margin)`, and the assembly into `O(n (lg n)^(1-κ))` at `κ = 83/10^12` proved; the components must still supply the row costs |

## 10. End-to-end theorem `EndToEnd`

| Subcomponent | Files | Mathematics | Tape | Notes |
| --- | --- | --- | --- | --- |
| Explicit multiplication program | — | ⬜ | ⬜ | |
| Correctness on every input length | — | ⬜ | ⬜ | Requires sections 2–9 |
| Uniform runtime `O(n log^(1−83/10¹²) n)` | `Assembly` | 🟡 | ⬜ | `EndToEnd` reduced to a program running within a cost of the cost-table shape |

## Next steps

- Assemble synthesized piece descriptors with repeated scaling, repeat inverse scaling, then compose signed rational scales and computed varying-offset translations.

- Compute repair keys and run extraction, sorting and reinsertion on tapes, with the `RepairPipeline` composition as the specification.
- Compile the proved optimized h=50 modular physical network and its fixed rational control schedule to literal tape execution and prove its recursive time bound.
- Account for complex endpoint corrections in the tape implementation.
- Finish the `NegacyclicKronecker` subroutine component.
- Extend `PowerOfTwoExact` from two coordinates to `d`.
- Compose the proved rational digit arithmetic into matrix routines and compile the finite network address permutations to literal tape steps.
- Start the tape compilation of §4: ordered-affine field updates, the role-stream split, and the depth-first schedule.
