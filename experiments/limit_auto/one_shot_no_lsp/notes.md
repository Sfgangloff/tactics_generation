Produced code, which seems to compile. No repair attempt, and no error. This is the report it gave me: 

⏺ Write(experiments/limit_auto/one_shot_no_lsp/output.lean)                                                                                                   
  ⎿  Wrote 336 lines to experiments/limit_auto/one_shot_no_lsp/output.lean                          
     import Mathlib                                                                                                                                           
                                                                                                                                                              
     open Lean Lean.Elab Lean.Elab.Tactic Lean.Meta                                                                                                           
     open Filter Topology Real Bornology                                                                                                                      
                                                                                                                                                              
     /-!                                                                                                                                                      
     # `limit_auto`                                                                                                                                         
                                                                                                                                                              
     A tactic that automatically proves limit goals of the form `Tendsto f F G` by                                                                            
     syntactic pattern-matching on `f` and selecting the appropriate Mathlib theorem.                                                                         
     … +326 lines (ctrl+o to expand)                                                                                                                          
                                                                                                                                                              
⏺ Written to experiments/limit_auto/one_shot_no_lsp/output.lean. Here is a summary of the implementation:
                                                                                                    
  ---
  Implementation summary                                                                                                                                      
   
  Structure                                                                                                                                                   
                                                                                                                                                            
  The file follows the three-class architecture from the spec, implemented entirely from knowledge of Lean 4 / Mathlib without reading any existing files or
  using LSP tools.

  Goal parsing (matchTendsto?)

  Extracts (f, F, G) from @Filter.Tendsto α β f F G by checking arity 5 and indexing args 2–4.

  Safety (containsIndeterminate)

  Recurses through lambdas and let-bindings looking for @HDiv.hDiv … num den where:
  - den is @OfNat.ofNat … (.lit (.natVal 0)) — literal zero
  - or num == den syntactically — covers t/t, (t-a)/(t-a)

  Classification (classifyFunction)

  Inspects the lambda body:
  - Reciprocal: body is @Inv.inv α inst (.bvar 0) (i.e. x⁻¹) or @HDiv.hDiv … 1 (.bvar 0) (i.e. 1/x)
  - ExponentialDecay: body recursively mentions Real.exp or Complex.exp
  - Continuity: everything else (tried speculatively)

  Proof strategies

  ┌──────────────────┬───────────────────────────────────────────────────────────────────────────────────────────────────┬──────────────────────┐
  │      Class       │                                         Primary approach                                          │       Fallback       │
  ├──────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────┼──────────────────────┤
  │ Reciprocal       │ Filter.tendsto_inv₀_nhdsWithin_ne_zero / tendsto_inv₀_cobounded' (multiple name variants)         │ Continuity           │
  ├──────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────┼──────────────────────┤
  │ ExponentialDecay │ Real.tendsto_exp_neg_atTop_nhds_zero / tendsto_exp_atBot / rewrite via tendsto_exp_comp_nhds_zero │ Continuity           │
  ├──────────────────┼───────────────────────────────────────────────────────────────────────────────────────────────────┼──────────────────────┤
  │ Continuity       │ Continuous.tendsto' + fun_prop/continuity / ContinuousAt.tendsto                                  │ Reciprocal, then Exp │
  └──────────────────┴───────────────────────────────────────────────────────────────────────────────────────────────────┴──────────────────────┘

  Tests

  17 tests matching the spec examples: 8 continuity, 2 exponential decay, 2 reciprocal, 5 safety/failure checks.