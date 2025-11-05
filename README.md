This repository stores experiments on the generation of tactics for theorem proving in Lean. 

The benchmark (`TacticsGeneration/Benchmark.lean`), coded manually, consists in 10 coding tasks with their tests and prompts.

We write the results of experiments in files `TacticsGeneration/Test*.lean`, including feedbacks.

The `data` folder contains a benchmark for prompts to python programs (`mbpp.jsonl`) which is used to produce a similar 
benchmark in Lean with the script `convert_to_lean.py` (see usage in the doc of the file).