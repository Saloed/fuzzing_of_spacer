# Fuzzing of Spacer
Fuzzer of the CHC-solver Spacer.

## Install
Install Z3 with Python API according to the instructions given here: https://github.com/Z3Prover/z3.  
Or you can use the Dockerfile (`docker build -t spacer-fuzzing .`).

## Use
* `python src/main.py <seed-file1> [<seed-file2> ...]`  
* `python src/main.py spacer-benchmarks[/<subdir>]` — to check all benchmarks from _/spacer-benchmarks_ or _/spacer-benchmarks/\<subdirectory\>_.  
* `python src/main.py chc-comp<year>-benchmarks[/<subdir>]` — to check all benchmarks from _/chc-comp\<year\>-benchmarks_ or _/chc-comp\<year\>-benchmarks/\<subdirectory\>_.  
* `python src/main.py all` — to check all benchmarks.  

`docker run spacer-fuzzing` if you are using docker.  

Add `-heuristics <priority1> <priority2> ...` (or `-heur`) to change default instance selection to the selection based on:  
* the probability of transitions (`transitions`);  
* the probability of states (`states`);  
* chc-difficulty (`difficulty`).  

You can add `-options <option1> <option2> ...` (or `-opt`) to:  
* use only Z3 rewritings as mutations (`only_simplify`);  
* choose mutations equally likely (`without_mutation_weights`);  
* use Eldarica (`with_oracles`).  

## Seeds
Download benchmarks from
* https://github.com/dvvrd/spacer-benchmarks  
* https://github.com/chc-comp/chc-comp21-benchmarks  
* https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/tree/main/clauses  

and place them in the root directory of this repository.  

## Output analysis and reducing
You can look at bugs in in the auto-generated directory _output/bugs/_.  
Use `python src/bug_analysis.py` to reduce bug-сausing examples (results of reducing are placed in _output/reduced/_). Also you can:  
* specify the file and mutation chain to reproduce the bug: `python src/bug_analysis.py <filename> <mutation chain>`;  
* specify the seed and mutant files to check instances equivalence: `python src/bug_analysis.py <seed_filename> -bug_file=<mutant_file>`.

