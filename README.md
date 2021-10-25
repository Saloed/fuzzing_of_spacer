# Fuzzing of Spacer
JetBrains Research intership project.

## Install
Install Z3 with Python API according to the instructions given here: https://github.com/Z3Prover/z3.  
Or you can use the Dockerfile (`docker build -t spacer/fuzz .`).

## Use
* `python src/main.py <seed-file1> [<seed-file2> ...]`  
* `python src/main.py` — to check benchmarks from _/spacer-benchmarks/relational_ that don't run for long and don't return "unknown".  
* `python src/main.py spacer-benchmarks[/<subdir>]` — to check all benchmarks from _/spacer-benchmarks_ or _/spacer-benchmarks/\<subdirectory\>_.  
* `python src/main.py chc-comp<year>-benchmarks[/<subdir>]` — to check all benchmarks from _/chc-comp\<year\>-benchmarks_ or _/chc-comp\<year\>-benchmarks/\<subdirectory\>_.  
* `python src/main.py all` — to check all benchmarks.  

`docker run spacer/fuzz` if you are using docker.  

Add `-heuristics <priority1> <priority2> ...` (or `-heur`) to change default instance selection to the selection based on:  
* the probability of transitions (`transitions`);  
* the probability of states (`states`);  
* chc-difficulty (`difficulty`).  

## Seeds
Download benchmarks from
* https://github.com/dvvrd/spacer-benchmarks  
* https://github.com/chc-comp/chc-comp21-benchmarks (or for another year)  

and place them in the root directory of this repository.  

## Output analysis
You can look at bugs in in the auto-generated directory _output/bugs/_.  
Use `python src/bug_analysis.py` to reduce bug-сausing examples (results of reducing are placed in _output/reduced/_). Also you can specify the file and mutation chain to reproduce the bug: `python src/bug_analysis.py <filename> -mut_chain=<mutation chain>`.

