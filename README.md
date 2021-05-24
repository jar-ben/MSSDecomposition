This repository contains a tool for enumeration of Maximal Satisfiable Subsets (MSSes), or alternatively, Minimal Correction Subsets (MCSes), of a given Boolean formula. 
**This is an experimental version which still needs some clean up. If you wish to use the tool and encounter any problems during installing or running the tool, please, contact me at xbendik=at=gmail.com.**

## Installation


## Running our tool
```
python3 counter.py <input_cnf_file>
```
So for example, "python3 counter.py ./tests/m1_marco_input_132_200_97_refined.cnf"

## Related Tools
This tool tends to speed-up the MSS (MCS) enumeration by decomposing the input formula into several smaller subformulas, then solving the subformulas, and combining results from the subformulas. However, for some benchmarks, the decomposition is not applicable. Hence, we recommend you to try also our another MSS enumerator that is not based on the decomposition called [RIME](https://github.com/jar-ben/rime). 

## Citing
A paper presenting our tool is currently under a conference review process. We will provide the citation info once the paper is accepted. 

## Contact
In case of any troubles, do not hesitate to contact me, Jaroslav Bendik, at xbendik=at=gmail.com.
