# Decomposition Based MSS/MCS Enumerator
This repository contains a tool for enumeration of Maximal Satisfiable Subsets (MSSes), or alternatively, Minimal Correction Subsets (MCSes), of a given Boolean formula. 
**This is an experimental version which still needs some clean up. If you wish to use the tool and encounter any problems during installing or running the tool, please, contact me at xbendik=at=gmail.com.**

## Installation
You need a Linux OS and python3 to run our tool. Moreover, 
you need to install the PySAT python library before using our tool; please, follow the instructions at [https://pysathq.github.io/installation.html](https://pysathq.github.io/installation.html). Also, we are using the RC2 MaxSAT solver that is a part of the PySAT library; to use RC2, you will probably have to add the path to RC2 to the PYTHONPATH variable. See [https://pysathq.github.io/usage.html](https://pysathq.github.io/usage.html) for instructions on how to use RC2. 

Besides PySAT, we use several tools that we distribute as precompiled binaries, including mainly: [rime](https://github.com/jar-ben/rime) and [UWrMaxSat](https://github.com/marekpiotrow/UWrMaxSat). The binaries are located in the folder `./tools/`. If you want to improve the performance, you can try to rebuild the binaries of
[rime](https://github.com/jar-ben/rime) and [UWrMaxSat](https://github.com/marekpiotrow/UWrMaxSat). 

To check that our tool is ready to use, run `python3 counter.py tests`. In case of any issues with the installation, you will see some assertions error, bug reports, etc. In the other case, when the tool works as intended, the output of executing the above command should look like the following:
```
./tests/m1_marco_input_199_200_80_refined.cnf nontrivial Components: 9 msses: 2304 counts: [2, 4, 2, 3, 2, 3, 2, 2, 2] explicit: 22
duration <duration_in_seconds>
```


## Running our tool
```
python3 counter.py <input_cnf_file>
```
So for example, "python3 counter.py ./tests/m1_marco_input_132_200_97_refined.cnf"

Use the flag `--verbosity 2` to also output (zero-based) indices of clauses in the individual MCSes of the input formula.

## Related Tools
This tool tends to speed-up the MSS (MCS) enumeration by decomposing the input formula into several smaller subformulas, then solving the subformulas, and combining results from the subformulas. However, in some cases, the decomposition is not applicable. Hence, we recommend you to try also our another MSS enumerator called [RIME](https://github.com/jar-ben/rime). 

## Citing
A paper presenting our tool is currently under a conference review process. We will provide the citation info once the paper is accepted. 

## Contact
In case of any troubles, do not hesitate to contact me, Jaroslav Bendik, at xbendik=at=gmail.com.
