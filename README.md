# Ultimate
[![Build Status Jenkins](https://jenkins.sopranium.de/buildStatus/icon?job=Ultimate%2FUltimate%2Fdev&subject=jenkins:dev)](https://jenkins.sopranium.de/job/Ultimate/job/Ultimate/job/dev/)
[![Build Status Travis](https://travis-ci.com/ultimate-pa/ultimate.svg?branch=dev)](https://travis-ci.com/ultimate-pa/ultimate)
[![LGPL License](https://img.shields.io/badge/license-LGPLv3+LE-brightgreen.svg)](https://github.com/ultimate-pa/ultimate/wiki/License)
[![ZenHub](https://img.shields.io/badge/ZenHub-Board-orange.svg)](https://app.zenhub.com/workspaces/ultimate-5d19cb84cfdf4303fb078546)

Ultimate is a program analysis framework. Ultimate consists of several plugins that perform steps of a program analysis, e.g., parsing source code, transforming programs from one representation to another, or analyzing programs. Toolchains of these plugins can perform complex tasks, e.g., verify that a C program fulfills a given specification.

The [official website](https://ultimate.informatik.uni-freiburg.de/) includes a web interface which allows you to use several toolchains online, a list of all developers, and a list of awards Ultimate received over the years.

The available documentation can be found in [our wiki](https://github.com/ultimate-pa/ultimate/wiki).

You can download the [latest release from GitHub's release page](https://github.com/ultimate-pa/ultimate/releases/latest) or try our [nightly builds](https://struebli.informatik.uni-freiburg.de/ultimate-nightly/).

## Developers

The main active developers of Ultimate are:

* Matthias Heizmann (@Heizmann)
* Daniel Dietsch (@danieldietsch)
* Dominik Klumpp (@maul-esel)
* Frank Schüssele (@schuessf)

You can find an extensive list of past and current contributors [on our website](https://ultimate.informatik.uni-freiburg.de/#developers).

## Verification Tools (SV-COMP)

Among other plugins and libraries, Ultimate contains several program verification tools with which we participate in the [International Competition on Software Verification (SV-COMP)](sv-comp.sosy-lab.org/). In this competition, various fully-automatic verifiers and bug finding tools from academia and industry compete, to see which tool can successfully analyse the most programs wrt. a given property. We currently compete with 4 tools: Automizer, Taipan, Kojak and GemCutter.

### Ultimate Automizer
Contact: Matthias Heizmann

Automizer uses _**trace abstraction**_ to generalize infeasibility proofs for single program traces to Floyd-Hoare automata that cover larger parts of the program. For concurrency, it uses a Petri-net-based automata model.

[More Information & Web Interface](https://ultimate.informatik.uni-freiburg.de/?ui=tool&tool=automizer)

#### Publications about Automizer

To cite:
```bibtex
@inproceedings{sas09:trace-abstraction,
  author    = {Matthias Heizmann and Jochen Hoenicke and Andreas Podelski},
  editor    = {Jens Palsberg and Zhendong Su},
  title     = {Refinement of Trace Abstraction},
  booktitle = {Static Analysis, 16th International Symposium, {SAS} 2009, Los Angeles,
               CA, USA, August 9-11, 2009. Proceedings},
  series    = {Lecture Notes in Computer Science},
  volume    = {5673},
  pages     = {69--85},
  publisher = {Springer},
  year      = {2009},
  doi       = {10.1007/978-3-642-03237-0\_7},
}
```

* *Ultimate Automizer and the Search for Perfect Interpolants - (Competition Contribution)*. Heizmann, Chen, Dietsch, Greitschus, Hoenicke, Li, Nutz, Musa, Schilling, Schindler and Podelski, TACAS (SV-COMP) 2018, https://doi.org/10.1007/978-3-319-89963-3_30
* *Software Model Checking for People Who Love Automata*. Heizmann, Hoenicke and Podelski, CAV 2013, https://doi.org/10.1007/978-3-642-39799-8_2
* *Refinement of Trace Abstraction*. Heizmann, Hoenicke and Podelski, SAS 2009, https://doi.org/10.1007/978-3-642-03237-0_7

### Ultimate Taipan
Contact: Daniel Dietsch

Taipan uses _**abstract interpretation**_ with various domains to find loop invariants for path programs. Proofs for path programs are combined using automata operations on Floyd-Hoare-automata. If abstract interpretation cannot find a proof, trace abstraction is used. For concurrency, it uses an explicit product of finite automata.

[More Information & Web Interface](https://ultimate.informatik.uni-freiburg.de/?ui=tool&tool=taipan)

#### Publications about Taipan

To cite:
```bibtex
@inproceedings{sas17:loop-inv-from-ctex,
  author    = {Marius Greitschus and Daniel Dietsch and Andreas Podelski},
  editor    = {Francesco Ranzato},
  title     = {Loop Invariants from Counterexamples},
  booktitle = {Static Analysis - 24th International Symposium, {SAS} 2017, New York,
               NY, USA, August 30 - September 1, 2017, Proceedings},
  series    = {Lecture Notes in Computer Science},
  volume    = {10422},
  pages     = {128--147},
  publisher = {Springer},
  year      = {2017},
  doi       = {10.1007/978-3-319-66706-5\_7}
}
```

* *Ultimate Taipan with Symbolic Interpretation and Fluid Abstractions - (Competition Contribution)*. Dietsch, Heizmann, Nutz, Schätzle and Schüssele, TACAS (SV-COMP) 2020, https://doi.org/10.1007/978-3-030-45237-7_32
* *Ultimate Taipan with Dynamic Block Encoding - (Competition Contribution)*. Dietsch, Greitschus, Heizmann, Hoenicke, Nutz, Podelski, Schilling and Schindler, TACAS (SV-COMP) 2018, https://doi.org/10.1007/978-3-319-89963-3_31
* *Loop Invariants from Counterexamples*. Greitschus, Dietsch and Podelski, SAS 2017, https://doi.org/10.1007/978-3-319-66706-5_7
* *Ultimate Taipan: Trace Abstraction and Abstract Interpretation - (Competition Contribution)*. Greitschus, Dietsch, Heizmann, Nutz, Schätzle, Schilling, Schüssele and Podelski, TACAS (SV-COMP) 2017, https://doi.org/10.1007/978-3-662-54580-5_31

### Ultimate Kojak
Contact: Frank Schüssele

Kojak analyses programs using an extension of the _**Lazy Interpolants**_ CEGAR scheme.

[More Information & Web Interface](https://ultimate.informatik.uni-freiburg.de/?ui=tool&tool=kojak)

#### Publications about Kojak

To cite:
```bibtex
@inproceedings{tacas14:kojak,
  author    = {Evren Ermis and Alexander Nutz and Daniel Dietsch and Jochen Hoenicke and Andreas Podelski},
  editor    = {Erika {\'{A}}brah{\'{a}}m and Klaus Havelund},
  title     = {Ultimate Kojak - (Competition Contribution)},
  booktitle = {Tools and Algorithms for the Construction and Analysis of Systems - 20th International Conference, {TACAS} 2014,
               Held as Part of the European Joint Conferences on Theory and Practice of Software, {ETAPS} 2014, Grenoble, France, April 5-13, 2014. Proceedings},
  series    = {Lecture Notes in Computer Science},
  volume    = {8413},
  pages     = {421--423},
  publisher = {Springer},
  year      = {2014},
  doi       = {10.1007/978-3-642-54862-8\_36},
}
```

* *Ultimate Kojak with Memory Safety Checks - (Competition Contribution)*. Nutz, Dietsch, Mohamed and Podelski, TACAS (SV-COMP) 2015, https://doi.org/10.1007/978-3-662-46681-0_44
* *Ultimate Kojak - (Competition Contribution)*. Ermis, Nutz, Dietsch, Hoenicke and Podelski, TACAS (SV-COMP) 2014, https://doi.org/10.1007/978-3-642-54862-8_36

### Ultimate GemCutter
Contact: Dominik Klumpp

GemCutter is a verifier for concurrent programs based on _**commutativity**_,
i.e., the observation that for certain statements from different threads, the execution order does not matter.
It integrates partial order reduction algorithms (that take advantage of commutativity) with a trace abstraction-based CEGAR scheme.

#### Publications about GemCutter

To cite:
```bibtex
@inproceedings{pldi22:sound-sequentialization,
  author    = {Azadeh Farzan and Dominik Klumpp and Andreas Podelski},
  editor    = {Ranjit Jhala and Isil Dillig},
  title     = {Sound sequentialization for concurrent program verification},
  booktitle = {{PLDI} '22: 43rd {ACM} {SIGPLAN} International Conference on Programming
               Language Design and Implementation, San Diego, CA, USA, June 13 - 17, 2022},
  pages     = {506--521},
  publisher = {{ACM}},
  year      = {2022},
  doi       = {10.1145/3519939.3523727},
}
```

* *Stratified Commutativity in Verification Algorithms for Concurrent Programs*. Farzan, Klumpp and Podelski, POPL 2023 (to appear)
* *Sound Sequentialization for Concurrent Program Verification*. Farzan, Klumpp and Podelski, PLDI 2022, https://doi.org/10.1145/3519939.3523727
* *Ultimate GemCutter and the Axes of Generalization - (Competition Contribution)*. Klumpp, Dietsch, Heizmann, Schüssele, Ebbinghaus, Farzan and Podelski, TACAS (SV-COMP) 2022, https://doi.org/10.1007/978-3-030-99527-0_35
