# Micro-Policies in Coq

### Description

Coq formalization accompanying the paper:
- Micro-Policies: A Framework for Verified, Tag-Based Security Monitors. Arthur Azevedo de Amorim, Maxime Dénès, Nick Giannarakis, Cătălin Hriţcu, Benjamin C. Pierce, Antal Spector-Zabusky, Andrew Tolmach. Submitted. November 2014. (http://prosecco.gforge.inria.fr/personal/hritcu/publications/micropolicies-draft.pdf)

### Prerequisites

- Coq 8.4pl4 or 8.4pl5 (https://coq.inria.fr/download)
- SSReflect 1.5 (http://ssr.msr-inria.inria.fr/FTP/)
- The Mathematical Components library 1.5
  (http://www.msr-inria.fr/projects/mathematical-components-2/)
- The CoqUtils library (https://github.com/arthuraa/coq-utils)

### Compiling

    make -j

### License

- The files in this directory and all subdirectories other than
  `compcert/lib` are under the MIT license (see `LICENSE`)
- The files in the `compcert/lib` directory are dual-licensed under
  the INRIA Non-Commercial License Agreement and the GNU General
  Public License version 2 or later (see `compcert/LICENSE`)
