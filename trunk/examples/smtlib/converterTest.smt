(benchmark PEQ002_size5.smt
:category { crafted }
:difficulty { 0 }
:logic QF_UF
:extrapreds ((A) (B) (C) (D) (E))
:assumption
(iff E (and A B))
:assumption
(or (not (and A B)) (and A B))
:assumption
(iff E (or A B))
:assumption
(iff E (implies A B))
:assumption
(iff E (iff A B))
:assumption
(iff E (xor A B))
:formula 
( and 
      (iff E (or A (or B (or C (and D true)))))
      (iff E (if_then_else A B C)) (iff E (if_then_else A true false))
)
)
