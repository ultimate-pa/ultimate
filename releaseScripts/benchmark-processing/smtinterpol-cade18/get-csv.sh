#!/bin/bash

shared_crashs=(
"SyntaxErrorResult"             # c translation error 
"UnsupportedSyntaxResult"       # c translation error 
"CACSL2BoogieTranslator"        # c translation error 
"TypeErrorResult"               # c translation error 
"overapproximation of memtrack" # this will be counted as unsafe in the next run; for svcomp, we say overapprox or unsafe if we get to such a path 
)

oors=(
"SMTLIBException: Timeout exceeded" # smtinterpol timeout 
"OutOfMemoryError" # sometimes there is OOM 
)

badproofs=(
"SMTLIBException.*theory not supported by interpolation or bad proof"                               # reported as error to z3 
"Sort mismatch at argument #1 for function \(declare-fun >= \(Int Int\) Bool\)"                     # could be an error in Ultimate
"SMTLIBException: Undeclared function symbol \(array-ext \(Array Int Int\) \(Array Int Int\)\)"     # unclear what kind of array-ext this should be 
)

pqecrashes=(
"traceabstraction: AssertionError: var is still there"          # PQE will throw this if it reached an incomplete part 
"UnsupportedOperationException: alternation not yet supported"  # not yet implemented in PQE 
)

# full header
#printf "setting,total,valid,safe,unsafe,timeout,unknown,ultcrashs,badproof,pqe_crash,solver_unknown,unexp_crash,check\n"

# reduced header 
printf "setting,total,safe,unsafe,timeout,unknown\n"
for i in "$1".summary.*; do 
    vt=`grep -oP "\d+ of \d+" "$i"`
    v=`echo "$vt" | cut -d " " -f 1`
    t=`echo "$vt" | cut -d " " -f 3`
    safe=`grep -oP "\d+ safe" "$i" | cut -d " " -f 1`
    unsafe=`grep -oP "\d+ unsafe" "$i" | cut -d " " -f 1`
    crash=`grep -oP "\d+ exceptions" "$i" | cut -d " " -f 1`
    
    sc=0
    for c in "${shared_crashs[@]}"; do 
        for inst in `grep -oP "\d+ : .*$c" "$i" | cut -d ":" -f 1`; do
            let sc=$sc+$inst
        done
    done

    bp=0
    for c in "${badproofs[@]}"; do 
        for inst in `grep -oP "\d+ : .*$c" "$i" | cut -d " " -f 1`; do
            let bp=$bp+$inst
        done
    done
    
    pqe_crash=0
    for c in "${pqecrashes[@]}"; do 
        for inst in `grep -oP "\d+ : .*$c" "$i" | cut -d " " -f 1`; do
            let pqe_crash=$pqe_crash+$inst
        done
    done

    sou_crash=0
    for inst in `grep -oP "\d+ : unable to decide satisfiability of path constraint" "$i" | cut -d " " -f 1`; do 
        let sou_crash=$sou_crash+$inst
    done
    
    to=`grep -oP "\d+ timeouts" "$i" | cut -d " " -f 1`
    oor=0
    for c in "${oors[@]}"; do 
        for inst in `grep -oP "\d+ : .*$c" "$i" | cut -d ":" -f 1`; do
            let oor=$oor+$inst
        done
    done    
    
    unk=`grep -oP "\d+ unknowns" "$i" | cut -d " " -f 1`
    unexp_crash=$((crash-bp-sc-pqe_crash-sou_crash-oor))
    to=$((to+oor))
    #check if line sum equals total 
    ctrl=$((t-(safe+unsafe+to+unk+sc+bp+pqe_crash+sou_crash+unexp_crash)))
    # full row 
    # printf "$i,$t,$v,$safe,$unsafe,$to,$unk,$sc,$bp,$pqe_crash,$sou_crash,$unexp_crash,$ctrl\n"
    
    # reduced row: total already without shared crashes  
    t=$((t-sc))
    all_remaining_as_unknown=$((unk+bp+pqe_crash+sou_crash+unexp_crash))
    ctrl=$((t-(safe+unsafe+to+all_remaining_as_unknown)))
    printf "$i,$t,$safe,$unsafe,$to,$all_remaining_as_unknown\n"
done 
echo $sc