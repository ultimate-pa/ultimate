#!/bin/bash
# Create a variant of speedup-poc with or without pointer limits 
# Number of pointers is first argument (has to be larger or equal to 1), with or without pointer limits is second argument (0 to disable, 1 to enable) 

pointers="$1"
limits="$2"

if [ -z "$pointers" ] ; then 
  echo "No pointer count given" ; exit 1
fi

if [ -z "$limits" ] ; then 
  echo "No pointer limits given" ; exit 1
fi

re='^[0-9]+$'
if ! [[ $pointers =~ $re ]] ; then
   echo "error: pointer count is not a number" ; exit 1
fi

if (( pointers < 1 )) ; then 
  echo "pointer count $pointers is too small. Specify minimum 1" ; exit 1
fi

# if [ "$limits" = "0" ]; then echo "pointer limits disabled" ; else echo "pointer limits enabled" ; fi

printf '//#Safe\n'
printf 'var #memory_int, #valid : [int] int;\n'
printf '\n'
printf 'procedure ULTIMATE.start();\n'
printf 'modifies #memory_int, #valid;\n'
printf '\n'
printf 'implementation ULTIMATE.start() {\n'
printf '  call main();\n'
printf '}\n'
printf '\n'
printf 'procedure main();\n'
printf 'modifies #memory_int, #valid;\n'
printf '\n'
printf 'implementation main() {\n'

printf '  var p1'
for i in $(seq 2 ${pointers}) ; do 
  printf ", p${i}"
done 
printf ' : int;\n'
printf '\n'
for i in $(seq 1 ${pointers}) ; do 
  printf "  call p${i} := malloc();\n"
done 
printf '\n'

if ! [ "$limits" = "0" ]; then
  for i in $(seq 2 ${pointers}) ; do 
    printf "  assume p$((i-1)) < p${i};\n"
  done
  if (( pointers > 1 )) ; then printf '\n' ; fi 
fi

for i in $(seq 1 ${pointers}) ; do 
  printf "  #memory_int[p${i}] := 0;\n"
done 
printf '\n'

printf '  while (*) {\n'
  if (( pointers == 1 )) ; then 
    printf '      #memory_int[p1] := #memory_int[p1] + 1;\n'
  else 
    printf '    if (*) {\n'
    printf '      #memory_int[p1] := #memory_int[p1] + 1;\n'
    printf '    }'
    
    for i in $(seq 2 ${pointers}) ; do 
      if (( i == pointers )) ; then 
        printf ' else {\n'
      else 
        printf ' else if (*) {\n'
      fi
      printf "      #memory_int[p${i}] := #memory_int[p${i}] "
      if (( i % 2 == 0 )) ; then printf "-" ; else printf "+" ; fi
      printf " 1;\n"
      printf '    }'
    done
  fi
printf '\n  }\n'
printf '\n'

for i in $(seq 1 ${pointers}) ; do 
  printf "  assert #memory_int[p${i}] "
  if (( i % 2 == 0 )) ; then 
    printf "<="
  else 
    printf ">="
  fi
  printf " 0;\n"
done 
printf '\n'
printf '}\n'
printf '\n'
printf 'procedure malloc() returns (ptr : int);\n'
printf 'modifies #valid;\n'
printf 'ensures old(#valid)[ptr] == 0;\n'
printf 'ensures #valid == old(#valid)[ptr:=1];\n'
