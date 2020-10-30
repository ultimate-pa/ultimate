#!/bin/bash

DIR=$(realpath $(dirname "$0"))/generated
MAX_TRANS=${1:-10}

mkdir -p "$DIR"

echo "Cleaning folder $DIR ..."
rm -rf $DIR/*.ats

echo "Generating $MAX_TRANS benchmarks ..."
for k in $(seq 2 $MAX_TRANS)
do
  printf -v k_pad "%02d" $k
  NAME="example_$k_pad"
  FILE="$DIR/$NAME.ats"

  LETTERS=""
  PLACES="q"
  TRANSITIONS="\n"
  INITIAL="q"

  for i in $(seq 1 $k)
  do
    LETTER="t${i}"
    LETTERS="$LETTERS $LETTER"
    PLACES="$PLACES p${i}_1 p${i}_2"
    TRANSITIONS="$TRANSITIONS    ({q p${i}_1} $LETTER {q p${i}_2})\n"
    INITIAL="$INITIAL p${i}_1"
  done

  echo -e "PetriNet cycle$k = (
  alphabet = { $LETTERS },
  places = { $PLACES },
  transitions = { $TRANSITIONS  },
  initialMarking = { $INITIAL },
  acceptingPlaces = { }
);

BranchingProcess unf$k = finitePrefix(cycle$k);
// print(unf$k); // risky for large examples, may freeze
print(numberOfConditions(unf$k));
" >> "$FILE"
done
