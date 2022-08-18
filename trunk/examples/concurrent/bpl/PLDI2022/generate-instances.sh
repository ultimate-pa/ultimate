#!/bin/bash

: ${MAX_THREADS:=10}
: ${MIN_ID:=1}
: ${OFFSET:=0}

echo "Settings:
  TEMPLATE_FILE    = $TEMPLATE_FILE
  THREAD_PROCEDURE = $THREAD_PROCEDURE
  MAX_THREADS      = $MAX_THREADS
  VERDICT          = $VERDICT
  MIN_ID           = $MIN_ID
  OFFSET           = $OFFSET
"

TEMPLATE=$(cat "$TEMPLATE_FILE")
grep -q "<<<JOINS>>>" <<< "$TEMPLATE"
JOIN_FREE=$?

if [[ "$VERDICT" == "true" ]]
then
  ULTIMATE_VERDICT="Safe"
else
  ULTIMATE_VERDICT="Unsafe"
fi

function get_unique_id {
  local ID=""
  local F=$((($1-MIN_ID+1)%10))
  for k in $(seq 1 $1)
  do
    ID="$ID$F"
    if (( k < $1 ))
    then
      ID="$ID,"
    fi
  done
  echo "$ID"
}

for ((i=1;i<=MAX_THREADS-OFFSET;i++));
do
  MAX_ID=$((MIN_ID+i-1))
  FORKS=""
  JOINS=""

  for ((j=MIN_ID;j<=MAX_ID;j++));
  do
    if (( $JOIN_FREE == 1 ))
    then
      ID=$(printf "%2d" $j)
    else
      ID=$(get_unique_id $j)
    fi

    FORKS="${FORKS}fork $ID $THREAD_PROCEDURE();"
    JOINS="${JOINS}join $ID;"
    if (( j < MAX_ID ));
    then
      FORKS="$FORKS\n  "
      JOINS="$JOINS\n  "
    fi
  done

  INSTANCE=${TEMPLATE/<<<FORKS>>>/$FORKS}
  INSTANCE=${INSTANCE/<<<JOINS>>>/$JOINS}
  SUFFIX=$(printf %02d $((i+OFFSET)))
  FILE=${TEMPLATE_FILE%.template}$SUFFIX.bpl
  YML=${FILE%.bpl}.yml
  echo -e "//#$ULTIMATE_VERDICT\n$INSTANCE" > "$FILE"

  echo "format_version: '2.0'

input_files: '$FILE'

properties:
  - property_file: ../../../svcomp/properties/unreach-call.prp
    expected_verdict: $VERDICT

options:
  language: Boogie
" > "$YML"

done
