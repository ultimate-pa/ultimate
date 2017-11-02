#!/bin/bash

for file in $(ls Problem15*.c); do
	RUN=$(grep "calculate_output2(int input);" ${file})
	STATUS=$?
	if [ $STATUS -ne 0 ]; then
		sed -i '22 iint calculate_output2(int input);' ${file}
	fi
done

for file in $(ls Problem16*.c); do
	RUN=$(grep "calculate_output2(int input);" ${file})
	STATUS=$?
	if [ $STATUS -ne 0 ]; then
		sed -i '22 iint calculate_output2(int input);' ${file}
	fi
done

for file in $(ls Problem17*.c); do
	RUN=$(grep "calculate_output2(int input);" ${file})
	STATUS=$?
	if [ $STATUS -ne 0 ]; then
		sed -i '22 iint calculate_output2(int input);' ${file}
	fi
done

for file in $(ls Problem18*.c); do
	RUN=$(grep "calculate_output2(int input);" ${file})
	STATUS=$?
	if [ $STATUS -ne 0 ]; then
		sed -i '22 iint calculate_output3(int input);' ${file}
		sed -i '22 iint calculate_output2(int input);' ${file}
	fi
done

for file in $(ls Problem19*.c); do
	RUN=$(grep "calculate_output2(int input);" ${file})
	STATUS=$?
	if [ $STATUS -ne 0 ]; then
		sed -i '22 iint calculate_output6(int input);' ${file}
		sed -i '22 iint calculate_output5(int input);' ${file}
		sed -i '22 iint calculate_output4(int input);' ${file}
		sed -i '22 iint calculate_output3(int input);' ${file}
		sed -i '22 iint calculate_output2(int input);' ${file}
	fi
done
