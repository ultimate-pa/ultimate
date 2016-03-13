@echo off
rem This is a windows script to apply generate-tables.py to all .csv files in the current folder and then move the created plots.tex to a folder, renaming it appropriately. 
rem 1 parameter: The path to releaseScripts\benchmark-processing\generate-tables.py
rem 2 parameter: Output directory

IF [%1]==[] (
	echo No path to generate-tables.py given
	exit /B 1
)
IF [%2]==[] (
	echo No output directory specified 
	exit /B 1
)

set PYTHON2="C:\Program Files\python 2.7.9\python.exe"

@echo off
for /f "tokens=*" %%f in ('dir /l /a-d /b *.csv') do (
    for /f "tokens=1 delims=1234567890" %%n in ("%%~nf") do (
        echo Processing file %%~nxf with prefix %%n
		%PYTHON2% %1 %%f -o %2 -n %%n
		move %2\plots.tex %2\plots-%%n.tex
    )
)