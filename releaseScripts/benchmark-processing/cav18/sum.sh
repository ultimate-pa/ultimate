#!/bin/bash
# save file 
cp "$1"/CsvTraceAbstractionBenchmarks* pcsv.csv
 
# remove [] 
perl -pi -e 's|\[(.*?)\]|\1|g' pcsv.csv
 
# remove .ats inputs 
perl -pi -e 's|;.*?\.ats||g' pcsv.csv
 
# remove paths from settings
perl -pi -e 's|F:\\repos\\ultimate\\trunk\\examples\\settings\\||g' pcsv.csv
perl -pi -e 's|F:\\repos\\ultimate\\trunk\\examples\\toolchain\\||g' pcsv.csv
perl -pi -e 's|regression-verif\\||g' pcsv.csv

# make db 
csvsql --db sqlite:///sqcsv.db --overwrite -I --tables csv --insert pcsv.csv
rm pcsv.csv 

exit

## interesting queries 
# get sum of overall time 
sql2csv --db sqlite:///sqcsv.db --query "select Settings,Sum(OverallTime),Count(File) from (select * from csv join (select File from (select File,Count(Settings) as Count from csv where Result='SUCCESS' and Message not like '%We were not able to verify any specifiation because the program does not contain any specification.%' group by File) where Count = 3) te on csv.File = te.File) group by Settings" | csvlook -I | less -S

# sanity check 
sql2csv --db sqlite:///sqcsv.db --query "select Settings,File,Result,Message,OverallTime from (select * from csv join (select File from (select File,Count(Settings) as Count from csv where Result='SUCCESS' and Message not like '%We were not able to verify any specifiation because the program does not contain any specification.%' group by File) where Count = 3) te on csv.File = te.File) " | csvstat

# get only revisions > 0 
sql2csv --db sqlite:///sqcsv.db --query "select File,Settings,OverallTime from csv where File like '%;%' and Settings like '%Lazy%' and Result = 'SUCCESS' and Message not like '%We were not able to verify any specifiation because the program does not contain any specification.%'" | csvstat
sql2csv --db sqlite:///sqcsv.db --query "select File,Settings,OverallTime from csv where File like '%;%' and Settings like '%Eager%' and Result = 'SUCCESS' and Message not like '%We were not able to verify any specifiation because the program does not contain any specification.%'" | csvstat

# 
sql2csv --db sqlite:///sqcsv.db --query "select distinct(File),Settings,OverallTime from (select * from csv JOIN (select File from csv where File like '%;%' and Result = 'SUCCESS' and Message not like '%We were not able to verify any specifiation because the program does not contain any specification.%') te on te.File LIKE csv.File||'%') where Settings like '%default.epf%'" | csvstat
