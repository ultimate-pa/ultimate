@echo off
setlocal
set "DIR=%~dp0"
set "ARCH=32bit"

rem Test verification
echo ---- Verification ----
for %%PROGRAM in ("%DIR%examples\*.c") do (
  for %%SPEC in ("%DIR%examples\*.prp") do (
    "%DIR%Ultimate.py" --file "%%~fPROGRAM" --spec "%%~fSPEC" --architecture "%ARCH%"
  )
)

rem Test validation (for YAML correctness witness)
echo ---- Validation ----
for %%WITNESS in ("%DIR%examples\*.yml") do (
  for %%SPEC in ("%DIR%examples\*.prp") do (
    "%DIR%Ultimate.py" --file "%%~dpnWITNESS.c" --witness-type correctness_witness --validate "%%~fWITNESS" --spec "%%~fSPEC" --architecture "%ARCH%"
  )
)
