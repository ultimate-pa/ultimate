@echo off
setlocal
set "DIR=%~dp0"
set "ARCH=32bit"

rem Test verification
echo ---- Verification ----
for %%P in ("%DIR%examples\*.c") do (
  for %%S in ("%DIR%examples\*.prp") do (
    python "%DIR%Ultimate.py" --file "%%~fP" --spec "%%~fS" --architecture "%ARCH%"
  )
)

rem Test validation (for YAML correctness witness)
echo ---- Validation ----
for %%W in ("%DIR%examples\*.yml") do (
  for %%S in ("%DIR%examples\*.prp") do (
    python "%DIR%Ultimate.py" --file "%%~dpnW.c" --witness-type correctness_witness --validate "%%~fW" --spec "%%~fS" --architecture "%ARCH%"
  )
)
