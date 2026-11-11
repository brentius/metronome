# Dot-source from PowerShell: . code\tools\env.ps1
# Puts the local OSS CAD Suite (2026-10-22) on PATH. Override with $env:OSS_CAD_SUITE.
if (-not $env:OSS_CAD_SUITE) { $env:OSS_CAD_SUITE = "C:\Users\b_yee23\tools\oss-cad-suite" }
$env:PATH = "$env:OSS_CAD_SUITE\bin;$env:OSS_CAD_SUITE\lib;$env:PATH"
$env:VERILATOR_ROOT = "$env:OSS_CAD_SUITE\share\verilator"
