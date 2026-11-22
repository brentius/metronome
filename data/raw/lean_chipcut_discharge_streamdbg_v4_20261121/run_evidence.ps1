Write-Host "== clean build (warningAsError from lakefile) =="
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
Push-Location code/tests/lean
$t0 = Get-Date
lake build Metronome.ChipCut.Discharge.StreamDbg
$code = $LASTEXITCODE
$t1 = Get-Date
Write-Host "exit=$code wall=$([math]::Round(($t1-$t0).TotalSeconds,1))s"

Write-Host "== axioms =="
$t0 = Get-Date
lake env lean ..\..\..\data\raw\lean_chipcut_discharge_streamdbg_v4_20261121\axioms.lean
$code2 = $LASTEXITCODE
$t1 = Get-Date
Write-Host "exit=$code2 wall=$([math]::Round(($t1-$t0).TotalSeconds,1))s"
Pop-Location

Write-Host "== src untouched =="
git diff --quiet HEAD -- src
Write-Host "exit=$LASTEXITCODE"
