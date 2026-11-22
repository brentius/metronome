Write-Host "== acceptance build (both modules, warningAsError from lakefile) =="
$env:PATH = "$env:USERPROFILE/.elan/bin;$env:PATH"
Push-Location code/tests/lean
$t0 = Get-Date
lake build Metronome.Bridge.Stream Metronome.ChipCut.Discharge.StreamDbg 2>&1 | Tee-Object -FilePath ..\..\..\data\raw\lean_bridge_stream_frozen_v4_20261121\build.log
$code = $LASTEXITCODE
$t1 = Get-Date
Write-Host "exit=$code wall=$([math]::Round(($t1-$t0).TotalSeconds,1))s acceptance_build"

Write-Host "== axioms =="
$t0 = Get-Date
lake env lean ..\..\..\data\raw\lean_bridge_stream_frozen_v4_20261121\axioms.lean |
  Tee-Object -FilePath ..\..\..\data\raw\lean_bridge_stream_frozen_v4_20261121\axioms.txt
$code2 = $LASTEXITCODE
$t1 = Get-Date
Write-Host "exit=$code2 wall=$([math]::Round(($t1-$t0).TotalSeconds,1))s axioms"

Write-Host "== no sorry/admit/native_decide =="
$hits = Select-String -Path Metronome/Bridge/Stream.lean, Metronome/ChipCut/Discharge/StreamDbg.lean -Pattern "sorry|admit|native_decide"
Write-Host "matches=$($hits.Count)"
Pop-Location

Write-Host "== src untouched =="
git diff --quiet HEAD -- src
Write-Host "exit=$LASTEXITCODE"
