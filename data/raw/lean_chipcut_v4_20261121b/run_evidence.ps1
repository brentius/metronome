$ErrorActionPreference = "Continue"
$root = Resolve-Path "C:\Users\b_yee23\Documents\projects\jane street comp"
$leanDir = Join-Path $root "code\tests\lean"
$ev = Join-Path $root "data\raw\lean_chipcut_v4_20261121b"
New-Item -ItemType Directory -Force -Path $ev | Out-Null
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
$log = Join-Path $ev "commands.log"
"# ChipCut v4 review-fix evidence (lean_chipcut_v4_20261121b)" | Set-Content $log
"# machine: $($env:COMPUTERNAME); PowerShell; lean toolchain from code/tests/lean/lean-toolchain" | Add-Content $log
"" | Add-Content $log

function Run-Cmd([string]$label, [string]$dir, [string]$cmd) {
  Push-Location $dir
  $sw = [System.Diagnostics.Stopwatch]::StartNew()
  $out = & powershell -NoProfile -Command "$cmd" 2>&1
  $code = $LASTEXITCODE
  $sw.Stop()
  Pop-Location
  $secs = [math]::Round($sw.Elapsed.TotalSeconds, 2)
  "[$label] $cmd" | Add-Content $log
  "  exit=$code wall=${secs}s" | Add-Content $log
  return @{ out = $out; code = $code; secs = $secs }
}

$b = Run-Cmd "clean" $leanDir "Remove-Item -Recurse -Force .lake\build\lib\lean\Metronome\ChipCut,.lake\build\lib\lean\Metronome\ChipCut.olean -ErrorAction SilentlyContinue; exit 0"
"[clean] exit=$($b.code) wall=$($b.secs)s  (ChipCut oleans removed)" | Add-Content $log
$b = Run-Cmd "build" $leanDir "`$env:PATH='$env:USERPROFILE\.elan\bin;' + `$env:PATH; lake build Metronome.ChipCut"
$b.out | Out-File -Encoding utf8 (Join-Path $ev "build.log")
"[build] exit=$($b.code) wall=$($b.secs)s  (log: build.log)" | Add-Content $log
"" | Add-Content $log

$a = Run-Cmd "axioms" $leanDir "`$env:PATH='$env:USERPROFILE\.elan\bin;' + `$env:PATH; lake env lean ..\..\..\data\raw\lean_chipcut_v4_20261121b\axioms.lean"
$a.out | Out-File -Encoding utf8 (Join-Path $ev "axioms.txt")
"[axioms] exit=$($a.code) wall=$($a.secs)s  (log: axioms.txt)" | Add-Content $log
"" | Add-Content $log

$g = Run-Cmd "src-unchanged" $root "git diff --quiet HEAD -- src; exit `$LASTEXITCODE"
"[src-unchanged] exit=$($g.code) wall=$($g.secs)s  (no output = src/ matches HEAD)" | Add-Content $log
"" | Add-Content $log

$s = Run-Cmd "no-sorry" $leanDir "Select-String -Path Metronome\ChipCut\*.lean,Metronome\ChipCut.lean -Pattern 'sorry|native_decide|admit' | ForEach-Object { `$_.Line }"
$s.out | Out-File -Encoding utf8 (Join-Path $ev "sorry_scan.txt")
"[no-sorry] exit=$($s.code) wall=$($s.secs)s  (empty scan = none; log: sorry_scan.txt)" | Add-Content $log
"" | Add-Content $log
"files changed by this task:" | Add-Content $log
"  code/tests/lean/Metronome/ChipCut/Wire.lean" | Add-Content $log
"  code/tests/lean/Metronome/ChipCut/Step.lean" | Add-Content $log
"  code/tests/lean/Metronome/ChipCut/Rel.lean   (new)" | Add-Content $log
"  code/tests/lean/Metronome/ChipCut/Proof.lean" | Add-Content $log
"  code/tests/lean/CHIPCUT_NOTES.md" | Add-Content $log
"  data/raw/lean_chipcut_v4_20261121b/ (this evidence)" | Add-Content $log
Get-Content $log
