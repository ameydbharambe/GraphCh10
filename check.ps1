
param(
    [switch]$Final
)

$ErrorActionPreference = "Stop"
$fail = $false

# Always run from the project root.
Set-Location $PSScriptRoot

$files = @(Get-ChildItem "GraphCh10" -Recurse -Filter "*.lean" -File)
$allowed = @(Get-Content "allowed-imports.txt" |
    Where-Object { $_.Trim() -ne "" -and $_ -notmatch '^\s*#' } |
    ForEach-Object { $_.Trim() })

$approved = @(Get-Content "approved-axioms.txt" |
    Where-Object { $_.Trim() -ne "" -and $_ -notmatch '^\s*#' } |
    ForEach-Object { $_.Trim() })

Write-Host "=== GraphCh10 Source Audit ==="

# CHECK 1: Import restrictions
Write-Host "`n[1] Checking imports..."

foreach ($file in $files) {
    $imports = @(Select-String -Path $file.FullName `
        -Pattern '^\s*import\s+(.+)$')

    foreach ($match in $imports) {
        $modules = $match.Matches[0].Groups[1].Value -split '\s+'

        foreach ($module in $modules) {
            if ($module -eq "") { continue }

            if ($file.Name -eq "Foundations.lean") {
                if ($module -notin $allowed) {
                    Write-Host "FAIL: Unauthorized import $module"
                    $fail = $true
                }
            }
            elseif ($module -notmatch '^GraphCh10(\.|$)') {
                Write-Host "FAIL: External import $module in $($file.Name)"
                $fail = $true
            }
        }
    }
}

# CHECK 2: Forbidden declarations and proof bypasses
Write-Host "[2] Checking forbidden references..."

$banned = @(
    '\bSimpleGraph\b',
    '\bDigraph\b',
    '\bQuiver\b',
    '\bMathlib\.Combinatorics\b',
    '\bnative_decide\b',
    '\badmit\b',
    '\bunsafe\b',
    '\bimplemented_by\b',
    '\bskipKernelTC\b'
)

foreach ($pattern in $banned) {
    $hits = @($files | Select-String -Pattern $pattern)

    if ($hits.Count -gt 0) {
        Write-Host "FAIL: Forbidden reference: $pattern"
        $hits | ForEach-Object { Write-Host $_ }
        $fail = $true
    }
}

# CHECK 3: Approved axioms
Write-Host "[3] Checking axioms..."

foreach ($file in $files) {
    $axioms = @(Select-String -Path $file.FullName `
        -Pattern '^\s*(?:private\s+|protected\s+)?axiom\s+([A-Za-z_][A-Za-z0-9_'']*)')

    foreach ($match in $axioms) {
        $name = $match.Matches[0].Groups[1].Value

        if ($file.Name -ne "Results.lean" -or
            $name -notin $approved) {
            Write-Host "FAIL: Unapproved axiom $name in $($file.Name)"
            $fail = $true
        }
    }
}

# CHECK 4: Exercise status and placeholders
Write-Host "[4] Checking exercise statuses..."

$exerciseDir = "GraphCh10\Exercises"

if (Test-Path $exerciseDir) {
    $exercises = @(Get-ChildItem $exerciseDir -Recurse -Filter "*.lean" -File)

    foreach ($file in $exercises) {
        $lines = @(Get-Content $file.FullName)
        $status = if ($lines.Count -gt 0) { $lines[0].Trim() } else { "" }

        if ($status -notin @(
            "-- STATUS: UNFINISHED",
            "-- STATUS: PARTIAL",
            "-- STATUS: COMPLETE"
        )) {
            Write-Host "FAIL: Invalid status in $($file.Name)"
            $fail = $true
            continue
        }

        $hasSorry = [bool](Select-String -Path $file.FullName `
            -Pattern '\b(sorry|admit)\b' -Quiet)

        if ($status -ne "-- STATUS: UNFINISHED" -and $hasSorry) {
            Write-Host "FAIL: Completed/partial file has sorry: $($file.Name)"
            $fail = $true
        }

        if ($Final -and $status -eq "-- STATUS: UNFINISHED") {
            Write-Host "FAIL: Unfinished exercise: $($file.Name)"
            $fail = $true
        }
    }
}

# CHECK 5: Final mode forbids all sorry placeholders
if ($Final) {
    Write-Host "[5] Running final proof completeness check..."

    $hits = @($files | Select-String -Pattern '\b(sorry|admit)\b')

    if ($hits.Count -gt 0) {
        Write-Host "FAIL: Proof placeholders remain."
        $hits | ForEach-Object { Write-Host $_ }
        $fail = $true
    }
}

# RESULT
Write-Host ""

if ($fail) {
    Write-Host "AUDIT FAILED" -ForegroundColor Red
    exit 1
}
else {
    Write-Host "ALL CHECKS PASSED" -ForegroundColor Green
    exit 0
}
