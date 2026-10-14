# Thin Windows wrapper over `zig build` for this repository.
#
#   pwsh -File build.ps1 <step> [zig build args]
#   .\build.ps1 test -Doptimize=ReleaseFast
#
# - Runs tools\zig-x86_64-windows-0.16.0\zig.exe when that toolchain directory exists next to this
#   script, otherwise `zig` from PATH.
# - Runs in the repository root, so relative paths in the arguments resolve against it.
# - For each of -Dlune, -Dluau-compile, -Dluau-ast and -Dluau-analyze that the caller did not pass,
#   adds the option when the tool exists in the maintainers' workspace layout (lune.exe and
#   tools\luau-0.720\ in the directory four levels above this repository).
# - Never sets --prefix or the cache directories; callers pass them.
# - Passes every other argument, such as -Dz3=true -Dz3-dir=<path>, to zig build unchanged.

$ErrorActionPreference = 'Stop'
Set-StrictMode -Version 2.0

# PowerShell splits an argument such as -Dlune=C:\tools\lune.exe at the drive colon (from a prompt:
# '-Dlune=C:' and '\tools\lune.exe'; through pwsh -File: '-Dlune=C' and '\tools\lune.exe'). Join the
# two pieces again so zig receives the argument as it was typed.
# PowerShell also ends such a token at its first '.' ('-Dz3-dir=..\z3\z3-4.16.0-x64-win' arrives as '-Dz3-dir=' and '..\z3\z3-4.16.0-x64-win'); a piece that starts with '.' is joined back the same way.
$zigArgs = New-Object System.Collections.Generic.List[string]
for ($i = 0; $i -lt $args.Count; $i++) {
    $arg = [string]$args[$i]
    if ($i + 1 -lt $args.Count) {
        $next = [string]$args[$i + 1]
        if ($arg -match '^-D[^=]+=[A-Za-z]:$') {
            $zigArgs.Add($arg + $next)
            $i++
            continue
        }
        if ($arg -match '^-D[^=]+=[A-Za-z]$' -and $next -match '^[\\/]') {
            $zigArgs.Add($arg + ':' + $next)
            $i++
            continue
        }
        if ($arg -match '^-D[^=]+=' -and $next -match '^\.') {
            $zigArgs.Add($arg + $next)
            $i++
            continue
        }
    }
    $zigArgs.Add($arg)
}

$workspace = [System.IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..\..\..\..'))
$tools = [ordered]@{
    'lune'         = Join-Path $workspace 'lune.exe'
    'luau-compile' = Join-Path $workspace 'tools\luau-0.720\luau-compile.exe'
    'luau-ast'     = Join-Path $workspace 'tools\luau-0.720\luau-ast.exe'
    'luau-analyze' = Join-Path $workspace 'tools\luau-0.720\luau-analyze.exe'
}
$added = New-Object System.Collections.Generic.List[string]
foreach ($name in $tools.Keys) {
    $pattern = '^-D' + [regex]::Escape($name) + '(=|$)'
    $passed = @($zigArgs | Where-Object { $_ -match $pattern }).Count -gt 0
    if (-not $passed -and (Test-Path -LiteralPath $tools[$name] -PathType Leaf)) {
        $added.Add('-D' + $name + '=' + $tools[$name])
    }
}

$toolchain = Join-Path $PSScriptRoot 'tools\zig-x86_64-windows-0.16.0'
if (Test-Path -LiteralPath $toolchain -PathType Container) {
    $zig = Join-Path $toolchain 'zig.exe'
} else {
    $zig = 'zig'
}

$buildArgs = @('build') + @($added) + @($zigArgs)
Write-Host ('build.ps1: ' + $zig + ' ' + ($buildArgs -join ' '))
Push-Location -LiteralPath $PSScriptRoot
try {
    & $zig @buildArgs
    $status = $LASTEXITCODE
} finally {
    Pop-Location
}
exit $status
