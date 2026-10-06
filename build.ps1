param([string]$XeLaTeX = 'xelatex', [string]$BibTeX = 'bibtex')
$ErrorActionPreference = 'Stop'
$manuscriptProject = $PSScriptRoot
function Invoke-CheckedProgram {
    param([string]$Program, [string[]]$ProgramArguments)
    $manuscriptCommandOutput = & $Program @ProgramArguments 2>&1
    $manuscriptCommandExit = $LASTEXITCODE
    if ($manuscriptCommandExit -ne 0) { throw ("Build command failed: $Program`n" + (($manuscriptCommandOutput | Select-Object -Last 50) -join "`n")) }
    Write-Output (([System.IO.Path]::GetFileName($Program)) + ' completed.')
}
function Build-ManuscriptDocument {
    param([string]$DocumentDirectory)
    Push-Location -LiteralPath $DocumentDirectory
    try {
        $latexArguments = @('-interaction=nonstopmode','-halt-on-error','-file-line-error','-synctex=0','main.tex')
        Invoke-CheckedProgram $XeLaTeX $latexArguments
        Invoke-CheckedProgram $BibTeX @('main')
        Invoke-CheckedProgram $XeLaTeX $latexArguments
        Invoke-CheckedProgram $XeLaTeX $latexArguments
    } finally { Pop-Location }
}
Build-ManuscriptDocument (Join-Path $manuscriptProject 'supplement')
Build-ManuscriptDocument (Join-Path $manuscriptProject 'paper')
$manuscriptOutput = Join-Path $manuscriptProject 'output/pdf'
New-Item -ItemType Directory -Path $manuscriptOutput -Force | Out-Null
Copy-Item -LiteralPath (Join-Path $manuscriptProject 'paper/main.pdf') -Destination (Join-Path $manuscriptOutput 'Seymour_Manuscript_2026-10-07.pdf')
Copy-Item -LiteralPath (Join-Path $manuscriptProject 'supplement/main.pdf') -Destination (Join-Path $manuscriptOutput 'Seymour_Supplement_2026-10-07.pdf')
Write-Output "Built manuscript and supplement in $manuscriptOutput"
