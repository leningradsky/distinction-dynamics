# Run elan installer
$ErrorActionPreference = "Stop"
Set-Location $PSScriptRoot

# Download installer
Write-Host "Downloading elan installer..."
curl.exe -O --location "https://elan.lean-lang.org/elan-init.ps1"

# Run with parameters
Write-Host "Installing elan and Lean 4..."
& .\elan-init.ps1 -NoPrompt $true -DefaultToolchain "leanprover/lean4:stable"

# Cleanup
Remove-Item elan-init.ps1 -ErrorAction SilentlyContinue

Write-Host "Done! Please restart your terminal."
