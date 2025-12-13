# Complete Installation: Agda + stdlib for DD

## Option 1: Via Chocolatey (recommended)

```powershell
# Install Chocolatey (if not present): https://chocolatey.org/install
# Then in PowerShell (Admin):

choco install ghc cabal git -y
cabal update
cabal install Agda
```

## Option 2: Via GHCup

```powershell
# Download: https://www.haskell.org/ghcup/
# Install GHC and Cabal
# Then:

cabal update
cabal install Agda
```

## After Installing Agda

Run the script:

```powershell
cd E:\claudecode\DD_v2
powershell -ExecutionPolicy Bypass -File install-agda-stdlib.ps1
```

Or manually:

```powershell
# 1. Clone stdlib
cd E:\claudecode\DD_v2
git clone --depth 1 --branch v1.7.3 https://github.com/agda/agda-stdlib.git

# 2. Configure
mkdir $env:USERPROFILE\.agda -Force
"E:\claudecode\DD_v2\agda-stdlib\standard-library.agda-lib" | Out-File $env:USERPROFILE\.agda\libraries
"standard-library" | Out-File $env:USERPROFILE\.agda\defaults

# 3. Verify
cd E:\claudecode\DD_v2\agda
agda DDWithStdlib.agda
```

## Verification

After installation, all these files should compile:

```
E:\claudecode\DD_v2\agda\
├── DDComplete.agda      ✓
├── DDWithStdlib.agda    ✓ (requires stdlib)
├── ThirdNecessity.agda  ✓
├── GoldenRatio.agda     ✓
├── DistCategory.agda    ✓
```

## Troubleshooting

### "agda not found"
- Add to PATH: `%APPDATA%\cabal\bin`
- Restart terminal

### "standard-library not found"
- Check that file `E:\claudecode\DD_v2\agda-stdlib\standard-library.agda-lib` exists
- Check contents of `%USERPROFILE%\.agda\libraries`

### "type-in-type" warning
- This is normal, we use `--type-in-type` intentionally for reflexivity
