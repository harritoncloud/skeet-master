# skeet-master

Minimal buildable source tree for the x86 client DLL and companion launcher.

## Repository layout

- `skeet/` - DLL source, generated headers, VM bytecode, and required payload resources.
- `steam/` - companion launcher source.
- `skeet.sln` - Visual Studio solution containing both projects.

Build outputs, backups, reverse databases, recovery exports, and audit workspaces are intentionally excluded.

## Requirements

- Git LFS
- Visual Studio 2022 or newer
- MSVC v143 toolset
- Windows 10 SDK

Clone the required payloads before building:

```powershell
git lfs install
git lfs pull
```

Build the x86 release configuration:

```powershell
msbuild skeet.sln /m /p:Configuration=Release /p:Platform=x86 /p:PlatformToolset=v143
```

The committed MinHook library and files under `skeet/Binary` and `skeet/VM` are required build inputs, not generated output.

