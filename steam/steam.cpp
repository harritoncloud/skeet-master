#include <iostream>
#include <Windows.h>
#include <TlHelp32.h>
#include <string>
#include <filesystem>
#include <vector>
#include "skCrypter.h"

static std::filesystem::path GetExecutableDirectory()
{
  wchar_t buffer[MAX_PATH]{};
  const DWORD length = GetModuleFileNameW(nullptr, buffer, MAX_PATH);
  if (!length || length >= MAX_PATH)
    return {};
  return std::filesystem::path(buffer).parent_path();
}

static void PrintLastError(const char* prefix)
{
  std::cout << prefix << " error=" << GetLastError() << '\n';
}

static std::filesystem::path GetLegacyCsgoPath()
{
  wchar_t steamPath[32768]{};
  DWORD steamPathBytes = sizeof(steamPath);

  auto status = RegGetValueW(HKEY_CURRENT_USER, L"Software\\Valve\\Steam", L"SteamPath",
    RRF_RT_REG_SZ, nullptr, steamPath, &steamPathBytes);
  if (status != ERROR_SUCCESS) {
    steamPathBytes = sizeof(steamPath);
    status = RegGetValueW(HKEY_LOCAL_MACHINE, L"SOFTWARE\\WOW6432Node\\Valve\\Steam",
      L"InstallPath", RRF_RT_REG_SZ, nullptr, steamPath, &steamPathBytes);
  }

  if (status != ERROR_SUCCESS)
    return {};

  auto path = std::filesystem::path(steamPath) / L"steamapps" / L"common" /
    L"Counter-Strike Global Offensive" / L"csgo.exe";
  return std::filesystem::exists(path) ? path : std::filesystem::path{};
}

static bool StartLegacyCsgo()
{
  const auto csgoPath = GetLegacyCsgoPath();
  if (csgoPath.empty()) {
    std::cout << "legacy csgo.exe was not found\n";
    return false;
  }

  std::wstring commandLine = L"\"" + csgoPath.wstring() + L"\" -steam -insecure";
  std::vector<wchar_t> writableCommand(commandLine.begin(), commandLine.end());
  writableCommand.push_back(L'\0');

  STARTUPINFOW startup{};
  startup.cb = sizeof(startup);
  PROCESS_INFORMATION process{};
  const auto workingDirectory = csgoPath.parent_path().wstring();

  if (!CreateProcessW(csgoPath.c_str(), writableCommand.data(), nullptr, nullptr, FALSE, 0,
      nullptr, workingDirectory.c_str(), &startup, &process)) {
    PrintLastError("failed to start legacy CS:GO");
    return false;
  }

  CloseHandle(process.hThread);
  CloseHandle(process.hProcess);
  return true;
}

static HANDLE GetProcessByName(const std::wstring& name)
{
  DWORD pid = 0;

  // Create toolhelp snapshot.
  HANDLE snapshot = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
  if (snapshot == INVALID_HANDLE_VALUE)
    return nullptr;

  PROCESSENTRY32 process;
  ZeroMemory(&process, sizeof(process));
  process.dwSize = sizeof(process);

  // Walkthrough all processes.
  if (Process32First(snapshot, &process))
  {
    do
    {
      // Compare process.szExeFile based on format of name, i.e., trim file path
      // trim .exe if necessary, etc.
      if (std::wstring(process.szExeFile) == std::wstring(name))
      {
        pid = process.th32ProcessID;
        break;
      }
    } while (Process32Next(snapshot, &process));
  }

  CloseHandle(snapshot);

  if (pid != 0)
  {
    return OpenProcess(PROCESS_CREATE_THREAD | PROCESS_QUERY_INFORMATION | PROCESS_VM_OPERATION |
      PROCESS_VM_WRITE | PROCESS_VM_READ, FALSE, pid);
  }
  return nullptr;
}

int main()
{
  SetConsoleTitleA(skCrypt("DONT RENAME skeet.dll!"));
  std::cout << skCrypt("DONT RENAME skeet.dll!\nEnter an -insecure in csgo params\nwaiting for csgo...\n");
  HANDLE hProc = nullptr;
  const auto executableDirectory = GetExecutableDirectory();
  if (executableDirectory.empty()) {
    PrintLastError("failed to resolve executable directory");
    system("pause");
    return 1;
  }

  auto dllPath = executableDirectory / L"skeet.dll";
  auto pathStr = dllPath.wstring();

  if (!std::filesystem::exists(dllPath)) {
    std::wcout << L"skeet.dll not found: " << pathStr << L'\n';
    system("pause");
    return 1;
  }

  hProc = GetProcessByName(L"csgo.exe");
  if (!hProc) {
    std::cout << skCrypt("starting legacy CS:GO...\n");
    if (!StartLegacyCsgo()) {
      system("pause");
      return 1;
    }
  }

  while (!hProc) {
    hProc = GetProcessByName(L"csgo.exe");
    if (!hProc)
      Sleep(500);
  }

  std::cout << skCrypt("csgo.exe found!\n");

  auto cheat = VirtualAllocEx(hProc, (void*)0x43310000, 0x2fc000, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);

  if (!cheat) {
    PrintLastError("failed to allocate cheat region");
    CloseHandle(hProc);
    system("pause");
    return 2;
  }

  const auto bytes = (pathStr.size() + 1) * sizeof(wchar_t);
  auto arg = VirtualAllocEx(hProc, 0, bytes, MEM_COMMIT | MEM_RESERVE, PAGE_EXECUTE_READWRITE);
  if (!arg) {
    PrintLastError("failed to allocate dll path");
    VirtualFreeEx(hProc, cheat, 0, MEM_RELEASE);
    CloseHandle(hProc);
    system("pause");
    return 3;
  }

  SIZE_T written = 0;
  if (!WriteProcessMemory(hProc, arg, pathStr.c_str(), bytes, &written) || written != bytes) {
    PrintLastError("failed to write dll path");
    VirtualFreeEx(hProc, arg, 0, MEM_RELEASE);
    VirtualFreeEx(hProc, cheat, 0, MEM_RELEASE);
    CloseHandle(hProc);
    system("pause");
    return 4;
  }

  const HMODULE kernel32 = GetModuleHandleA(skCrypt("kernel32.dll"));
  auto loadLibrary = reinterpret_cast<LPTHREAD_START_ROUTINE>(
    kernel32 ? GetProcAddress(kernel32, skCrypt("LoadLibraryW")) : nullptr);
  if (!loadLibrary) {
    PrintLastError("failed to resolve LoadLibraryW");
    VirtualFreeEx(hProc, arg, 0, MEM_RELEASE);
    VirtualFreeEx(hProc, cheat, 0, MEM_RELEASE);
    CloseHandle(hProc);
    system("pause");
    return 5;
  }

  auto hThread = CreateRemoteThread(hProc, 0, 0, loadLibrary, arg, 0, 0);
  if (!hThread) {
    PrintLastError("failed to create remote thread");
    VirtualFreeEx(hProc, arg, 0, MEM_RELEASE);
    VirtualFreeEx(hProc, cheat, 0, MEM_RELEASE);
    CloseHandle(hProc);
    system("pause");
    return 6;
  }

  if (WaitForSingleObject(hThread, INFINITE) != WAIT_OBJECT_0) {
    PrintLastError("failed while waiting for remote thread");
    CloseHandle(hThread);
    CloseHandle(hProc);
    system("pause");
    return 7;
  }

  DWORD remoteResult = 0;
  if (!GetExitCodeThread(hThread, &remoteResult)) {
    PrintLastError("failed to read remote thread result");
    CloseHandle(hThread);
    VirtualFreeEx(hProc, arg, 0, MEM_RELEASE);
    VirtualFreeEx(hProc, cheat, 0, MEM_RELEASE);
    CloseHandle(hProc);
    system("pause");
    return 8;
  }

  CloseHandle(hThread);
  VirtualFreeEx(hProc, arg, 0, MEM_RELEASE);

  if (!remoteResult) {
    std::cout << skCrypt("LoadLibraryW failed in csgo.exe\n");
    VirtualFreeEx(hProc, cheat, 0, MEM_RELEASE);
    CloseHandle(hProc);
    system("pause");
    return 9;
  }

  CloseHandle(hProc);
  std::cout << skCrypt("injected successfully\n");
  return 0;
}
