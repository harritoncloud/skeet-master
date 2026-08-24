#include <bit>
#include "pch.h"
#include "Binary/pattern.h"
#include "Binary/initializer.h"
#include "Binary/menu_fonts.h"
#include "VM/recompilation.h"
#include "ntstructs.h"
#include "Binary/mem_int3.h"
#include "Binary/menu.h"
#include <thread>
#include "skCrypter.h"
#include "resource.h"

FILETIME ftime = {};

namespace {
struct exact_patch_t {
    uintptr_t address;
    const uint8_t* expected;
    const uint8_t* replacement;
    size_t size;
};

static bool is_readable_range(uintptr_t address, size_t size)
{
    if (address == 0 || size == 0 ||
        address > static_cast<uintptr_t>(-1) - (size - 1)) {
        return false;
    }

    const uintptr_t end = address + size;
    uintptr_t cursor = address;
    while (cursor < end) {
        MEMORY_BASIC_INFORMATION mbi = {};
        if (VirtualQuery(reinterpret_cast<const void*>(cursor), &mbi,
            sizeof(mbi)) != sizeof(mbi)) {
            return false;
        }

        if (mbi.State != MEM_COMMIT ||
            (mbi.Protect & (PAGE_GUARD | PAGE_NOACCESS)) != 0) {
            return false;
        }

        const uintptr_t region_start =
            reinterpret_cast<uintptr_t>(mbi.BaseAddress);
        const uintptr_t region_end = region_start + mbi.RegionSize;
        if (region_end <= cursor)
            return false;

        cursor = region_end < end ? region_end : end;
    }

    return true;
}

static bool write_code_bytes(const exact_patch_t& patch, const uint8_t* bytes)
{
    auto target = reinterpret_cast<uint8_t*>(patch.address);
    DWORD old_protection = 0;
    if (!VirtualProtect(target, patch.size, PAGE_EXECUTE_READWRITE,
        &old_protection)) {
        return false;
    }

    if (patch.size == sizeof(LONG) &&
        (patch.address % sizeof(LONG)) == 0) {
        LONG value = 0;
        memcpy(&value, bytes, sizeof(value));
        InterlockedExchange(reinterpret_cast<volatile LONG*>(target), value);
    }
    else {
        memcpy(target, bytes, patch.size);
    }

    DWORD unused_protection = 0;
    const BOOL protection_restored = VirtualProtect(
        target, patch.size, old_protection, &unused_protection);
    const BOOL cache_flushed = FlushInstructionCache(
        GetCurrentProcess(), target, patch.size);

    return protection_restored && cache_flushed &&
        memcmp(target, bytes, patch.size) == 0;
}

template <size_t PatchCount>
static bool install_patch_set(const exact_patch_t (&patches)[PatchCount])
{
    bool needs_write[PatchCount] = {};
    bool changed[PatchCount] = {};

    // Validate the complete set before changing any instruction.
    for (size_t i = 0; i < PatchCount; ++i) {
        const auto& patch = patches[i];
        if (!is_readable_range(patch.address, patch.size))
            return false;

        const auto target = reinterpret_cast<const uint8_t*>(patch.address);
        if (memcmp(target, patch.replacement, patch.size) == 0)
            continue;
        if (memcmp(target, patch.expected, patch.size) != 0)
            return false;

        needs_write[i] = true;
    }

    for (size_t i = 0; i < PatchCount; ++i) {
        if (!needs_write[i])
            continue;

        changed[i] = true;
        if (!write_code_bytes(patches[i], patches[i].replacement)) {
            for (size_t rollback = i + 1; rollback > 0; --rollback) {
                const size_t index = rollback - 1;
                if (changed[index])
                    write_code_bytes(patches[index], patches[index].expected);
            }
            return false;
        }
    }

    for (size_t i = 0; i < PatchCount; ++i) {
        const auto& patch = patches[i];
        if (memcmp(reinterpret_cast<const void*>(patch.address),
            patch.replacement, patch.size) == 0) {
            continue;
        }

        for (size_t rollback = PatchCount; rollback > 0; --rollback) {
            const size_t index = rollback - 1;
            if (changed[index])
                write_code_bytes(patches[index], patches[index].expected);
        }
        return false;
    }

    return true;
}

#if defined(_M_IX86)
static volatile LONG force_defensive_state = 0;
static volatile LONG force_defensive_token = 0;
static volatile LONG force_defensive_mark_ms = 0;

static void __stdcall mark_force_defensive(uintptr_t state, LONG token)
{
    InterlockedExchange(&force_defensive_token, token);
    InterlockedExchange(&force_defensive_mark_ms,
        static_cast<LONG>(GetTickCount()));
    InterlockedExchange(&force_defensive_state, static_cast<LONG>(state));
}

static BOOL __stdcall consume_force_defensive(uintptr_t state, LONG token)
{
    const LONG expected_state = static_cast<LONG>(state);
    const LONG marked_state = InterlockedCompareExchange(
        &force_defensive_state, 0, 0);
    if (marked_state != expected_state)
        return FALSE;

    const LONG marked_token = InterlockedCompareExchange(
        &force_defensive_token, 0, 0);
    if (marked_token != token) {
        InterlockedCompareExchange(&force_defensive_state, 0, marked_state);
        return FALSE;
    }

    const DWORD marked_at = static_cast<DWORD>(InterlockedCompareExchange(
        &force_defensive_mark_ms, 0, 0));
    if (GetTickCount() - marked_at > 250u) {
        InterlockedCompareExchange(&force_defensive_state, 0, marked_state);
        return FALSE;
    }

    return InterlockedCompareExchange(
        &force_defensive_state, 0, marked_state) == marked_state;
}

// Probe the command flag at the native force-defensive branch. The original
// TEST is repeated immediately before control returns so its flags stay exact.
static __declspec(naked) void force_defensive_probe_stub()
{
    __asm {
        test dword ptr [esi], 20000000h
        jz resume_original_test

        pushad
        push dword ptr [edi + 128h]
        push edi
        call mark_force_defensive
        popad

    resume_original_test:
        test dword ptr [esi], 20000000h
        push 43366E97h
        ret
    }
}

// A forced defensive shift must not spend the normal DT recharge cursor.
// All other shifts execute the untouched cursor-debit instructions.
static __declspec(naked) void force_defensive_cursor_stub()
{
    __asm {
        pushad
        push dword ptr [esi + 128h]
        push esi
        call consume_force_defensive
        test eax, eax
        jz restore_original_cursor_debit

        popad
        mov ecx, dword ptr [esi + 104h]
        push 4335B6EAh
        ret

    restore_original_cursor_debit:
        popad
        xor ecx, ecx
        cmp dword ptr [esi + 0F4h], ecx
        push 4335B6D9h
        ret
    }
}

static void make_relative_jump(uint8_t* bytes, size_t size,
    uintptr_t source, uintptr_t destination)
{
    memset(bytes, 0x90, size);
    bytes[0] = 0xE9;
    const uint32_t displacement = static_cast<uint32_t>(destination) -
        static_cast<uint32_t>(source + 5);
    memcpy(bytes + 1, &displacement, sizeof(displacement));
}
#endif
}

bool install_force_defensive_recharge_fix()
{
#if defined(_M_IX86)
    static const uintptr_t force_probe_address = 0x43366E91;
    static const uintptr_t cursor_debit_address = 0x4335B6D1;
    static const uint8_t force_probe_expected[] = {
        0xF7, 0x06, 0x00, 0x00, 0x00, 0x20
    };
    static const uint8_t cursor_debit_expected[] = {
        0x33, 0xC9, 0x39, 0x8E, 0xF4, 0x00, 0x00, 0x00
    };

    uint8_t force_probe_replacement[sizeof(force_probe_expected)] = {};
    uint8_t cursor_debit_replacement[sizeof(cursor_debit_expected)] = {};
    make_relative_jump(force_probe_replacement,
        sizeof(force_probe_replacement), force_probe_address,
        reinterpret_cast<uintptr_t>(&force_defensive_probe_stub));
    make_relative_jump(cursor_debit_replacement,
        sizeof(cursor_debit_replacement), cursor_debit_address,
        reinterpret_cast<uintptr_t>(&force_defensive_cursor_stub));

    const exact_patch_t patches[] = {
        { force_probe_address, force_probe_expected,
            force_probe_replacement, sizeof(force_probe_expected) },
        { cursor_debit_address, cursor_debit_expected,
            cursor_debit_replacement, sizeof(cursor_debit_expected) }
    };
    return install_patch_set(patches);
#else
    return false;
#endif
}

bool install_gameplay_patches()
{
    static const uint8_t spread_expected[] = { 0x7B, 0x26 };
    static const uint8_t spread_replacement[] = { 0xEB, 0x26 };

    // Keep Auto Peek's defensive flag, but let a valid DT-release command
    // rebuild the shot/stop-ready bits that Auto Peek clears earlier.
    static const uint8_t autopeek_dt_gate_expected[] = {
        0x25, 0x03, 0x00, 0x00
    };
    static const uint8_t autopeek_dt_gate_replacement[] = {
        0x00, 0x00, 0x00, 0x00
    };
    static const uint8_t autopeek_dt_gate_opcode[] = { 0x0F, 0x85 };

    const exact_patch_t patches[] = {
        { 0x4331FC12, spread_expected, spread_replacement,
            sizeof(spread_expected) },
        { 0x4335B11A, autopeek_dt_gate_opcode,
            autopeek_dt_gate_opcode, sizeof(autopeek_dt_gate_opcode) },
        { 0x4335B11C, autopeek_dt_gate_expected,
            autopeek_dt_gate_replacement,
            sizeof(autopeek_dt_gate_expected) }
    };
    return install_patch_set(patches);
}

std::uint8_t* PatternScan(void* module, const char* signature)
{
  static auto pattern_to_byte = [](const char* pattern) {
    auto bytes = std::vector<int>{};
    auto start = const_cast<char*>(pattern);
    auto end = const_cast<char*>(pattern) + strlen(pattern);

    for (auto current = start; current < end; ++current) {
      if (*current == '?') {
        ++current;
        if (*current == '?')
          ++current;
        bytes.push_back(-1);
      }
      else {
        bytes.push_back(strtoul(current, &current, 16));
      }
    }
    return bytes;
    };

  auto dosHeader = (PIMAGE_DOS_HEADER)module;
  auto ntHeaders = (PIMAGE_NT_HEADERS)((std::uint8_t*)module + dosHeader->e_lfanew);

  auto sizeOfImage = ntHeaders->OptionalHeader.SizeOfImage;
  auto patternBytes = pattern_to_byte(signature);
  auto scanBytes = reinterpret_cast<std::uint8_t*>(module);

  auto s = patternBytes.size();
  auto d = patternBytes.data();

  for (auto i = 0ul; i < sizeOfImage - s; ++i) {
    bool found = true;
    for (auto j = 0ul; j < s; ++j) {
      if (scanBytes[i + j] != d[j] && d[j] != -1) {
        found = false;
        break;
      }
    }
    if (found) {
      return &scanBytes[i];
    }
  }
  return nullptr;
}

static bool handle_int3(CONTEXT* ctx, ctx_t* dump_ctx) {
    auto skeet = skeet_t::getInstance();

    auto offset = static_cast<int32_t>(dump_ctx->offset);
    auto size = static_cast<int32_t>(dump_ctx->size);

     if(offset > 0) {
         ctx->Esp -= size;
     }
     else if (offset < 0) {
         ctx->Esp += size;
     }

    if ((dump_ctx->current_rip == 0x43493904 || dump_ctx->current_rip == 0x43493908)) {
        if (!skeet_t::is_stack_range(dump_ctx->rax) || skeet_t::is_image_range(dump_ctx->rax))
            ctx->Eax = dump_ctx->rax;
        //if (!skeet_t::is_stack_range(dump_ctx->rbx) || skeet_t::is_image_range(dump_ctx->rbx))
        //    ctx->Ebx = dump_ctx->rbx;
        //if (!skeet_t::is_stack_range(dump_ctx->rdi) || skeet_t::is_image_range(dump_ctx->rdi))
        //    ctx->Edi = dump_ctx->rdi;
        //if (!skeet_t::is_stack_range(dump_ctx->rsi) || skeet_t::is_image_range(dump_ctx->rsi))
        //    ctx->Esi = dump_ctx->rsi;
        //if (!skeet_t::is_stack_range(dump_ctx->rbp) || skeet_t::is_image_range(dump_ctx->rbp))
        //    ctx->Ebp = dump_ctx->rbp;
        //if (!skeet_t::is_stack_range(dump_ctx->rcx) || skeet_t::is_image_range(dump_ctx->rcx))
        //    ctx->Ecx = dump_ctx->rcx;
        //if (!skeet_t::is_stack_range(dump_ctx->rdx) || skeet_t::is_image_range(dump_ctx->rdx))
        //    ctx->Edx = dump_ctx->rdx;

        if (dump_ctx->current_rip == 0x43493908) {
            std::memcpy((void*)ctx->Esi, menuBin, sizeof(menuBin));
        }
    }
    else if (dump_ctx->current_rip == 0x43493900) {
        if (!skeet_t::is_stack_range(dump_ctx->rax) || skeet_t::is_image_range(dump_ctx->rax))
            ctx->Eax = dump_ctx->rax;
    }


    if (dump_ctx->current_rip == 0x43493900 || dump_ctx->current_rip == 0x434938FC) {
        ctx->Eax = (u32)skeet_t::getInstance()->menuFonts() + (dump_ctx->rax - 0x940000);
    }
    if (dump_ctx->rip == 0x43482439) {
        ctx->Ebp = (u32)((u32)GetModuleHandleA("client.dll") + 0xDB61DC);
    }
    

    ctx->Eip = dump_ctx->rip;

    if (dump_ctx->rbp == 0x6CD10000)
        ctx->Ebp = (u32)GetModuleHandleA("comctl32.dll");

    if (dump_ctx->rbp == 0x285b0000)
        ctx->Ebp = (u32)GetModuleHandleA("client.dll");

     return true;
}

static Value fromERegToContext(ereg reg, CONTEXT& ctx) {
    switch (reg) {
    case ereg::eax:
        return Value(&ctx.Eax, 4);
    case ereg::ebx:
        return Value(&ctx.Ebx, 4);
    case ereg::ecx:
        return Value(&ctx.Ecx, 4);
    case ereg::edx:
        return Value(&ctx.Edx, 4);
    case ereg::esi:
        return Value(&ctx.Esi, 4);
    case ereg::edi:
        return Value(&ctx.Edi, 4);
    case ereg::ebp:
        return Value(&ctx.Ebp, 4);
    case ereg::esp:
        return Value(&ctx.Esp, 4);
    }
}

Value Operand::get(CONTEXT& ctx)
{
    switch (type) {
    case etype::reg:
        return fromERegToContext(reg, ctx);
    case etype::imm:
        return Value(&this->imm, 4);
    case etype::mem:
        return Value((void*)this->imm, 4);
    }
}

void Handler::handle(CONTEXT& ctx)
{
    if (ctx.Eip == 0x43495251) {
      std::memcpy((void*)ctx.Eax, initialization_info, sizeof(initialization_info));
    }

    switch (this->mnem) {
    case emnemonic::mov: {
        auto op1 = this->operands[0].get(ctx);
        auto op2 = this->operands[1].get(ctx);

        op1.setValue(op2.value());
        break;
    }
    case emnemonic::push: {
        auto op1 = this->operands[0].get(ctx);

        ctx.Esp -= 4;
        *(uint32_t*)(ctx.Esp) = op1.value();
        break;
    }
    case emnemonic::call: {
        auto op1 = this->operands[0].get(ctx);

        ctx.Esp -= 4;
        *(uint32_t*)(ctx.Esp) = this->addr +this->len;
        ctx.Eip = op1.value();
        return;
    }
    }
    ctx.Eip += this->len;
}

static PCONTEXT saver;

static LONG __stdcall skeet_exception_handler(EXCEPTION_POINTERS* ExceptionInfo) {
    auto exception_ctx = ExceptionInfo->ContextRecord;
    static int i = 0;
    if (exception_ctx->Eip == 0x434938FF)
    {
        i++;
        if (i == 314)
        {
            saver = new CONTEXT;
            memcpy(saver, exception_ctx, sizeof(CONTEXT));
            extern void LoadStub();
            exception_ctx->Eip = (DWORD)LoadStub;
            return EXCEPTION_CONTINUE_EXECUTION;
        }
        else if (i == 315)
        {
            memcpy(exception_ctx, saver, sizeof(CONTEXT));
            delete saver;
        };
    };

    if (ExceptionInfo->ExceptionRecord->ExceptionCode != EXCEPTION_BREAKPOINT) {
      if (ExceptionInfo->ExceptionRecord->ExceptionCode == EXCEPTION_ACCESS_VIOLATION) {
        std::wstring msg = std::format(L"access violation at 0x{:x}\nPress CTRL + C and send to the topic", exception_ctx->Eip);
        MessageBoxW(0, msg.c_str(), L"error", MB_ICONWARNING);
      }
      return EXCEPTION_CONTINUE_SEARCH;
    }

    static int c = 0;
    auto& ctx = contexts[c];
    if (exception_ctx->Eip >= skeet_t::getInstance()->base() && exception_ctx->Eip < skeet_t::getInstance()->base() + skeet_t::getInstance()->size()) {
        auto it = std::find_if(handlers.begin(), handlers.end(), [&](const Handler& other) {
            return exception_ctx->Eip >= other.addr && exception_ctx->Eip < other.addr + other.len;
            });

        if (it == handlers.end()) {
            if (!(exception_ctx->Eip >= ctx.current_rip - 5 && exception_ctx->Eip < ctx.current_rip + 5)) {
                auto it = std::find_if(contexts.begin() + c, contexts.end(), [&](const ctx_t& ctx) {
                    return exception_ctx->Eip >= ctx.current_rip - 1 && exception_ctx->Eip < ctx.current_rip + 1;
                    });

                if (it == contexts.end()) {

                    auto it = std::find_if(removedHandlers.begin(), removedHandlers.end(), [&](const removed_handler_t& other) {
                        return other.vip == exception_ctx->Ebp;
                        });

                    if (it == removedHandlers.end())
                        return EXCEPTION_CONTINUE_SEARCH;

                    exception_ctx->Edi -= 4;
                    *(uint32_t*)exception_ctx->Edi = it->value;
                    exception_ctx->Ebx = it->key;
                    exception_ctx->Ebp += 8;
                    exception_ctx->Esi = it->next_handler;
                    exception_ctx->Eip = it->next_handler;
                    return EXCEPTION_CONTINUE_EXECUTION;
                }

                ctx = *it;
                c = it - contexts.begin();
            }

            c++;

            if (!handle_int3(exception_ctx, &ctx)) {
                MessageBoxA(0, "undefined behaviour", "error", 2);
                return EXCEPTION_CONTINUE_SEARCH;
            }
            LPRINT(skCrypt("[INFO]") << std::dec << c - 1 << " | " << std::hex << " [RAX]: " << ctx.rax << " |  rip handling... " << ctx.current_rip << " to rip " << ctx.rip << " | total size " << std::dec << contexts.size() << "\n");
        }
        else {
            it->handle(*exception_ctx);
        }

        return EXCEPTION_CONTINUE_EXECUTION;
    }
    return EXCEPTION_CONTINUE_SEARCH;
}

void entry_thread() {
    return ((void(__stdcall*)())0x1337)();
}

static vm_element_t parse_vm_element(const nlohmann::json& json) {
    static std::map<std::string, eoperation> op_correspondence = {
        { "ROL", eoperation::ROL },
        { "DEC", eoperation::DEC },
        { "NOT", eoperation::NOT },
        { "BSWAP", eoperation::BSWAP },
        { "ADD", eoperation::ADD },
        { "XOR", eoperation::XOR },
        { "ROR", eoperation::ROR },
        { "INC", eoperation::INC },
        { "NEG", eoperation::NEG },
        { "SUB", eoperation::SUB }
    };
    vm_element_t element = {};

    element.addr = json["address"].get<uint32_t>();
    element.encryption_key = json["key"].get<uint32_t>();

    for (const nlohmann::json& operation : json["operations"]) {
        vm_operation_t vm_op = {};

        vm_op.addr = std::stoull(operation[0].get<std::string>());

        vm_op.operation = op_correspondence[operation[1]];

        vm_op.value = std::stoul(operation[2].get<std::string>());

        element.operations.push_back(vm_op);
    }

    element.size = json["size"];
    element.value = json["value"];
    element.vip = json["vip"];

    return element;
}
skeet_t::skeet_t(HMODULE base) : _base(0x43310000), page(nullptr), _stack(nullptr) {
    if (singleton)
        return;

    singleton = this;

    HRSRC hRes = FindResource(base, MAKEINTRESOURCE(IDR_BINARY1), skCrypt(L"BINARY"));

    HGLOBAL hResData = LoadResource(base, hRes);

    LPVOID pData = LockResource(hResData);
    DWORD size = SizeofResource(base, hRes);

    _size = size;
    
    skeet_bin = new char[size];

    std::memcpy(skeet_bin, pData, size);

    hRes = FindResource(base, MAKEINTRESOURCE(IDR_EXPORTS1), skCrypt(L"EXPORTS"));

    hResData = LoadResource(base, hRes);

    pData = LockResource(hResData);
    size = SizeofResource(base, hRes);

    std::string strFileExports((char*)pData, size);

    nlohmann::json jsExports = nlohmann::json::parse(strFileExports);

    for (const auto& [addr, value] : jsExports.items()) {
        import_t import_;
        import_.old_addr = static_cast<uint32_t>(std::stoul(addr));
        for (const auto& [lib, api] : value.items()) {
            import_.lib = lib;
            import_.name = api;
        }
        exports[import_.old_addr] = import_;
    }

    hRes = FindResource(base, MAKEINTRESOURCE(IDR_BYTECODE1), skCrypt(L"BYTECODE"));

    hResData = LoadResource(base, hRes);

    pData = LockResource(hResData);
    size = SizeofResource(base, hRes);

    std::string strFileBytecode((char*)pData, size);

    nlohmann::json jsBytecode = nlohmann::json::parse(strFileBytecode);

    for (const auto& unit : jsBytecode) {
        if (unit["main"].empty())
            continue;

        std::vector<vm_element_t> infoHandlers;

        infoHandlers.push_back(parse_vm_element(unit["main"]));

        if (unit.contains("others")) {
            for (const nlohmann::json& other : unit["others"]) {
                infoHandlers.push_back(parse_vm_element(other));
            }
        }

        handlers.push_back(infoHandlers);
    }

    skeetFonts = VirtualAlloc(0, sizeof(menu_fonts), MEM_RESERVE | MEM_COMMIT, PAGE_EXECUTE_READWRITE);
    std::memcpy(skeetFonts, menu_fonts, sizeof(menu_fonts));
}

bool skeet_t::map()
{
    //page = VirtualAlloc(reinterpret_cast<void*>(_base), _size, MEM_RESERVE | MEM_COMMIT, PAGE_EXECUTE_READWRITE);
    //if (!page)
    //    return false;
    page = (void*)_base;
    _size = 0x2fc000;
    try {
        memcpy(page, skeet_bin, _size);
    }
    catch (...) {
        return false;
    }

    return true;
}

bool skeet_t::fix_imports()
{
    for (auto& _import : imports) {
        auto old_addr = 0;

        switch (*(uint8_t*)(_import.rip)) {
            case 0xe8:
            case 0xe9: {
                old_addr = *(u32*)(_import.rip + 1) + _import.rip + 5;
                break;
            }
            default: {
                old_addr = *(u32*)(_import.rip + 1);
                break;
            }
        }

        if (exports.find(old_addr) == exports.end())
            LPRINT("(fix_imports) failed to get " << std::hex << old_addr << "\n");

        auto& export_ = exports[old_addr];

        auto import_addr = (u32)(GetProcAddress(LoadLibraryA(export_.lib.c_str()), export_.name.c_str()));

        if (!import_addr) {
            LPRINT("(fix_imports) failed to get " << std::hex << export_.lib.c_str() << " " << export_.name.c_str() << "\n");
            return false;
        }
        
        switch (*(uint8_t*)(_import.rip)) {
        case 0xe8:
        case 0xe9: {
            *(u32*)(_import.rip + 1) = import_addr - _import.rip - 5;
            break;
        }
        default: {
            *(u32*)(_import.rip + 1) = import_addr;
            break;
        }
        }
    }
    return true;
}

using HkRecoverFn = int(__fastcall*)(int base, int size);
HkRecoverFn detourCrcCheck = nullptr;

static int __fastcall crcCheck(int base, int size) {

    if (base == 0x4331E000 && size == 0x105B12) {
        return 0x20547A5B ^ 0x92CA5DF1;
    }
    return detourCrcCheck(base, size);
}

bool skeet_t::extra()
{
    //if(MH_Initialize() != MH_STATUS::MH_OK) 
    //    return false;

    // hash
    const uint32_t hashes[] = {
        0xC0BA92C9,
        0xBBFFA7E0,
        0xA42BE2F8
    };

    std::thread([&]() {
        int c = 0;
        while (*(uint32_t*)(0x4346D4CC) == 0 && c < 3) {
            *(uint32_t*)(0x4346D4CC) = hashes[c];
        }
        }).detach();

    LPRINT(skCrypt("[INFO] adding exception handler...\n"));
    AddVectoredExceptionHandler(0, skeet_exception_handler);
    LPRINT(skCrypt("[INFO] added!\n"));
    memcpy((void*)0x43490c82, "\xC7\x02\x00\x00\x00\x00\xC3", sizeof("\xC7\x02\x00\x00\x00\x00\xC3") - 1);


    *(uint8_t*)0x43466D7C = 0xeb;
    *(uint8_t*)0x4348B4FC = 0xeb;

    auto hWnd = FindWindowA("Valve001", "Counter-Strike: Global Offensive - Direct3D 9");
    *(uint32_t*)0x433A068A = (uint32_t)hWnd;
    *(uint32_t*)0x4341F644 = (uint32_t)hWnd;
    *(uint32_t*)0x4341F7C0 = (uint32_t)hWnd;

    memset((void*)0x4350F0C7, 0x90, 5);

    *(uint32_t*)0x43467F64 = ((u32)GetModuleHandleA("shaderapidx9.dll") + 0xA62C0);

    // dont devirt, maybe checks
    *(uint32_t*)(0x4346837C) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0x2BDC20);
    *(uint32_t*)(0x43467570) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0x2BD020);
    *(uint32_t*)(0x43468234) = (uint32_t)((uint32_t)GetModuleHandleA("studiorender.dll") + 0x57DF0);
    *(uint32_t*)(0x43468C98) = (uint32_t)((uint32_t)GetModuleHandleA("studiorender.dll") + 0x44E2EC);

    *(uint32_t*)(0x434670AC) = (uint32_t)((uint32_t)GetModuleHandleA("matchmaking.dll"));
    *(uint32_t*)(0x434670E4) = (uint32_t)((uint32_t)GetModuleHandleA("server.dll"));
    *(uint32_t*)(0x4346762C) = (uint32_t)((uint32_t)GetModuleHandleA("panoramauiclient.dll"));
    *(uint32_t*)(0x43467AFC) = (uint32_t)((uint32_t)GetModuleHandleA("vguimatsurface.dll"));
    *(uint32_t*)(0x43467B74) = (uint32_t)((uint32_t)GetModuleHandleA("filesystem_stdio.dll"));
    *(uint32_t*)(0x43467DAC) = (uint32_t)((uint32_t)GetModuleHandleA("inputsystem.dll"));
    *(uint32_t*)(0x4346889C) = (uint32_t)((uint32_t)GetModuleHandleA("vgui2.dll"));
    *(uint32_t*)(0x43468A7C) = (uint32_t)((uint32_t)GetModuleHandleA("vstdlib.dll"));
    *(uint32_t*)(0x43468B74) = (uint32_t)((uint32_t)GetModuleHandleA("vphysics.dll"));
    *(uint32_t*)(0x43468D08) = (uint32_t)((uint32_t)GetModuleHandleA("gameoverlayrenderer.dll"));
    *(uint32_t*)(0x43468D20) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll"));
    *(uint32_t*)(0x43468D40) = (uint32_t)((uint32_t)GetModuleHandleA("soundsystem.dll"));
    *(uint32_t*)(0x43468D98) = (uint32_t)((uint32_t)GetModuleHandleA("datacache.dll"));
    *(uint32_t*)(0x43469234) = (uint32_t)((uint32_t)GetModuleHandleA("panorama.dll"));
    *(uint32_t*)(0x4346A55C) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll"));
    *(uint32_t*)(0x4346A600) = (uint32_t)((uint32_t)GetModuleHandleA("materialsystem.dll"));
    *(uint32_t*)(0x4346A604) = (uint32_t)((uint32_t)GetModuleHandleA("shaderapidx9.dll"));
    *(uint32_t*)(0x4346A650) = (uint32_t)((uint32_t)GetModuleHandleA("studiorender.dll"));

    //
    *(uint32_t*)(0x434693F0) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll") + 0x43E9E0);
    *(uint32_t*)(0x43467F0C) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll") + 0x443481);

    *(uint32_t*)(0x43468E44) = **(uint32_t**)((uint32_t)GetModuleHandleA("engine.dll") + 0x23790);
    *(uint32_t*)(0x4346D4D0) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0xB7550);

    *(uint32_t*)(0x4346D4C8) = (uint32_t)((uint32_t)GetModuleHandleA("materialsystem.dll") + 0xBBF4);
    *(uint32_t*)(0x4346D4C4) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0x1A3656);
    *(uint32_t*)(0x4346D4C0) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0x59E9CC);

    *(uint32_t*)(0x434689A0) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll") + 0x2F10D3);
    *(uint32_t*)(0x4346A454) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0xD99C0);
    *(uint32_t*)(0x434674E0) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll") + 0x4123AC);
    *(uint32_t*)(0x43468518) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll") + 0x52EFAC);
    *(uint32_t*)(0x434688C4) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll") + 0x4413A0);


    *(uint32_t*)(0x4346D668) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0x00228908);
    *(uint32_t*)(0x4346D66C) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0x000F03FD);
    *(uint32_t*)(0x43468B9C) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll") + 0x00712740);


    *(uint32_t*)(0x4346A31C) = (uint32_t)((uint32_t)GetModuleHandleA("localize.dll") + 0x00038A70);

    *(uint32_t*)(0x43468B2C) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0x52C810);
    *(uint32_t*)(0x43467288) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0x22F08F);
    *(uint32_t*)(0x4346728C) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll") + 0x9A2CF0);
    *(uint32_t*)(0x4346728C) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll") + 0xDF14C0);
    *(uint32_t*)(0x4346D540) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll") + 0x3DC9B0);
    *(uint32_t*)(0x43476A40) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0x52B270);
    *(uint32_t*)(0x434671B4) = (uint32_t)((uint32_t)GetModuleHandleA("engine.dll") + 0x52B248);
    *(uint32_t*)(0x434678C4) = (uint32_t)((uint32_t)GetModuleHandleA("client.dll") + 0x2C8F50);
    *(uint32_t*)0x43468B9C = ((uint32_t)GetModuleHandleA("client.dll") + 0x712740);
    *(uint32_t*)0x43467C04 = ((uint32_t)GetModuleHandleA("client.dll") + 0x5344CE0);
    *(uint32_t*)0x43467040 = ((uint32_t)GetModuleHandleA("client.dll") + 0x70ADB0);
    *(uint32_t*)0x43468994 = ((uint32_t)GetModuleHandleA("client.dll") + 0x523BC98);

    *(uint32_t*)0x4346D67C = ((uint32_t)GetModuleHandleA("panorama.dll") + 0x9E220);
    *(uint32_t*)0x4346D680 = ((uint32_t)GetModuleHandleA("panorama.dll") + 0x9A320);
    *(uint32_t*)0x4346D684 = ((uint32_t)GetModuleHandleA("panorama.dll") + 0xA1B80);
    *(uint32_t*)0x4346D688 = ((uint32_t)GetModuleHandleA("panorama.dll") + 0xA3C80);
    *(uint32_t*)0x4346D68C = ((uint32_t)GetModuleHandleA("panorama.dll") + 0xAB6F0);

    *(uint32_t*)0x43468D0C = ((uint32_t)GetModuleHandleA("client.dll") + 0xDF14C0);
    *(uint32_t*)0x43467A70 = ((uint32_t)GetModuleHandleA("client.dll") + 0xDF14D4);
    *(uint32_t*)0x43468D50 = ((uint32_t)GetModuleHandleA("client.dll") + 0x5334E08);

    *(uint32_t*)0x4346D560 = ((uint32_t)GetModuleHandleA("engine.dll") + 0x8E55C);
    *(uint32_t*)0x4346D55C = ((uint32_t)GetModuleHandleA("engine.dll") + 0x22BE36);

    *(uint32_t*)0x4346A374 = ((uint32_t)GetModuleHandleA("client.dll") + 0x2D3A40);
    *(uint32_t*)0x4346D65C = ((uint32_t)GetModuleHandleA("client.dll") + 0x346AC0);
    *(uint32_t*)0x4346D660 = ((uint32_t)GetModuleHandleA("client.dll") + 0x344610);
    *(uint32_t*)0x4346A624 = ((uint32_t)GetModuleHandleA("client.dll") + 0x52632C8);
    *(uint32_t*)0x4346A364 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1D94A0);
    *(uint32_t*)0x434679AC = ((uint32_t)GetModuleHandleA("client.dll") + 0x9A6740);
    *(uint32_t*)0x4346A38C = ((uint32_t)GetModuleHandleA("client.dll") + 0x1D2CA0);
    *(uint32_t*)0x434683D0 = ((uint32_t)GetModuleHandleA("client.dll") + 0xDACC0F);
    *(uint32_t*)0x43468F80 = ((uint32_t)GetModuleHandleA("client.dll") + 0x432E20);
    *(uint32_t*)0x434688C8 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1EA950);
    *(uint32_t*)0x4346A6B0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1D1BA0);
    *(uint32_t*)0x43468C10 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1AEC40);
    *(uint32_t*)0x43467C58 = ((uint32_t)GetModuleHandleA("client.dll") + 0x5334DA4);
    *(uint32_t*)0x43467E44 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1EA790);
    *(uint32_t*)0x4346A598 = ((uint32_t)GetModuleHandleA("client.dll") + 0x442740);
    *(uint32_t*)0x43467C48 = ((uint32_t)GetModuleHandleA("client.dll") + 0x307260);
    *(uint32_t*)0x43468F30 = ((uint32_t)GetModuleHandleA("client.dll") + 0x320BD0);
    *(uint32_t*)0x434691DC = ((uint32_t)GetModuleHandleA("client.dll") + 0x9A2C40);
    *(uint32_t*)0x4346830C = ((uint32_t)GetModuleHandleA("client.dll") + 0xDF7FC0);
    *(uint32_t*)0x4346A3A4 = ((uint32_t)GetModuleHandleA("client.dll") + 0x5334764);
    *(uint32_t*)0x4346A4F8 = ((uint32_t)GetModuleHandleA("client.dll") + 0x19D140);
    *(uint32_t*)0x434678C8 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1D9440);
    *(uint32_t*)0x4346832C = ((uint32_t)GetModuleHandleA("client.dll") + 0x1B1AC0);
    *(uint32_t*)0x43467CF0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x7DE760);
    *(uint32_t*)0x43467B54 = ((uint32_t)GetModuleHandleA("client.dll") + 0x526388C);
    *(uint32_t*)0x43468C3C = ((uint32_t)GetModuleHandleA("client.dll") + 0x7DEB00);



    *(uint32_t*)0x43467000 = ((uint32_t)GetModuleHandleA("client.dll") + 0x32C0A59);
    *(uint32_t*)0x434693B0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x292CA6C);
    *(uint32_t*)0x4346A770 = ((uint32_t)GetModuleHandleA("client.dll") + 0x4F741CB);
    *(uint32_t*)0x43469198 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1F4E28D);
    *(uint32_t*)0x43469060 = ((uint32_t)GetModuleHandleA("client.dll") + 0x5332374);
    //*(uint32_t*)0x43468BE8 = ((uint32_t)GetModuleHandleA("client.dll") + 0x3374AD0);
    //*(uint32_t*)0x43468ED4 = ((uint32_t)GetModuleHandleA("client.dll") + 0x2491B42);
    *(uint32_t*)0x434688C8 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1EA950);
    *(uint32_t*)0x43467CF0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x7DE760);
    *(uint32_t*)0x4346830C = ((uint32_t)GetModuleHandleA("client.dll") + 0xDF7FC0);
    *(uint32_t*)0x4346728C = ((uint32_t)GetModuleHandleA("client.dll") + 0x9A2CF0);
    *(uint32_t*)0x43468C10 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1AEC40);
    *(uint32_t*)0x4346A3A4 = ((uint32_t)GetModuleHandleA("client.dll") + 0x5334764);
    *(uint32_t*)0x4346D628 = ((uint32_t)GetModuleHandleA("panorama.dll") + 0x3DFE0);
    *(uint32_t*)0x4346D62C = ((uint32_t)GetModuleHandleA("panorama.dll") + 0x3E020);
    *(uint32_t*)0x43467C48 = ((uint32_t)GetModuleHandleA("client.dll") + 0x307260);
    *(uint32_t*)0x4346D658 = ((uint32_t)GetModuleHandleA("client.dll") + 0x52448F8);
    *(uint32_t*)0x4346D65C = ((uint32_t)GetModuleHandleA("client.dll") + 0x346AC0);
    *(uint32_t*)0x43467E44 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1EA790);
    *(uint32_t*)0x4346A5DC = ((uint32_t)GetModuleHandleA("client.dll") + 0x3E2E673);
    *(uint32_t*)0x43468994 = ((uint32_t)GetModuleHandleA("client.dll") + 0x523BC98);
    //*(uint32_t*)0x43467A48 = ((uint32_t)GetModuleHandleA("client.dll") + 0x2FB9A4F);
    *(uint32_t*)0x4346A7CC = ((uint32_t)GetModuleHandleA("engine.dll") + 0x20CE50);
    *(uint32_t*)0x4346A374 = ((uint32_t)GetModuleHandleA("client.dll") + 0x2D3A40);
    *(uint32_t*)0x4346D67C = ((uint32_t)GetModuleHandleA("panorama.dll") + 0x9E220);
    *(uint32_t*)0x4346D680 = ((uint32_t)GetModuleHandleA("panorama.dll") + 0x9A320);
    *(uint32_t*)0x4346D688 = ((uint32_t)GetModuleHandleA("panorama.dll") + 0xA3C80);
    *(uint32_t*)0x43468FF0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x3231380);
    *(uint32_t*)0x434679EC = ((uint32_t)GetModuleHandleA("client.dll") + 0xE10580);
    *(uint32_t*)0x43467F0C = ((uint32_t)GetModuleHandleA("client.dll") + 0x443481);
    *(uint32_t*)0x4346D664 = ((uint32_t)GetModuleHandleA("client.dll") + 0x525E110);
    *(uint32_t*)0x43468250 = ((uint32_t)GetModuleHandleA("client.dll") + 0x5334848);
    *(uint32_t*)0x4346A64C = ((uint32_t)GetModuleHandleA("engine.dll") + 0xD9A18);
    *(uint32_t*)0x43468390 = ((uint32_t)GetModuleHandleA("client.dll") + 0x12170B3);
    *(uint32_t*)0x43467550 = ((uint32_t)GetModuleHandleA("engine.dll") + 0x8DAB0);
    *(uint32_t*)0x43468F80 = ((uint32_t)GetModuleHandleA("client.dll") + 0x432E20);
    *(uint32_t*)0x434688C4 = ((uint32_t)GetModuleHandleA("client.dll") + 0x4413A0);
    *(uint32_t*)0x43468B9C = ((uint32_t)GetModuleHandleA("client.dll") + 0x712740);
    *(uint32_t*)0x43468C94 = ((uint32_t)GetModuleHandleA("client.dll") + 0x52BF6D8);
    *(uint32_t*)0x434688A4 = ((uint32_t)GetModuleHandleA("client.dll") + 0x215080);
    *(uint32_t*)0x4346A624 = ((uint32_t)GetModuleHandleA("client.dll") + 0x52632C8);
    *(uint32_t*)0x434689A0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x2F10D3);
    *(uint32_t*)0x434692F4 = ((uint32_t)GetModuleHandleA("client.dll") + 0x430D0E);
    *(uint32_t*)0x4346D64C = ((uint32_t)GetModuleHandleA("client.dll") + 0x4364D0);
    *(uint32_t*)0x434691DC = ((uint32_t)GetModuleHandleA("client.dll") + 0x9A2C40);
    *(uint32_t*)0x4346D660 = ((uint32_t)GetModuleHandleA("client.dll") + 0x344610);
    *(uint32_t*)0x434688C0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x525D440);
    *(uint32_t*)0x43467DDC = ((uint32_t)GetModuleHandleA("client.dll") + 0x43C750);
    *(uint32_t*)0x43468308 = ((uint32_t)GetModuleHandleA("engine.dll") + 0x2A5982);
    *(uint32_t*)0x434679AC = ((uint32_t)GetModuleHandleA("client.dll") + 0x9A6740);
    *(uint32_t*)0x4346D684 = ((uint32_t)GetModuleHandleA("panorama.dll") + 0xA1B80);
    *(uint32_t*)0x4346D68C = ((uint32_t)GetModuleHandleA("panorama.dll") + 0xAB6F0);




    *(uint32_t*)0x4346A884 = ((uint32_t)GetModuleHandleA("client.dll") + 0x2A78A0);
    *(uint32_t*)0x43468E88 = ((uint32_t)GetModuleHandleA("client.dll") + 0x2A77E0);
    *(uint32_t*)0x4346A7F0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x28CC90);
    *(uint32_t*)0x43467040 = ((uint32_t)GetModuleHandleA("client.dll") + 0x70ADB0);
    //*(uint32_t*)0x4346A480 = ((uint32_t)GetModuleHandleA("client.dll") + 0x48E2CA4);
    *(uint32_t*)0x4346A724 = ((uint32_t)GetModuleHandleA("engine.dll") + 0x1791916);
    *(uint32_t*)0x43472B64 = ((uint32_t)GetModuleHandleA("engine.dll") + 0x2AC6E69);
    *(uint32_t*)0x4346EF18 = ((uint32_t)GetModuleHandleA("engine.dll") + 0x2AC6E69);
    *(uint32_t*)0x4346D558 = ((uint32_t)GetModuleHandleA("engine.dll") + 0x38FDCC8);
    *(uint32_t*)0x434674E0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x4123AC);
    *(uint32_t*)0x4346756C = ((uint32_t)GetModuleHandleA("client.dll") + 0x5B1E2E);
    //*(uint32_t*)0x43467C58 = ((uint32_t)GetModuleHandleA("client.dll") + 0x5334DA4);
    *(uint32_t*)0x4346832C = ((uint32_t)GetModuleHandleA("client.dll") + 0x1B1AC0);
    *(uint32_t*)0x43468FA4 = ((uint32_t)GetModuleHandleA("client.dll") + 0x5334C84);
    *(uint32_t*)0x4346A364 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1D94A0);
    //*(uint32_t*)0x4346FF78 = ((uint32_t)GetModuleHandleA("engine.dll") + 0x2AC6E69);
    *(uint32_t*)0x43468320 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1E69D0);
    *(uint32_t*)0x4346A6B0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1D1BA0);
    //*(uint32_t*)0x43467A44 = ((uint32_t)GetModuleHandleA("client.dll") + 0x23B5D03);
    
    *(uint32_t*)0x43467EF4 = ((uint32_t)GetModuleHandleA("client.dll") + 0xE047DC);
    
    *(uint32_t*)0x434670C4 = ((uint32_t)GetModuleHandleA("client.dll") + 0x525EBC4);
    
    //*(uint32_t*)0x4346FE0C = ((uint32_t)GetModuleHandleA("engine.dll") + 0x2AC6E69);
    *(uint32_t*)0x43468C3C = ((uint32_t)GetModuleHandleA("client.dll") + 0x7DEB00);
    *(uint32_t*)0x43468CA4 = ((uint32_t)GetModuleHandleA("client.dll") + 0x7DE8A0);
    *(uint32_t*)0x434693F0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x43E9E0);
    *(uint32_t*)0x434683D0 = ((uint32_t)GetModuleHandleA("client.dll") + 0xDACC0F);
    //*(uint32_t*)0x43468D50 = ((uint32_t)GetModuleHandleA("client.dll") + 0x5334E08);
    *(uint32_t*)0x43469348 = ((uint32_t)GetModuleHandleA("client.dll") + 0x36CAC0);
    *(uint32_t*)0x4346A4F8 = ((uint32_t)GetModuleHandleA("client.dll") + 0x19D140);
    *(uint32_t*)0x434679C0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x525CAA0);
    //*(uint32_t*)0x43468418 = ((uint32_t)GetModuleHandleA("client.dll") + 0x2491B42);
    //*(uint32_t*)0x43467B54 = ((uint32_t)GetModuleHandleA("client.dll") + 0x526388C);
    *(uint32_t*)0x4346A454 = ((uint32_t)GetModuleHandleA("engine.dll") + 0xD99C0);
    *(uint32_t*)0x43468F30 = ((uint32_t)GetModuleHandleA("client.dll") + 0x320BD0);
    *(uint32_t*)0x43468DC0 = ((uint32_t)GetModuleHandleA("client.dll") + 0x19D600);
    *(uint32_t*)0x43469370 = ((uint32_t)GetModuleHandleA("engine.dll") + 0x159296);
    *(uint32_t*)0x4346A82C = ((uint32_t)GetModuleHandleA("client.dll") + 0x3D1820);
    *(uint32_t*)0x43468518 = ((uint32_t)GetModuleHandleA("client.dll") + 0x52EFAC);
    *(uint32_t*)0x43469304 = ((uint32_t)GetModuleHandleA("client.dll") + 0x535E4CC);
    *(uint32_t*)0x43467288 = ((uint32_t)GetModuleHandleA("engine.dll") + 0x22F08F);
    *(uint32_t*)0x4346746C = ((uint32_t)GetModuleHandleA("engine.dll") + 0x1C5D7D3);
    *(uint32_t*)0x4346A598 = ((uint32_t)GetModuleHandleA("client.dll") + 0x442740);
    *(uint32_t*)0x434678C8 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1D9440);
    //*(uint32_t*)0x43468DFC = ((uint32_t)GetModuleHandleA("client.dll") + 0x5058269);
    *(uint32_t*)0x43468D6C = ((uint32_t)GetModuleHandleA("engine.dll") + 0x8CD5F0);
    //*(uint32_t*)0x434679A4 = ((uint32_t)GetModuleHandleA("engine.dll") + 0x1B76092);
    *(uint32_t*)0x4346A7E4 = ((uint32_t)GetModuleHandleA("client.dll") + 0x5344B38);
    *(uint32_t*)0x4346A38C = ((uint32_t)GetModuleHandleA("client.dll") + 0x1D2CA0);
    *(uint32_t*)0x4346D644 = ((uint32_t)GetModuleHandleA("client.dll") + 0x1E8100);

    *(uint32_t*)0x4346A898 = ((uint32_t)GetModuleHandleA("client.dll") + 0xDF98A0);
    
    uint32_t ret_addr = (uint32_t)PatternScan(GetModuleHandleA("gameoverlayrenderer.dll"), "3D ? ? ? ? 73 ? 68 ? ? ? ? E8 ? ? ? ? 8B 0D ? ? ? ? 83 C4 ? ? ? 6A ? FF 50 ? 3B 5F");
    if (!ret_addr)
        ret_addr = (uint32_t)PatternScan(GetModuleHandleA("gameoverlayrenderer.dll"), "3D ? ? ? ? 73 1A 68 ? ? ? ? E8 ? ? ? ? 8B 0D ? ? ? ? 83 C4 04 8B 01 6A 00 FF 50 14 3B 7B 3C");
    
    *(uint32_t*)0x43468D94 = ret_addr;

    uint32_t xref = (uint32_t)PatternScan(GetModuleHandleA("gameoverlayrenderer.dll"), "89 3D ? ? ? ? F3 0F 10 87");

    if (!xref)
        xref = (uint32_t)PatternScan(GetModuleHandleA("gameoverlayrenderer.dll"), "89 1D ? ? ? ? F3 0F 10 83");

    if (!xref)
        MessageBoxW(0, L"failed to find pattern[0]", L"error", 0);

    *(uint32_t*)0x43468350 = *(uint32_t*)(xref + 2);

    LPRINT(skCrypt("[INFO] recompiling vm...\n"));
    recompile();
    LPRINT(skCrypt("[INFO] recompiled!\n"));
    return true;
}

bool skeet_t::entry()
{
    DWORD tid = 0;
    auto hThread = CreateThread(0, 0, reinterpret_cast<LPTHREAD_START_ROUTINE>(entry_thread), 0, CREATE_SUSPENDED, &tid);

    if (hThread == INVALID_HANDLE_VALUE)
        return false;

    _stack = VirtualAlloc(nullptr, 0x100000, MEM_RESERVE | MEM_COMMIT, PAGE_EXECUTE_READWRITE);

    CONTEXT ctx = {};
    ctx.ContextFlags = CONTEXT_FULL;
    ctx.Esp = (uint32_t)_stack + 0x20000;
    ctx.Eip = 0x43481e2c;
    ctx.Esi = 0x43481e2c;
    ctx.Edi = 0x43481e2c;

    typedef struct _LSA_UNICODE_STRING { USHORT Length;	USHORT MaximumLength; PWSTR  Buffer; } UNICODE_STRING, * PUNICODE_STRING;
    typedef struct _OBJECT_ATTRIBUTES { ULONG Length; HANDLE RootDirectory; PUNICODE_STRING ObjectName; ULONG Attributes; PVOID SecurityDescriptor;	PVOID SecurityQualityOfService; } OBJECT_ATTRIBUTES, * POBJECT_ATTRIBUTES;
    using myNtCreateSection = NTSTATUS(NTAPI*)(OUT PHANDLE SectionHandle, IN ULONG DesiredAccess, IN POBJECT_ATTRIBUTES ObjectAttributes OPTIONAL, IN PLARGE_INTEGER MaximumSize OPTIONAL, IN ULONG PageAttributess, IN ULONG SectionAttributes, IN HANDLE FileHandle OPTIONAL);

    myNtCreateSection fNtCreateSection = (myNtCreateSection)(GetProcAddress(GetModuleHandleA("ntdll.dll"), "NtCreateSection"));

    SIZE_T size = 0x00100000;
    LARGE_INTEGER sectionSize = { size };
    HANDLE sectionHandle = NULL;
    PVOID localSectionAddress = NULL, remoteSectionAddress = NULL;

    fNtCreateSection(&sectionHandle, SECTION_MAP_READ | SECTION_MAP_WRITE | SECTION_MAP_EXECUTE, NULL, (PLARGE_INTEGER)&sectionSize, PAGE_EXECUTE_READWRITE, SEC_COMMIT, NULL);

    *(uint32_t*)(ctx.Esp + 0xC) = (uint32_t)sectionHandle;

    SetThreadContext(hThread, &ctx);

    ResumeThread(hThread);

    CloseHandle(hThread);
    return true;
}

uint32_t reverse_emulate(eoperation action, int size, uint32_t op1, uint32_t op2) {
    switch (action) {
    case eoperation::ROL: {
        switch (size) {
        case 1:
            return std::rotr<uint8_t>(op1, op2);
        case 2:
            return std::rotr<uint16_t>(op1, op2);
        case 4:
            return std::rotr<uint32_t>(op1, op2);
        }
    }
    case eoperation::ROR: {

        switch (size) {
        case 1:
            return std::rotl<uint8_t>(op1, op2);
        case 2:
            return std::rotl<uint16_t>(op1, op2);
        case 4:
            return std::rotl<uint32_t>(op1, op2);
        }
    }
    case eoperation::BSWAP: {

        switch (size) {
        case 1:
            return std::byteswap<uint8_t>(op1);
        case 2:
            return std::byteswap<uint16_t>(op1);
        case 4:
            return std::byteswap<uint32_t>(op1);
        }
    }
    case eoperation::INC: {
        return op1 - 1;
    }
    case eoperation::DEC: {
        return op1 + 1;
    }
    case eoperation::SUB: {

        switch (size) {
        case 1:
            return static_cast<uint8_t>(op1 + op2);
        case 2:
            return static_cast<uint16_t>(op1 + op2);
        case 4:
            return static_cast<uint32_t>(op1 + op2);
        }
    }
    case eoperation::ADD: {

        switch (size) {
        case 1:
            return static_cast<uint8_t>(op1 - op2);
        case 2:
            return static_cast<uint16_t>(op1 - op2);
        case 4:
            return static_cast<uint32_t>(op1 - op2);
        }
    }
    case eoperation::NOT: {
        switch (size) {
        case 1:
            return static_cast<uint8_t>(~op1);
        case 2:
            return static_cast<uint16_t>(~op1);
        case 4:
            return static_cast<uint32_t>(~op1);
        }
    }
    case eoperation::XOR: {

        switch (size) {
        case 1:
            return static_cast<uint8_t>(op1 ^ op2);
        case 2:
            return static_cast<uint16_t>(op1 ^ op2);
        case 4:
            return static_cast<uint32_t>(op1 ^ op2);
        }
    }
    case eoperation::NEG: {

        switch (size) {
        case 1:
            return static_cast<uint8_t>(0 - op1);
        case 2:
            return static_cast<uint16_t>(0 - op1);
        case 4:
            return static_cast<uint32_t>(0 - op1);
        }
    }
    }
}

uint32_t fnv1a(const std::wstring& data) {
    const uint32_t FNV_prime = 0x1000193;
    const uint32_t offset_basis = 0x811C9DC5;
    uint32_t hash = offset_basis;

    for (wchar_t c : data) {
        hash ^= c;             // XOR ñ òåêóùèì áàéòîì äàííûõ
        hash *= FNV_prime;     // Óìíîæàåì íà êîíñòàíòó FNV_prime
    }

    return hash;
}

void SubtractMinutesFromSystemTime(int minutes, FILETIME& ft) {
    ULARGE_INTEGER li;
    li.LowPart = ft.dwLowDateTime;
    li.HighPart = ft.dwHighDateTime;

    const ULONGLONG intervalsPerMinute = 60 * 10000000ULL;

    li.QuadPart += (minutes * intervalsPerMinute);

    ft.dwLowDateTime = li.LowPart;
    ft.dwHighDateTime = li.HighPart;
}

void skeet_t::recompile()
{
    // VIP -> PATCH MAP
    std::map<uint32_t, uint32_t> patches;

    patches[0x000000004349D3E2] = (u32)GetModuleHandleA("ntdll.dll");

    GetSystemTimeAsFileTime(&ftime);
    SubtractMinutesFromSystemTime(10, ftime);
    auto arg1 = ftime.dwLowDateTime - 0x0D53E8000;
    auto arg2 = ftime.dwHighDateTime - 0x19DB1DE;
    auto time_check = ((int(__stdcall*)(int arg1, int arg2, int arg3, int arg4))0x433AE31E)(arg1, arg2, 0x989680, 0);
    patches[0x000000004353C3D1] = time_check;

    auto crc_hash = ((int(__fastcall*)(int base, int size))0x4333D6A2)(0x4331E000, 0x105B12);
    patches[0x00000000434C6B29] = crc_hash ^ 0x92CA5DF1;

    patches[0x00000000434EB360] = GetCurrentProcessId();

    patches[0x00000000435507ED] = time_check;

    PPEB peb = (PPEB)(__readfsdword(0x30));

    auto ldr_entry = peb->Ldr;

    PLDR_DATA_TABLE_ENTRY entry = (PLDR_DATA_TABLE_ENTRY)ldr_entry->InLoadOrderModuleList->Flink;

    auto val = *(uint32_t*)((uint32_t)entry + 0x88) - 0xD53E8000;
    auto val2 = *(uint32_t*)((uint32_t)entry + 0x8c) - 0x19DB1DE;
    time_check = ((int(__stdcall*)(int arg1, int arg2, int arg3, int arg4))0x433AE31E)(val, val2, 0x989680, 0);

    patches[0x000000004352A5D6] = time_check;

    SetEnvironmentVariable(L"STEAMID", L"7612345678901");

    patches[0x000000004356C0A1] = fnv1a(L"7612345678901");

    patches[0x000000004352EE8F] = *(uint16_t*)0x7FFE0260;


    int cpu_info[4] = {};
    __cpuidex(cpu_info, 1, 0);

    patches[0x434bc39e] = cpu_info[2];
    patches[0x4356afc4] = cpu_info[2];
    patches[0x000000004352C91C] = cpu_info[2];

    patches[0x000000004351B2B5] = (u32)GetModuleHandleA("ntdll.dll");

    patches[0x434d4faa] = (u32)GetCurrentProcessId();

    uint32_t hash = 0;
    for (uint32_t i = 0x80000002; i <= 0x80000004; i++) {
        __cpuidex(cpu_info, i, 0);

        hash += cpu_info[0] + cpu_info[1] + cpu_info[2] + cpu_info[3];
    }

    auto it = std::find_if(removedHandlers.begin(), removedHandlers.end(), [](const removed_handler_t& other) {
        return other.vip == 0x000000004359257D;
        });

    it->value = hash;
    patches[0x43507C7F] = hash;

    patches[0x435194de] = (u32)GetModuleHandleA("kernel32.dll");

    uint32_t hashKUserSharedData = 0x811C9DC5;

    for (int i = 0; i < 0x40; i++) {
        unsigned char byte = *(unsigned char*)(0x7FFE0274 + i);

        uint32_t tmpValue = byte + i;
        tmpValue = tmpValue ^ hashKUserSharedData;
        hashKUserSharedData = tmpValue * 0x1000193;
    }

    patches[0x434eb732] = hashKUserSharedData;

    patches[0x435469B5] = (uint32_t)GetModuleHandleA("kernelbase.dll");

    for (int i = 0; i < handlers.size(); i++) {
        auto& handlers_info = handlers[i];

        if (patches.find(handlers_info[0].vip) != patches.end()) {
            handlers_info[0].value = patches[handlers_info[0].vip];
        }
        else {
            auto import_dest = handlers_info[0].value;

            if (exports.find(import_dest) != exports.end()) {
                auto& export_ = exports[import_dest];

                handlers_info[0].value = (u32)GetProcAddress(LoadLibraryA(export_.lib.c_str()), export_.name.c_str());
            }
            else {
                LPRINT("failed to get " << std::hex << import_dest << " VIP " << handlers_info[0].vip << "\n");
            }
        }

        uint32_t encryption_key = handlers_info[0].encryption_key;

        for (auto& handler_info : handlers_info) {

            if (!skeet_t::is_image_range(handler_info.vip))
                continue;

            uint32_t value = handler_info.value;
            uint8_t size = handler_info.size;

            for (auto it = handler_info.operations.rbegin(); it != handler_info.operations.rend(); it++) {
                value = reverse_emulate(it->operation, size, value, it->value);
            }
            switch (size) {
            case 4:
                value ^= encryption_key;
                *(uint32_t*)handler_info.vip = value;
                break;
            case 2:
                value ^= static_cast<uint16_t>(encryption_key);
                *(uint16_t*)handler_info.vip = value;
                break;
            case 1:
                value ^= static_cast<uint8_t>(encryption_key);
                *(uint8_t*)handler_info.vip = value;
                break;
            }
            encryption_key ^= static_cast<uint32_t>(handler_info.value);
            //LPRINT(skCrypt("[INFO] patched vip at ") << std::hex << handler_info.vip << skCrypt(" with value ") << handler_info.value);
        }
    }
}

skeet_t* skeet_t::getInstance(HMODULE base)
{
    if (!singleton)
        singleton = new skeet_t(base);
        
    return singleton;
}

bool skeet_t::is_stack_range(u32 addr)
{
    auto skeet = getInstance();

    return addr >= 0x10D0000 && addr < 0x10D0000 + 0x100000;
}

bool skeet_t::is_image_range(u32 addr)
{
    auto skeet = getInstance();

    return addr >= skeet->base() && addr < skeet->base() + skeet->size();
}

bool skeet_t::is_exception(u32 addr)
{
    if(addr >= 0x434F8532 && addr <= 0x434F853A)
        return true;
    return false;
}
