#include "pch.h"
#define SDK_RENDERER_IMP
#include "SkeetSDK/skeetsdk.h"

#include <algorithm>
#include <cstdint>
#include <cstring>

using namespace SkeetSDK;

#if defined(_M_IX86)
namespace
{
struct TooltipOverlayState
{
    volatile LONG active = 0;
    int x = 0;
    int y = 0;
    wchar_t title[64] = {};
    wchar_t line1[160] = {};
    wchar_t line2[160] = {};
};

TooltipOverlayState g_tooltip_overlay;
EventListener* g_tooltip_listener = nullptr;

void copy_tooltip_text(const char* source, wchar_t* destination, int capacity)
{
    destination[0] = L'\0';
    if (!source || !source[0] || capacity <= 1)
        return;

    if (MultiByteToWideChar(CP_UTF8, 0, source, -1, destination, capacity) <= 0)
        MultiByteToWideChar(CP_ACP, 0, source, -1, destination, capacity);
    destination[capacity - 1] = L'\0';
}

void render_tooltip_overlay()
{
    if (InterlockedCompareExchange(&g_tooltip_overlay.active, 0, 0) == 0 ||
        !Menu || !(Menu->MenuStatus & MenuOpened))
    {
        return;
    }

    const auto title_size = Renderer::MeasureText(g_tooltip_overlay.title, TEXT_FLAG_BOLD);
    const auto line1_size = Renderer::MeasureText(g_tooltip_overlay.line1, TEXT_FLAG_SMALL);
    const auto line2_size = g_tooltip_overlay.line2[0]
        ? Renderer::MeasureText(g_tooltip_overlay.line2, TEXT_FLAG_SMALL)
        : Vec2{};

    int content_width = std::max(title_size.x, std::max(line1_size.x, line2_size.x));
    int width = std::max(190, std::min(content_width + 20, 320));
    int height = g_tooltip_overlay.line2[0] ? 58 : 44;
    int x = g_tooltip_overlay.x;
    int y = g_tooltip_overlay.y;

    const auto screen = Renderer::ScreenSize();
    x = std::max(6, std::min(x, screen.x - width - 6));
    y = std::max(6, std::min(y, screen.y - height - 6));

    const Vec2 position{ x, y };
    const Vec2 size{ width, height };
    Renderer::Rect({ x + 2, y + 2 }, size, { 0, 0, 0, 135 });
    Renderer::OutlinedRect(position, size, { 20, 20, 20, 248 }, { 72, 72, 72, 255 }, 1);
    Renderer::Triangle({ x - 7, y + 10 }, { x, y + 6 }, { x, y + 15 }, { 72, 72, 72, 255 });
    Renderer::Triangle({ x - 5, y + 10 }, { x, y + 8 }, { x, y + 13 }, { 20, 20, 20, 248 });
    Renderer::Text({ x + 9, y + 7 }, { 232, 232, 232, 255 }, g_tooltip_overlay.title, TEXT_FLAG_BOLD);
    Renderer::Text({ x + 9, y + 25 }, { 174, 174, 174, 255 }, g_tooltip_overlay.line1, TEXT_FLAG_SMALL);
    if (g_tooltip_overlay.line2[0])
        Renderer::Text({ x + 9, y + 39 }, { 174, 174, 174, 255 }, g_tooltip_overlay.line2, TEXT_FLAG_SMALL);
}

void initialize_tooltip_overlay()
{
    if (g_tooltip_listener)
        return;

    Renderer::InitFinal();
    g_tooltip_listener = Renderer::AddEvent(REVENT_FINAL, render_tooltip_overlay);
}

}
#endif

#if defined(_M_IX86)
extern "C" __declspec(dllexport) void __cdecl annesty_tooltip_set(
    int active,
    int x,
    int y,
    const char* title,
    const char* line1,
    const char* line2)
{
    InterlockedExchange(&g_tooltip_overlay.active, 0);
    if (!active)
        return;

    g_tooltip_overlay.x = x;
    g_tooltip_overlay.y = y;
    copy_tooltip_text(title, g_tooltip_overlay.title, _countof(g_tooltip_overlay.title));
    copy_tooltip_text(line1, g_tooltip_overlay.line1, _countof(g_tooltip_overlay.line1));
    copy_tooltip_text(line2, g_tooltip_overlay.line2, _countof(g_tooltip_overlay.line2));
    MemoryBarrier();
    InterlockedExchange(&g_tooltip_overlay.active, 1);
}

struct TooltipBridgeLocator
{
    std::uint8_t magic[16];
    decltype(&annesty_tooltip_set) bridge;
};

#pragma section(".text$annesty", execute, read)
extern "C" __declspec(dllexport) __declspec(allocate(".text$annesty"))
const TooltipBridgeLocator annesty_tooltip_locator = {
    { 0x41, 0x4E, 0x4E, 0x45, 0x53, 0x54, 0x59, 0x5F,
      0x54, 0x49, 0x50, 0x5F, 0x56, 0x37, 0x7F, 0xA7 },
    &annesty_tooltip_set
};
#endif

static PCTab find_menu_tab(ETab index)
{
    if (!Menu || !Menu->Tabs.data() || Menu->Tabs.size() > 16)
        return nullptr;

    if (Menu->TabsArr[index] && Menu->TabsArr[index]->Menu == Menu && Menu->TabsArr[index]->Header.Index == index)
        return Menu->TabsArr[index];

    for (auto tab : Menu->Tabs)
    {
        if (tab && tab->Menu == Menu && tab->Header.Index == index)
            return tab;
    }

    return nullptr;
}

struct TabLayoutState
{
    PCMenu menu = nullptr;
    bool captured = false;
    size_t count = 0;
    size_t legit_slot = static_cast<size_t>(-1);
    int shift = 0;
    PCTab tabs[16] = {};
    Vec2 pos[16] = {};
};

static TabLayoutState g_tab_layout;

static bool tab_layout_matches(PCTab legit_tab)
{
    if (!g_tab_layout.captured || g_tab_layout.menu != Menu ||
        g_tab_layout.legit_slot >= g_tab_layout.count ||
        !Menu || !Menu->Tabs.data() || Menu->Tabs.size() != g_tab_layout.count)
        return false;

    if (g_tab_layout.tabs[g_tab_layout.legit_slot] != legit_tab)
        return false;

    for (size_t i = 0; i < g_tab_layout.count; ++i)
    {
        if (Menu->Tabs[i] != g_tab_layout.tabs[i])
            return false;
    }

    return true;
}

static bool legit_tab_is_parked(PCTab legit_tab)
{
    if (!Menu || !legit_tab)
        return false;

    return legit_tab->Pos.x < Menu->Pos.x - 300 &&
        legit_tab->Pos.y < Menu->Pos.y - 300;
}

static int tab_visual_spacing(size_t slot)
{
    auto count = g_tab_layout.count;
    auto shift = 0;

    if (slot + 1 < count)
        shift = g_tab_layout.pos[slot + 1].y - g_tab_layout.pos[slot].y;
    else if (slot > 0)
        shift = g_tab_layout.pos[slot].y - g_tab_layout.pos[slot - 1].y;

    auto legit_tab = g_tab_layout.tabs[slot];
    if ((shift <= 0 || shift > 300) && legit_tab)
        shift = legit_tab->Size.y;

    if (shift <= 0 || shift > 300)
        shift = 48;

    return shift;
}

static bool capture_tab_layout()
{
    if (!Menu || !Menu->Tabs.data() || Menu->Tabs.size() <= LEGIT || Menu->Tabs.size() > 16)
        return false;

    auto count = Menu->Tabs.size();
    size_t legit_slot = static_cast<size_t>(-1);

    for (size_t i = 0; i < count; ++i)
    {
        auto tab = Menu->Tabs[i];
        if (!tab || tab->Menu != Menu)
            return false;

        g_tab_layout.tabs[i] = tab;
        g_tab_layout.pos[i] = tab->Pos;

        if (tab->Header.Index == LEGIT)
            legit_slot = i;
    }

    if (legit_slot == static_cast<size_t>(-1))
        return false;

    g_tab_layout.menu = Menu;
    g_tab_layout.count = count;
    g_tab_layout.legit_slot = legit_slot;
    g_tab_layout.shift = tab_visual_spacing(legit_slot);
    g_tab_layout.captured = true;
    return true;
}

static bool apply_legit_visual_compact()
{
    if (!g_tab_layout.captured || g_tab_layout.menu != Menu)
        return false;

    auto legit_slot = g_tab_layout.legit_slot;
    if (legit_slot >= g_tab_layout.count)
        return false;

    auto legit_tab = g_tab_layout.tabs[legit_slot];
    if (!legit_tab)
        return false;

    for (size_t i = 0; i < g_tab_layout.count; ++i)
    {
        auto tab = g_tab_layout.tabs[i];
        if (!tab)
            continue;

        if (i < legit_slot)
        {
            tab->Pos = g_tab_layout.pos[i];
        }
        else if (i > legit_slot)
        {
            tab->Pos = g_tab_layout.pos[i];
            tab->Pos.y -= g_tab_layout.shift;
        }
    }

    legit_tab->Pos.x = Menu->Pos.x - legit_tab->Size.x - 500;
    legit_tab->Pos.y = Menu->Pos.y - legit_tab->Size.y - 500;
    return true;
}

static bool hide_legit_tab_once()
{
    auto legit_tab = find_menu_tab(LEGIT);
    if (!legit_tab)
        return false;

    auto layout_changed = !tab_layout_matches(legit_tab) || !legit_tab_is_parked(legit_tab);
    if (layout_changed)
    {
        g_tab_layout.captured = false;
        if (!capture_tab_layout())
            return false;
    }

    legit_tab->Header.Flags.Visible = false;
    legit_tab->Header.Flags.Hovered = false;
    legit_tab->Header.Flags.AllowMouseInput = false;

    if (layout_changed && !apply_legit_visual_compact())
        return false;

    if (Menu->CurrentTab == LEGIT)
    {
        Menu->CurrentTab = RAGE;
    }

    return true;
}

static DWORD WINAPI hide_legit_tab_worker(LPVOID)
{
    auto last_dpi = *reinterpret_cast<volatile uint32_t*>(0x43475A94);

    while (GetModuleHandleA("client.dll"))
    {
        if (!Menu || !(Menu->MenuStatus & MenuOpened))
        {
            Sleep(100);
            continue;
        }

        auto current_dpi = *reinterpret_cast<volatile uint32_t*>(0x43475A94);
        if (current_dpi != last_dpi)
        {
            last_dpi = current_dpi;
            Sleep(75);
            g_tab_layout.captured = false;
            hide_legit_tab_once();
        }

        Sleep(100);
    }

    return 0;
}

static void remove_legit_tab()
{
    static bool started = false;
    if (started)
        return;

    started = true;
    hide_legit_tab_once();

    auto thread = CreateThread(nullptr, 0, hide_legit_tab_worker, nullptr, 0, nullptr);
    if (thread)
        CloseHandle(thread);
}

static void load_settings()
{
    InitAndWaitForSkeet();
    extern bool install_gameplay_patches();
    if (!install_gameplay_patches())
        LPRINT("[WARN] gameplay patches were not applied\n");
    initialize_tooltip_overlay();

    HKEY regkey;
    if (RegOpenKeyW(HKEY_CURRENT_USER, L"SOFTWARE", &regkey) != ERROR_SUCCESS) return;

    static void(__thiscall* setpossize)(CMenu*, uint32_t&) = reinterpret_cast<decltype(setpossize)>(Memory::CheatChunk.find("56 57 8B 7C 24 ?? 8B F1 ?? ?? ?? 0F 85"));
    static void(__thiscall* apply_dpi)(bool) = reinterpret_cast<decltype(apply_dpi)>(Memory::CheatChunk.find("55 8B EC 83 E4 ?? A1 ?? ?? ?? ?? 53"));

    DWORD size = 0x400;
    uint8_t* data = Memory::bytealloc.allocate(size);

    DWORD keytype;
    if (RegQueryValueExW(regkey, Menu->RegValueName, 0, &keytype, data, &size) == ERROR_SUCCESS)
    {
        if (keytype != REG_BINARY)
        {
            RegDeleteValueW(HKEY_CURRENT_USER, Menu->RegValueName);
            goto end;
        };

        auto* cursor = data;
        ConfigHead* header = reinterpret_cast<ConfigHead*>(cursor);

        if (size > sizeof(ConfigHead) && header->sig == SKEET_HEAD_SIGNATURE)
        {
            while ((uintptr_t)cursor - (uintptr_t)header < size)
            {
                ConfigDataUnit* cfg_unit = reinterpret_cast<ConfigDataUnit*>(cursor + sizeof(ConfigHead));
                switch (cfg_unit->data_type)
                {
                case LCOLOR:
                    *(uint32_t*)0x43468FB0 = cfg_unit->get_ref<uint32_t>();
                    Menu->Tabs[MISC]->Childs[2]->Elements[3]->GetAs<CPicker>()->OnConfigLoad();
                    break;
                case LPOSSIZE:
                    setpossize(Menu, cfg_unit->get_ref<uint32_t>());
                    break;
                case LBOOL:
                    *(bool*)0x43475798 = cfg_unit->get_ref<bool>();
                    break;
                case LHOTKEY:
                    *(uint32_t*)0x43478DC8 = cfg_unit->get_ref<uint32_t>();
                    break;
                case LARRAY:
                    memcpy(Menu->OnStartupHash, cfg_unit->data, cfg_unit->data_size);
                    break;
                case LINTEGER:
                    switch (cfg_unit->hash)
                    {
                    case 0x1F495BA0:
                        Menu->Size.x = cfg_unit->get_ref<int>();
                        break;
                    case 0xEAA92CD1:
                        Menu->Size.y = cfg_unit->get_ref<int>();
                        break;
                    case 0x27BA18FA:
                        *(uint32_t*)0x43475A94 = cfg_unit->get_ref<uint32_t>();
                        apply_dpi(true);
                        break;
                    case 0xD3F1456E:
                        *(bool*)0x43467E4B = cfg_unit->get_ref<bool>();
                        break;
                    default:
                        LPRINT(std::hex << cfg_unit->hash << ' ' << std::dec << cfg_unit->get_ref<uint32_t>() << '\n');
                        break;
                    };
                    break;
                default:
                    break;
                };

                cursor += sizeof(ConfigDataUnit) + cfg_unit->data_size;
            };
        };
    }
end:
    RegCloseKey(regkey);
    Memory::bytealloc.deallocate(data, 0);
    remove_legit_tab();
};


static decltype(load_settings)* fn = &load_settings;
__declspec(naked) __declspec(noreturn) void LoadStub()
{
    __asm
    {
        mov eax, fn
        call eax
        mov eax, 0x434938FF
        jmp eax
    };
};
