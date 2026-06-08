import os
import struct
import sys
import tkinter as tk
from tkinter import messagebox

SCREEN_W = 240
SCREEN_H = 160
CYCLES_PER_FRAME = 280896
CYCLES_PER_SCANLINE = 1232
VDRAW_LINES = 160
TOTAL_LINES = 228

# I/O register offsets (from 0x04000000)
REG_DISPCNT = 0x000
REG_DISPSTAT = 0x004
REG_VCOUNT = 0x006
REG_BG0CNT = 0x008
REG_BG0HOFS = 0x010
REG_KEYINPUT = 0x130
REG_IE = 0x200
REG_IF = 0x202
REG_IME = 0x208
REG_DMA0 = 0x0B0

GBA_KEY_MASK = 0x03FF

# GBA keypad (active low in KEYINPUT)
KEY_A, KEY_B, KEY_SELECT, KEY_START = 0, 1, 2, 3
KEY_RIGHT, KEY_LEFT, KEY_UP, KEY_DOWN = 4, 5, 6, 7
KEY_R, KEY_L = 8, 9

KEY_MAP = {
    "z": KEY_A,
    "x": KEY_B,
    "BackSpace": KEY_SELECT,
    "Return": KEY_START,
    "Right": KEY_RIGHT,
    "Left": KEY_LEFT,
    "Up": KEY_UP,
    "Down": KEY_DOWN,
    "e": KEY_R,
    "q": KEY_L,
}

def _build_demo_rom() -> bytes:
    """ARM bx stub + Thumb: mode 3 gradient demo."""
    rom = bytearray(0x200)
    struct.pack_into("<I", rom, 0x00, 0xEA00002E)  # b 0x080000C0
    rom[0xA0:0xAC] = b"MEWGBA      "
    struct.pack_into("<I", rom, 0xC0, 0xE59F0000)  # ldr r0, [pc, #0]
    struct.pack_into("<I", rom, 0xC4, 0xE12FFF10)  # bx r0
    thumb_entry = 0xCC
    struct.pack_into("<I", rom, 0xC8, 0x08000000 | thumb_entry | 1)

    demo_thumb = bytes.fromhex(
        "0648"
        "0749"
        "0880"
        "074a"
        "2300"
        "2000"
        "1846"
        "4010"
        "1080"
        "921d"
        "cb1d"
        "ff2b"
        "f8d1"
        "f8e7"
    )
    rom[thumb_entry : thumb_entry + len(demo_thumb)] = demo_thumb
    pool_off = (thumb_entry + len(demo_thumb) + 3) & ~3
    struct.pack_into("<III", rom, pool_off, 0x0403, 0x04000000, 0x06000000)
    return bytes(rom)


DEFAULT_ROM = _build_demo_rom()


def rgb565_to_rgb(color: int) -> tuple[int, int, int]:
    r = (color & 0x1F) << 3
    g = ((color >> 5) & 0x1F) << 3
    b = ((color >> 10) & 0x1F) << 3
    return r, g, b


class MewGBACore:
    """mGBA-class GBA core (single-file, BIOS HLE, no external files)."""

    def __init__(self) -> None:
        self.rom = bytearray()
        self.ewram = bytearray(256 * 1024)
        self.iwram = bytearray(32 * 1024)
        self.io = bytearray(1024)
        self.palette = bytearray(1024)
        self.vram = bytearray(96 * 1024)
        self.oam = bytearray(1024)
        self.r = [0] * 16
        self.cpsr = 0x0000001F
        self.spsr = 0
        self.halted = False
        self.framebuffer = bytearray(SCREEN_W * SCREEN_H * 3)
        self._prio = [[3] * SCREEN_W for _ in range(SCREEN_H)]
        self._pxbuf = [[(8, 12, 27)] * SCREEN_W for _ in range(SCREEN_H)]
        self.keys_down = 0
        self.rom_label: str | None = None
        self.is_loaded = False
        self.cycles = 0
        self.line_cycles = 0
        self.current_line = 0
        self.timers = [{"reload": 0, "count": 0, "ctrl": 0, "frac": 0} for _ in range(4)]
        self.dma = [{"src": 0, "dst": 0, "count": 0, "ctrl": 0} for _ in range(4)]
        self._init_io_defaults()

    def _init_io_defaults(self) -> None:
        self.io[REG_KEYINPUT : REG_KEYINPUT + 2] = struct.pack("<H", GBA_KEY_MASK)
        self.io[REG_DISPSTAT : REG_DISPSTAT + 2] = struct.pack("<H", 0x0000)
        self.io[REG_VCOUNT : REG_VCOUNT + 2] = struct.pack("<H", 0x0000)
        self.io[REG_IE : REG_IE + 2] = struct.pack("<H", 0x0000)
        self.io[REG_IF : REG_IF + 2] = struct.pack("<H", 0x0000)
        self.io[REG_IME : REG_IME + 2] = struct.pack("<H", 0x0000)
        self.io[REG_DISPCNT : REG_DISPCNT + 2] = struct.pack("<H", 0x0080)

    def reset_cpu(self) -> None:
        self.r = [0] * 16
        self.r[15] = 0x08000000
        self.cpsr = 0x0000001F
        self.spsr = 0
        self.halted = False
        self.cycles = 0
        self.line_cycles = 0
        self.current_line = 0
        self.ewram[:] = b"\x00" * len(self.ewram)
        self.iwram[:] = b"\x00" * len(self.iwram)
        self.io[:] = b"\x00" * len(self.io)
        self.palette[:] = b"\x00" * len(self.palette)
        self.vram[:] = b"\x00" * len(self.vram)
        self.oam[:] = b"\x00" * len(self.oam)
        self.timers = [{"reload": 0, "count": 0, "ctrl": 0, "frac": 0} for _ in range(4)]
        self.dma = [{"src": 0, "dst": 0, "count": 0, "ctrl": 0} for _ in range(4)]
        self._init_io_defaults()

    def _io16(self, off: int) -> int:
        return self.io[off] | (self.io[off + 1] << 8)

    def _set_io16(self, off: int, val: int) -> None:
        self.io[off] = val & 0xFF
        self.io[off + 1] = (val >> 8) & 0xFF

    def _irq_raise(self, bit: int) -> None:
        self._set_io16(REG_IF, self._io16(REG_IF) | (1 << bit))
        self._irq_dispatch()

    def _irq_dispatch(self) -> None:
        if not (self._io16(REG_IME) & 1):
            return
        pending = self._io16(REG_IE) & self._io16(REG_IF) & 0x3FFF
        if not pending:
            return
        bit = (pending & -pending).bit_length() - 1
        self.halted = False
        self.spsr = self.cpsr
        self.cpsr = (self.cpsr & ~0xFF) | 0x92
        self.r[14] = (self.r[15] - (2 if self.thumb() else 4)) & 0xFFFFFFFF
        self.set_thumb(True)
        self.r[15] = 0x03000000 + bit * 4
        self._set_io16(REG_IF, self._io16(REG_IF) & ~(1 << bit))

    def _wait_states(self, addr: int, bits: int) -> int:
        region = addr & 0xFF000000
        if region == 0x02000000:
            return 3 if bits == 32 else 2
        if region == 0x03000000:
            return 1
        if region in (0x05000000, 0x06000000, 0x07000000):
            return 1
        if region in (0x08000000, 0x09000000):
            return 5 if bits == 32 else 3
        return 1

    def _swi_hle(self, num: int) -> None:
        if num == 0x00:
            self.reset_cpu()
            self.r[15] = 0x08000000
            self.cpsr = 0x0000001F
            return
        if num == 0x01:
            flags = self.r[0] & 0xFF
            if flags & 0x01:
                self.palette[:] = b"\x00" * len(self.palette)
            if flags & 0x02:
                self.vram[:] = b"\x00" * len(self.vram)
            if flags & 0x04:
                self.oam[:] = b"\x00" * len(self.oam)
            if flags & 0x08:
                self.io[:] = b"\x00" * len(self.io)
                self._init_io_defaults()
            if flags & 0x10:
                self.iwram[:] = b"\x00" * len(self.iwram)
            if flags & 0x20:
                self.palette[512:] = b"\x00" * (len(self.palette) - 512)
            if flags & 0x40:
                self.ewram[:] = b"\x00" * len(self.ewram)
            return
        if num in (0x02, 0x03):
            self.halted = True
            return
        if num in (0x04, 0x05):
            clear = self.r[0] & 0x3FFF
            wait = self.r[1] & 0x3FFF if num == 0x04 else 0x0001
            while not (self._io16(REG_IF) & wait):
                self._run_cycles(4)
            self._set_io16(REG_IF, self._io16(REG_IF) & ~clear)
            return
        if num == 0x08:
            val = self.r[0] & 0xFFFFFFFF
            self.r[0] = 0 if val == 0 else int(val ** 0.5)
            return
        if num in (0x0B, 0x0C):
            src = self.r[0] & 0xFFFFFFFC
            dst = self.r[1] & 0xFFFFFFFC
            ctrl = self.r[2] & 0xFFFFFFFF
            count = ctrl & 0x001FFFFF
            fill = bool(ctrl & 0x01000000)
            word = bool(ctrl & 0x04000000)
            if num == 0x0C:
                count = (count + 7) // 8
            if word:
                if fill:
                    val = self.read32(src)
                    for _ in range(count):
                        self.write32(dst, val)
                        dst = (dst + 4) & 0xFFFFFFFF
                else:
                    for _ in range(count):
                        self.write32(dst, self.read32(src))
                        src = (src + 4) & 0xFFFFFFFF
                        dst = (dst + 4) & 0xFFFFFFFF
            elif fill:
                val = self.read16(src)
                for _ in range(count):
                    self.write16(dst, val)
                    dst = (dst + 2) & 0xFFFFFFFF
            else:
                for _ in range(count):
                    self.write16(dst, self.read16(src))
                    src = (src + 2) & 0xFFFFFFFF
                    dst = (dst + 2) & 0xFFFFFFFF
            return
        if num == 0x0D:
            self.r[0] = 1

    def _timer_tick(self, cyc: int) -> None:
        for i, t in enumerate(self.timers):
            if not (t["ctrl"] & 0x80):
                continue
            if i > 0 and (t["ctrl"] & 0x04):
                continue
            prescale = (0, 6, 8, 10)[(t["ctrl"] >> 0) & 3]
            step = 1 << prescale
            t["frac"] += cyc
            while t["frac"] >= step:
                t["frac"] -= step
                t["count"] = (t["count"] - 1) & 0xFFFF
                if t["count"] == 0xFFFF:
                    t["count"] = t["reload"]
                    if t["ctrl"] & 0x40:
                        self._irq_raise(3 + i)

    def _run_cycles(self, budget: int) -> None:
        used = 0
        while used < budget:
            if self.halted:
                used += 4
                self.cycles += 4
                self._timer_tick(4)
                continue
            c = self.step_cpu()
            used += c
            self.cycles += c
            self._timer_tick(c)

    def _dma_reg(self, off: int) -> tuple[int, int] | None:
        if off < REG_DMA0 or off > REG_DMA0 + 46:
            return None
        rel = off - REG_DMA0
        ch, reg = rel // 12, rel % 12
        return (ch, reg) if ch <= 3 else None

    def _dma_write(self, ch: int, reg: int, val: int) -> None:
        d = self.dma[ch]
        if reg == 0:
            d["src"] = (d["src"] & 0xFFFF0000) | val
        elif reg == 2:
            d["src"] = (d["src"] & 0x0000FFFF) | (val << 16)
        elif reg == 4:
            d["dst"] = (d["dst"] & 0xFFFF0000) | val
        elif reg == 6:
            d["dst"] = (d["dst"] & 0x0000FFFF) | (val << 16)
        elif reg == 8:
            d["count"] = val
        elif reg == 10:
            d["ctrl"] = val
            if val & 0x8000 and ((val >> 12) & 3) == 0:
                self._start_dma(ch)

    def _start_dma(self, ch: int) -> None:
        d = self.dma[ch]
        src = d["src"] & 0x0FFFFFFF
        dst = d["dst"] & 0x0FFFFFFF
        count = d["count"]
        if ch == 3:
            count &= 0xFFFF
            if count == 0:
                count = 0x10000
        elif count == 0:
            count = 0x4000
        ctrl = d["ctrl"]
        src_inc = (0, 2, -2, 0)[(ctrl >> 7) & 3]
        dst_inc = (0, 2, -2, 0)[(ctrl >> 5) & 3]
        width = 4 if ctrl & 0x0400 else 2 if ctrl & 0x0200 else 1
        for _ in range(count):
            if width == 4:
                self.write32(dst, self.read32(src))
                src = (src + src_inc) & 0xFFFFFFFF if src_inc else src
                dst = (dst + dst_inc) & 0xFFFFFFFF if dst_inc else dst
            elif width == 2:
                self.write16(dst, self.read16(src))
                src = (src + src_inc) & 0xFFFFFFFF if src_inc else src
                dst = (dst + dst_inc) & 0xFFFFFFFF if dst_inc else dst
            else:
                self.write8(dst, self.read8(src))
                src = (src + src_inc) & 0xFFFFFFFF if src_inc else src
                dst = (dst + dst_inc) & 0xFFFFFFFF if dst_inc else dst
        d["ctrl"] = ctrl & 0x7FFF
        if ctrl & 0x4000:
            self._irq_raise(8 + ch)

    def _dma_vblank_hblank(self, mode: int) -> None:
        for ch in range(4):
            ctrl = self.dma[ch]["ctrl"]
            if (ctrl & 0x8000) and ((ctrl >> 12) & 3) == mode:
                self._start_dma(ch)

    def _read_io(self, off: int) -> int:
        if off == REG_VCOUNT:
            return self._io16(REG_VCOUNT) & 0xFF
        if off == REG_VCOUNT + 1:
            return (self._io16(REG_VCOUNT) >> 8) & 0xFF
        if off in (REG_KEYINPUT, REG_KEYINPUT + 1):
            return self.io[off]
        if 0x100 <= off < 0x110:
            idx = (off - 0x100) // 4
            rem = (off - 0x100) % 4
            if rem == 0:
                return self.timers[idx]["count"] & 0xFF
            if rem == 1:
                return (self.timers[idx]["count"] >> 8) & 0xFF
        return self.io[off]

    def _write_io(self, off: int, val: int) -> None:
        if off in (REG_KEYINPUT, REG_KEYINPUT + 1):
            return
        if 0x100 <= off < 0x110:
            idx = (off - 0x100) // 4
            rem = (off - 0x100) % 4
            if rem == 0:
                self.timers[idx]["reload"] = (self.timers[idx]["reload"] & 0xFF00) | val
                self.timers[idx]["count"] = (self.timers[idx]["count"] & 0xFF00) | val
            elif rem == 1:
                self.timers[idx]["reload"] = (self.timers[idx]["reload"] & 0x00FF) | (val << 8)
                self.timers[idx]["count"] = (self.timers[idx]["count"] & 0x00FF) | (val << 8)
            elif rem == 2:
                self.timers[idx]["ctrl"] = (self.timers[idx]["ctrl"] & 0xFF00) | val
            elif rem == 3:
                self.timers[idx]["ctrl"] = (self.timers[idx]["ctrl"] & 0x00FF) | (val << 8)
                if val & 0x80:
                    self.timers[idx]["count"] = self.timers[idx]["reload"]
                    self.timers[idx]["frac"] = 0
            return
        dma = self._dma_reg(off)
        if dma is not None:
            ch, reg = dma
            self.io[off] = val
            self._dma_write(ch, reg, val)
            return
        self.io[off] = val

    def load_rom_bytes(self, rom: bytes, label: str = "Demo (built-in)") -> bool:
        if not rom:
            return False
        self.rom = bytearray(rom)
        self.reset_cpu()
        self.rom_label = label
        self.is_loaded = True
        return True

    def set_keys(self, mask: int) -> None:
        self.keys_down = mask & GBA_KEY_MASK
        self._set_io16(REG_KEYINPUT, GBA_KEY_MASK & ~self.keys_down)

    # --- Memory bus ---

    def _rom_addr(self, addr: int) -> int | None:
        if 0x08000000 <= addr < 0x0A000000:
            off = addr - 0x08000000
            if off < len(self.rom):
                return off
        elif 0x0E000000 <= addr < 0x0E010000:
            off = addr - 0x0E000000
            if off < len(self.rom):
                return off
        return None

    def read8(self, addr: int) -> int:
        addr &= 0xFFFFFFFF
        if 0x02000000 <= addr < 0x02040000:
            return self.ewram[addr - 0x02000000]
        if 0x03000000 <= addr < 0x03008000:
            return self.iwram[addr - 0x03000000]
        if 0x04000000 <= addr < 0x04000400:
            return self._read_io(addr - 0x04000000)
        if 0x05000000 <= addr < 0x05000400:
            return self.palette[addr - 0x05000000]
        if 0x06000000 <= addr < 0x06018000:
            return self.vram[addr - 0x06000000]
        if 0x07000000 <= addr < 0x07000400:
            return self.oam[addr - 0x07000000]
        off = self._rom_addr(addr)
        if off is not None:
            return self.rom[off]
        return 0

    def read16(self, addr: int) -> int:
        addr &= 0xFFFFFFFE
        lo = self.read8(addr)
        hi = self.read8(addr + 1)
        return lo | (hi << 8)

    def read32(self, addr: int) -> int:
        addr &= 0xFFFFFFFC
        return (
            self.read8(addr)
            | (self.read8(addr + 1) << 8)
            | (self.read8(addr + 2) << 16)
            | (self.read8(addr + 3) << 24)
        )

    def write8(self, addr: int, val: int) -> None:
        addr &= 0xFFFFFFFF
        val &= 0xFF
        if 0x02000000 <= addr < 0x02040000:
            self.ewram[addr - 0x02000000] = val
        elif 0x03000000 <= addr < 0x03008000:
            self.iwram[addr - 0x03000000] = val
        elif 0x04000000 <= addr < 0x04000400:
            self._write_io(addr - 0x04000000, val)
        elif 0x05000000 <= addr < 0x05000400:
            self.palette[addr - 0x05000000] = val
        elif 0x06000000 <= addr < 0x06018000:
            self.vram[addr - 0x06000000] = val
        elif 0x07000000 <= addr < 0x07000400:
            self.oam[addr - 0x07000000] = val
        elif 0x08000000 <= addr < 0x0E000000:
            off = self._rom_addr(addr)
            if off is not None and off < len(self.rom):
                self.rom[off] = val

    def write16(self, addr: int, val: int) -> None:
        addr &= 0xFFFFFFFE
        val &= 0xFFFF
        self.write8(addr, val & 0xFF)
        self.write8(addr + 1, (val >> 8) & 0xFF)

    def write32(self, addr: int, val: int) -> None:
        addr &= 0xFFFFFFFC
        val &= 0xFFFFFFFF
        self.write8(addr, val & 0xFF)
        self.write8(addr + 1, (val >> 8) & 0xFF)
        self.write8(addr + 2, (val >> 16) & 0xFF)
        self.write8(addr + 3, (val >> 24) & 0xFF)

    # --- CPU flags ---

    def thumb(self) -> bool:
        return bool(self.cpsr & 0x20)

    def set_thumb(self, on: bool) -> None:
        if on:
            self.cpsr |= 0x20
        else:
            self.cpsr &= ~0x20

    def flag_n(self) -> bool:
        return bool(self.cpsr & 0x80000000)

    def flag_z(self) -> bool:
        return bool(self.cpsr & 0x40000000)

    def flag_c(self) -> bool:
        return bool(self.cpsr & 0x20000000)

    def flag_v(self) -> bool:
        return bool(self.cpsr & 0x10000000)

    def set_nz(self, val: int, bits: int = 32) -> None:
        val &= (1 << bits) - 1
        self.cpsr &= ~0xC0000000
        if val & (1 << (bits - 1)):
            self.cpsr |= 0x80000000
        if val == 0:
            self.cpsr |= 0x40000000

    def set_nz_sub(self, res: int, op1: int, op2: int, bits: int = 32) -> None:
        self.set_nz(res, bits)
        mask = (1 << bits) - 1
        op1 &= mask
        op2 &= mask
        res &= mask
        self.cpsr &= ~0x30000000
        if op1 >= op2:
            self.cpsr |= 0x20000000
        if ((op1 ^ op2) & (op1 ^ res)) & (1 << (bits - 1)):
            self.cpsr |= 0x10000000

    def set_nz_add(self, res: int, op1: int, op2: int, bits: int = 32) -> None:
        self.set_nz(res, bits)
        mask = (1 << bits) - 1
        op1 &= mask
        op2 &= mask
        res &= mask
        self.cpsr &= ~0x30000000
        if res < op1:
            self.cpsr |= 0x20000000
        if (~(op1 ^ op2) & (op1 ^ res)) & (1 << (bits - 1)):
            self.cpsr |= 0x10000000

    def check_cond(self, cond: int) -> bool:
        n, z, c, v = self.flag_n(), self.flag_z(), self.flag_c(), self.flag_v()
        return {
            0x0: z,
            0x1: not z,
            0x2: c,
            0x3: not c,
            0x4: n,
            0x5: not n,
            0x6: v,
            0x7: not v,
            0x8: c and not z,
            0x9: not c or z,
            0xA: n == v,
            0xB: n != v,
            0xC: not z and (n == v),
            0xD: z or (n != v),
            0xE: True,
            0xF: False,
        }.get(cond, False)

    def reg_get(self, i: int) -> int:
        i &= 15
        if i == 15:
            return (self.r[15] + (2 if self.thumb() else 4)) & 0xFFFFFFFF
        return self.r[i] & 0xFFFFFFFF

    def reg_set(self, i: int, val: int) -> None:
        i &= 15
        val &= 0xFFFFFFFF
        if i == 15:
            thumb_bit = bool(val & 1)
            if self.thumb() or thumb_bit:
                val &= ~1
                self.set_thumb(thumb_bit)
            else:
                val &= ~3
            self.r[15] = val
        else:
            self.r[i] = val

    # --- CPU execution ---

    def step_cpu(self) -> int:
        if self.halted:
            return 4
        if self.thumb():
            return self._exec_thumb(self.read16(self.r[15]))
        return self._exec_arm(self.read32(self.r[15]))

    def _exec_thumb(self, op: int) -> int:
        pc = self.r[15]
        self.r[15] = (pc + 2) & 0xFFFFFFFF
        hi = (op >> 12) & 0xF

        if (op >> 13) == 0:
            if ((op >> 11) & 3) == 3:
                imm3 = (op >> 6) & 7
                rn = (op >> 3) & 7
                rd = op & 7
                res = (self.reg_get(rn) + imm3) & 0xFFFFFFFF
                self.set_nz_add(res, self.reg_get(rn), imm3)
                self.reg_set(rd, res)
                return 1

            rd, imm = op & 7, (op >> 3) & 0x1F
            if op & 0x0800:
                if op & 0x0400:
                    val = self.reg_get(rd)
                    self.set_nz(val - imm, 8)
                else:
                    val = (self.reg_get(rd) + imm) & 0xFF
                    self.set_nz(val, 8)
                    self.reg_set(rd, val)
            else:
                shift = (op >> 6) & 3
                if shift == 0:
                    old = self.reg_get(rd)
                    val = (old << imm) & 0xFFFFFFFF
                    if imm:
                        carry = ((old << (imm - 1)) & 0x80000000) != 0
                        self.cpsr = (self.cpsr & ~0x20000000) | (0x20000000 if carry else 0)
                elif shift == 1:
                    old = self.reg_get(rd)
                    val = (old >> imm) & 0xFFFFFFFF
                    if imm:
                        self.cpsr = (self.cpsr & ~0x20000000) | (((old >> (imm - 1)) & 1) << 29)
                elif shift == 2:
                    c = self.flag_c()
                    old = self.reg_get(rd)
                    if imm:
                        val = ((old >> (imm - 1)) | (int(c) << 31)) >> 1 if imm < 32 else 0
                        self.cpsr = (self.cpsr & ~0x20000000) | (((old >> (imm - 1)) & 1) << 29)
                    else:
                        val = old
                else:
                    c = self.flag_c()
                    old = self.reg_get(rd)
                    if imm:
                        val = (((old << (32 - imm)) | (old >> imm)) & 0xFFFFFFFF) if imm < 32 else 0
                        self.cpsr = (self.cpsr & ~0x20000000) | ((old >> (imm - 1)) & 1) << 29
                    else:
                        val = old
                self.set_nz(val)
                self.reg_set(rd, val)
            return 1

        if (op & 0xF800) == 0x1800:
            rs, rd = (op >> 3) & 7, op & 7
            if op & 0x0400:
                res = (self.reg_get(rd) - self.reg_get(rs)) & 0xFFFFFFFF
                self.set_nz_sub(res, self.reg_get(rd), self.reg_get(rs))
            else:
                res = (self.reg_get(rd) + self.reg_get(rs)) & 0xFFFFFFFF
                self.set_nz_add(res, self.reg_get(rd), self.reg_get(rs))
            self.reg_set(rd, res)
            return 1

        if (op & 0xE000) == 0x2000:
            rd, imm = (op >> 8) & 7, op & 0xFF
            fn = (op >> 11) & 3
            if fn == 0:
                self.set_nz(imm, 8)
                self.reg_set(rd, imm)
            elif fn == 1:
                self.set_nz(self.reg_get(rd) | imm, 8)
                self.reg_set(rd, self.reg_get(rd) | imm)
            elif fn == 2:
                res = (self.reg_get(rd) + imm) & 0xFFFFFFFF
                self.set_nz_add(res, self.reg_get(rd), imm)
                self.reg_set(rd, res)
            else:
                res = (self.reg_get(rd) - imm) & 0xFFFFFFFF
                self.set_nz_sub(res, self.reg_get(rd), imm)
                self.reg_set(rd, res)
            return 1

        if (op & 0xFC00) == 0x4000:
            rs, rd = (op >> 3) & 7, op & 7
            val = self.reg_get(rs)
            if (op >> 6) & 3 == 0:
                res = (self.reg_get(rd) + val) & 0xFFFFFFFF
                self.set_nz_add(res, self.reg_get(rd), val)
                self.reg_set(rd, res)
            elif (op >> 6) & 3 == 1:
                res = (self.reg_get(rd) - val) & 0xFFFFFFFF
                self.set_nz_sub(res, self.reg_get(rd), val)
                self.reg_set(rd, res)
            elif (op >> 6) & 3 == 2:
                res = self.reg_get(rd) & val
                self.set_nz(res)
                self.reg_set(rd, res)
            else:
                res = self.reg_get(rd) ^ val
                self.set_nz(res)
                self.reg_set(rd, res)
            return 1

        if (op & 0xFC00) == 0x4400:
            if (op >> 6) & 0xF == 11:
                rs, rd = ((op >> 3) & 7) | 8, (op & 7) | 8
                addr = self.reg_get(rs)
                self.set_thumb(bool(addr & 1))
                self.r[15] = (addr & ~1) & 0xFFFFFFFF
                return 3
            rs, rd = ((op >> 3) & 7) | 8, (op & 7) | 8
            if (op >> 6) & 0xF in (1, 2, 4, 8):
                ops = {1: lambda a, b: a + b, 2: lambda a, b: a - b, 4: lambda a, b: a & b, 8: lambda a, b: a ^ b}
                fn = ops[(op >> 6) & 0xF]
                a, b = self.reg_get(rd), self.reg_get(rs)
                res = fn(a, b) & 0xFFFFFFFF
                if (op >> 6) & 0xF == 1:
                    self.set_nz_add(res, a, b)
                elif (op >> 6) & 0xF == 2:
                    self.set_nz_sub(res, a, b)
                else:
                    self.set_nz(res)
                self.reg_set(rd, res)
            elif (op >> 6) & 0xF == 9:
                res = self.reg_get(rd) * self.reg_get(rs)
                self.set_nz(res)
                self.reg_set(rd, res)
            return 1

        if (op & 0xF800) == 0x4800:
            rd = (op >> 8) & 7
            off = (op & 0xFF) << 2
            base = ((pc & 0xFFFFFFFC) + 4) & 0xFFFFFFFF
            self.reg_set(rd, self.read32((base + off) & 0xFFFFFFFC))
            return 2

        if (op & 0xF800) == 0x5000:
            rb, ro, rd = (op >> 3) & 7, (op >> 6) & 7, op & 7
            addr = (self.reg_get(rb) + self.reg_get(ro)) & 0xFFFFFFFF
            if op & 0x0800:
                if op & 0x0400:
                    val = self.read8(addr)
                    if val & 0x80:
                        val |= 0xFFFFFF00
                    self.reg_set(rd, val)
                elif op & 0x0200:
                    val = self.read16(addr)
                    if val & 0x8000:
                        val |= 0xFFFF0000
                    self.reg_set(rd, val)
                else:
                    self.reg_set(rd, self.read16(addr))
            elif op & 0x0400:
                self.write8(addr, self.reg_get(rd) & 0xFF)
            else:
                self.write16(addr, self.reg_get(rd) & 0xFFFF)
            return 2 + self._wait_states(addr, 16)

        if (op & 0xF800) == 0x5800:
            rb, rd = (op >> 3) & 7, op & 7
            off = (op >> 6) & 0x1F
            addr = (self.reg_get(rb) + off) & 0xFFFFFFFF
            if op & 0x0800:
                val = self.read8(addr)
                if val & 0x80:
                    val |= 0xFFFFFF00
                self.reg_set(rd, val)
            else:
                self.write8(addr, self.reg_get(rd) & 0xFF)
            return 2

        if (op & 0xF800) == 0x6000:
            rb, rd = (op >> 3) & 7, op & 7
            off = ((op >> 6) & 0x1F) << 2
            addr = (self.reg_get(rb) + off) & 0xFFFFFFFF
            if op & 0x0800:
                self.reg_set(rd, self.read32(addr))
            else:
                self.write32(addr, self.reg_get(rd))
            return 2

        if (op & 0xF800) == 0x8000:
            rb, rd = (op >> 3) & 7, op & 7
            off = ((op >> 6) & 0x1F) << 1
            addr = (self.reg_get(rb) + off) & 0xFFFFFFFF
            if op & 0x0800:
                val = self.read16(addr)
                self.reg_set(rd, val)
            else:
                self.write16(addr, self.reg_get(rd) & 0xFFFF)
            return 2 + self._wait_states(addr, 16)

        if (op & 0xF800) == 0x9000:
            rd = (op >> 8) & 7
            off = (op & 0xFF) << 2
            addr = (self.r[13] + off) & 0xFFFFFFFF
            if op & 0x0800:
                self.reg_set(rd, self.read32(addr))
            else:
                self.write32(addr, self.reg_get(rd))
            return 2

        if (op & 0xFF00) == 0xA000:
            rd = (op >> 8) & 7
            off = (op & 0xFF) << 2
            base = ((pc & 0xFFFFFFFC) + 4) & 0xFFFFFFFF
            self.reg_set(rd, (self.reg_get(rd) + base + off) & 0xFFFFFFFF)
            return 1

        if (op & 0xF800) == 0xB000:
            regs = op & 0xFF
            lr = 1 if op & 0x100 else 0
            sp = self.r[13]
            if op & 0x0800:
                if lr:
                    self.write32(sp, self.r[14])
                    sp += 4
                for i in range(8):
                    if regs & (1 << i):
                        self.write32(sp, self.r[i])
                        sp += 4
                self.r[13] = sp
            else:
                for i in range(7, -1, -1):
                    if regs & (1 << i):
                        sp -= 4
                        self.r[i] = self.read32(sp)
                if lr:
                    sp -= 4
                    self.r[15] = self.read32(sp)
                self.r[13] = sp
            return 2

        if (op & 0xF000) == 0xC000:
            off = op & 0xFF
            if off & 0x80:
                off = -((~off + 1) & 0xFF)
            self.r[15] = (self.r[15] + (off << 1)) & 0xFFFFFFFF
            return 3

        if (op & 0xFF00) == 0xDF00:
            self._swi_hle(op & 0xFF)
            return 3

        if (op & 0xF800) == 0x7000:
            off = op & 0x7FF
            if off & 0x400:
                off = -((~off + 1) & 0x7FF)
            self.r[15] = (self.r[15] + (off << 1)) & 0xFFFFFFFF
            return 3

        if (op & 0xF800) == 0xE000:
            self.r[15] = (self.r[15] + struct.unpack("<h", struct.pack("<H", op & 0x7FF))[0] * 2) & 0xFFFFFFFF
            return 3

        if (op & 0xF000) == 0xD000:
            cond = hi
            if cond == 0xE:
                return 1
            if self.check_cond(cond):
                off = op & 0xFF
                if off & 0x80:
                    off = -((~off + 1) & 0xFF)
                self.r[15] = (self.r[15] + (off << 1)) & 0xFFFFFFFF
            return 3

        return 1

    def _exec_arm(self, op: int) -> int:
        cond = (op >> 28) & 0xF
        if cond != 0xE and not self.check_cond(cond):
            self.r[15] = (self.r[15] + 4) & 0xFFFFFFFF
            return 1

        if (op & 0x0FFFFFF0) == 0x012FFF10:
            rm = op & 0xF
            addr = self.reg_get(rm)
            self.set_thumb(bool(addr & 1))
            self.r[15] = (addr & ~1) & 0xFFFFFFFF
            return 3

        if (op & 0x0E000000) == 0x00000000 and (op & 0xFC000000) != 0x04000000:
            return self._arm_data_proc(op)
        if (op & 0x0C000000) == 0x04000000:
            return self._arm_single_trans(op)
        if (op & 0x0F000000) == 0x02000000:
            return self._arm_multiply(op)
        if (op & 0x0F000000) == 0x0F000000:
            self._swi_hle(op & 0xFFFFFF)
            self.r[15] = (self.r[15] + 4) & 0xFFFFFFFF
            return 3
        if (op & 0x0E000000) == 0x0A000000:
            return self._arm_branch(op)
        self.r[15] = (self.r[15] + 4) & 0xFFFFFFFF
        return 1

    def _arm_shifter(self, op: int, c_in: bool) -> tuple[int, bool]:
        rm = op & 0xF
        val = self.reg_get(rm)
        if op & 0x02000000:
            imm = op & 0xFF
            rot = ((op >> 8) & 0xF) * 2
            if rot:
                c_out = bool((imm >> (rot - 1)) & 1)
                val = ((imm >> rot) | (imm << (32 - rot))) & 0xFFFFFFFF
            else:
                c_out = c_in
            return val, c_out
        shift = (op >> 5) & 3
        amount = (op >> 7) & 0x1F
        rs = (op >> 8) & 0xF
        if rs == 15:
            amount = (self.reg_get(15) + 4) & 0xFF if not self.thumb() else (self.reg_get(15) + 2) & 0xFF
        if shift == 0:
            if amount == 0:
                return val, c_in
            c_out = bool((val >> (amount - 1)) & 1)
            val = (val << amount) & 0xFFFFFFFF
        elif shift == 1:
            if amount == 0:
                amount = 32
            c_out = bool((val >> (amount - 1)) & 1)
            val = (val >> amount) & 0xFFFFFFFF
        elif shift == 2:
            if amount == 0:
                amount = 32
            c_out = bool((val >> (amount - 1)) & 1)
            val = (val >> amount) | (int(c_in) << (31 - amount + 1)) if amount <= 32 else 0
            val &= 0xFFFFFFFF
        else:
            if amount == 0:
                amount = 32
            c_out = bool(val & 1)
            val = ((val >> 1) | (int(c_in) << 31)) & 0xFFFFFFFF if amount == 1 else (
                ((val << (32 - amount)) | (val >> amount)) & 0xFFFFFFFF
            )
        return val, c_out

    def _arm_data_proc(self, op: int) -> int:
        rd = (op >> 12) & 0xF
        rn = (op >> 16) & 0xF
        opcode = (op >> 21) & 0xF
        s = bool(op & 0x00100000)
        op2, c_out = self._arm_shifter(op, self.flag_c())
        op1 = self.reg_get(rn)
        res = 0
        if opcode == 0x0:
            res = op1 & op2
            if s:
                self.set_nz(res)
                self.cpsr = (self.cpsr & ~0x20000000) | (int(c_out) << 29)
        elif opcode == 0x1:
            res = op1 ^ op2
            if s:
                self.set_nz(res)
                self.cpsr = (self.cpsr & ~0x20000000) | (int(c_out) << 29)
        elif opcode == 0x2:
            res = (op1 - op2) & 0xFFFFFFFF
            if s:
                self.set_nz_sub(res, op1, op2)
                self.cpsr = (self.cpsr & ~0x20000000) | (int(c_out) << 29)
        elif opcode == 0x4:
            res = (op1 + op2) & 0xFFFFFFFF
            if s:
                self.set_nz_add(res, op1, op2)
                self.cpsr = (self.cpsr & ~0x20000000) | (int(c_out) << 29)
        elif opcode == 0xC:
            res = (op1 | op2) & 0xFFFFFFFF
            if s:
                self.set_nz(res)
                self.cpsr = (self.cpsr & ~0x20000000) | (int(c_out) << 29)
        elif opcode == 0xD:
            res = op2
            if s:
                self.set_nz(res)
                self.cpsr = (self.cpsr & ~0x20000000) | (int(c_out) << 29)
        else:
            res = op1
        if rd == 15:
            self.r[15] = (res - 4) & 0xFFFFFFFF
        else:
            self.reg_set(rd, res)
        self.r[15] = (self.r[15] + 4) & 0xFFFFFFFF
        return 1

    def _arm_multiply(self, op: int) -> int:
        rd = (op >> 16) & 0xF
        rs = op & 0xF
        rm = (op >> 8) & 0xF
        res = (self.reg_get(rm) * self.reg_get(rs)) & 0xFFFFFFFF
        if op & 0x00200000:
            res = (res + self.reg_get(rd)) & 0xFFFFFFFF
        self.reg_set(rd, res)
        if op & 0x00100000:
            self.set_nz(res)
        self.r[15] = (self.r[15] + 4) & 0xFFFFFFFF
        return 1

    def _arm_single_trans(self, op: int) -> int:
        rd = (op >> 12) & 0xF
        rn = (op >> 16) & 0xF
        load = bool(op & 0x00100000)
        byte = bool(op & 0x00400000)
        half = bool(op & 0x00000040)
        signed = bool(op & 0x00000040)
        up = bool(op & 0x00800000)
        imm = op & 0xFFF
        if not (op & 0x02000000):
            imm = self.reg_get(op & 0xF)
        if rn == 15:
            addr = (self.r[15] + 8) & 0xFFFFFFFF
        else:
            addr = self.reg_get(rn)
        if up:
            addr = (addr + imm) & 0xFFFFFFFF
        else:
            addr = (addr - imm) & 0xFFFFFFFF
        if load:
            if byte:
                val = self.read8(addr)
            elif half:
                val = self.read16(addr)
                if signed and val & 0x8000:
                    val |= 0xFFFF0000
            else:
                val = self.read32(addr)
            if rd == 15:
                self.r[15] = val
            else:
                self.reg_set(rd, val)
        else:
            if byte:
                self.write8(addr, self.reg_get(rd) & 0xFF)
            elif half:
                self.write16(addr, self.reg_get(rd) & 0xFFFF)
            else:
                self.write32(addr, self.reg_get(rd))
        self.r[15] = (self.r[15] + 4) & 0xFFFFFFFF
        return 1

    def _arm_branch(self, op: int) -> int:
        link = bool(op & 0x01000000)
        off = op & 0x00FFFFFF
        if off & 0x00800000:
            off |= ~0xFFFFFF
        target = (self.r[15] + 8 + (off << 2)) & 0xFFFFFFFF
        if link:
            self.r[14] = (self.r[15] + 4) & 0xFFFFFFFF
        self.r[15] = target
        return 3

    def _run_scanline(self, line: int) -> None:
        self._set_io16(REG_VCOUNT, line)
        stat = self._io16(REG_DISPSTAT)
        if line == VDRAW_LINES:
            self._set_io16(REG_DISPSTAT, stat | 0x0001)
            self._irq_raise(0)
            self._dma_vblank_hblank(1)
        if line < VDRAW_LINES:
            self._run_cycles(CYCLES_PER_SCANLINE)
            self._dma_vblank_hblank(2)
        else:
            self._run_cycles(CYCLES_PER_SCANLINE)

    # --- PPU ---

    def _pix(self, x: int, y: int, rgb: tuple[int, int, int], prio: int = 3) -> None:
        if 0 <= x < SCREEN_W and 0 <= y < SCREEN_H and prio <= self._prio[y][x]:
            self._prio[y][x] = prio
            self._pxbuf[y][x] = rgb

    def render_frame(self) -> None:
        self._prio = [[3] * SCREEN_W for _ in range(SCREEN_H)]
        self._pxbuf = [[(8, 12, 27)] * SCREEN_W for _ in range(SCREEN_H)]
        disp = self._io16(REG_DISPCNT)
        mode = disp & 7
        if mode == 3:
            self._render_mode3()
        elif mode == 4:
            self._render_mode4()
        elif mode in (0, 1, 2):
            self._render_mode012(mode)
        elif mode == 5:
            self._render_mode5()
        self._render_sprites()
        for y in range(SCREEN_H):
            for x in range(SCREEN_W):
                r, g, b = self._pxbuf[y][x]
                i = (y * SCREEN_W + x) * 3
                self.framebuffer[i], self.framebuffer[i + 1], self.framebuffer[i + 2] = r, g, b

    def _render_mode3(self) -> None:
        for y in range(SCREEN_H):
            for x in range(SCREEN_W):
                off = (y * SCREEN_W + x) * 2
                color = self.vram[off] | (self.vram[off + 1] << 8)
                self._pix(x, y, rgb565_to_rgb(color), 0)

    def _render_mode4(self) -> None:
        frame = (self._io16(REG_DISPCNT) >> 4) & 1
        base = frame * 0xA000
        for y in range(SCREEN_H):
            for x in range(SCREEN_W):
                idx = self.vram[base + y * SCREEN_W + x]
                color = self.palette[idx * 2] | (self.palette[idx * 2 + 1] << 8)
                self._pix(x, y, rgb565_to_rgb(color), 0)

    def _render_mode5(self) -> None:
        frame = (self._io16(REG_DISPCNT) >> 4) & 1
        base = frame * 0xA000
        for y in range(SCREEN_H):
            for x in range(SCREEN_W):
                off = base + (y * SCREEN_W + x) * 2
                color = self.vram[off] | (self.vram[off + 1] << 8)
                self._pix(x, y, rgb565_to_rgb(color), 0)

    def _render_mode012(self, mode: int) -> None:
        layers = []
        disp = self._io16(REG_DISPCNT)
        for bg in range(4 if mode < 2 else 2):
            if not (disp & (0x0400 << bg)):
                continue
            ctrl = self._io16(REG_BG0CNT + bg * 2)
            layers.append((ctrl & 3, bg, ctrl))
        layers.sort()
        for _, bg, ctrl in layers:
            self._render_text_bg(bg, ctrl, (ctrl & 3))

    def _render_text_bg(self, bg: int, ctrl: int, prio: int) -> None:
        char_base = ((ctrl >> 2) & 3) * 0x4000
        map_base = ((ctrl >> 8) & 0x1F) * 0x800
        bpp8 = bool(ctrl & 0x80)
        mx = 512 if (ctrl & 0x400) else 256
        hofs = self._io16(REG_BG0HOFS + bg * 4) & 0x1FF
        vofs = self._io16(REG_BG0HOFS + bg * 4 + 2) & 0x1FF
        for y in range(SCREEN_H):
            for x in range(SCREEN_W):
                wx = (x + hofs) % mx
                wy = (y + vofs) % 256
                tx, ty = wx // 8, wy // 8
                map_off = map_base + (ty * (mx // 8) + tx) * 2
                if map_off + 1 >= len(self.vram):
                    continue
                entry = self.vram[map_off] | (self.vram[map_off + 1] << 8)
                tile_id = entry & 0x3FF
                hflip = entry & 0x0400
                vflip = entry & 0x0800
                pal_bank = (entry >> 12) & 0xF
                px, py = wx % 8, wy % 8
                if hflip:
                    px = 7 - px
                if vflip:
                    py = 7 - py
                if bpp8:
                    tile_off = char_base + tile_id * 64 + py * 8 + px
                    if tile_off >= len(self.vram):
                        continue
                    idx = self.vram[tile_off]
                    color = self.palette[idx * 2] | (self.palette[idx * 2 + 1] << 8)
                else:
                    tile_off = char_base + tile_id * 32 + py * 4 + (px // 2)
                    if tile_off >= len(self.vram):
                        continue
                    byte = self.vram[tile_off]
                    idx = (byte >> 4) if px & 1 else (byte & 0xF)
                    if idx == 0:
                        continue
                    pal_off = (pal_bank * 16 + idx) * 2
                    color = self.palette[pal_off] | (self.palette[pal_off + 1] << 8)
                if bpp8 or idx != 0:
                    self._pix(x, y, rgb565_to_rgb(color), prio)

    def _render_sprites(self) -> None:
        disp = self.read16(0x4000000)
        if not (disp & 0x1000):
            return
        obj1d = bool(disp & 0x0040)
        for i in range(128):
            off = i * 8
            attr0 = self.oam[off] | (self.oam[off + 1] << 8)
            attr1 = self.oam[off + 2] | (self.oam[off + 3] << 8)
            attr2 = self.oam[off + 4] | (self.oam[off + 5] << 8)
            if (attr0 & 0x0300) == 0x0200:
                continue
            y = attr0 & 0xFF
            x = attr1 & 0x1FF
            tile = attr2 & 0x3FF
            prio = (attr2 >> 10) & 3
            pal = (attr2 >> 12) & 0xF
            shape = (attr0 >> 14) & 3
            size = (attr1 >> 14) & 3
            dims = [(8, 8), (16, 16), (32, 32), (64, 64)][size] if shape == 0 else [(16, 8), (32, 8), (32, 16), (64, 32)][size] if shape == 1 else [(8, 16), (8, 32), (16, 32), (32, 64)][size]
            w, h = dims
            if y >= 160:
                y -= 256
            for sy in range(h):
                for sx in range(w):
                    px, py = x + sx, y + sy
                    if not (0 <= px < SCREEN_W and 0 <= py < SCREEN_H):
                        continue
                    tnum = tile + (sy // 8) * (32 if obj1d else 16) + (sx // 8)
                    toff = 0x10000 + tnum * 32
                    subx, suby = sx % 8, sy % 8
                    byte = self.vram[toff + suby * 4 + subx // 2]
                    idx = (byte >> 4) if subx & 1 else (byte & 0xF)
                    if idx == 0:
                        continue
                    pal_off = (pal * 16 + idx) * 2
                    color = self.palette[pal_off] | (self.palette[pal_off + 1] << 8)
                    self._pix(px, py, rgb565_to_rgb(color), prio)

    def step_frame(self) -> None:
        if not self.is_loaded:
            return
        for line in range(TOTAL_LINES):
            self._run_scanline(line)
        self.render_frame()


class MewGBAEmulator:
    def __init__(self, root: tk.Tk, rom_bytes: bytes | None = None, rom_label: str = "Demo (built-in)") -> None:
        self.root = root
        self.root.title("mewgba$")
        self.root.geometry("520x420")
        self.root.resizable(False, False)

        self.bg_color = "#0a192f"
        self.text_color = "#00b4d8"
        self.button_bg = "#000000"
        self.button_fg = "#00b4d8"
        self.screen_bg = "#020c1b"

        self.root.configure(bg=self.bg_color)

        self.core = MewGBACore()
        self.rom_bytes = rom_bytes if rom_bytes is not None else DEFAULT_ROM
        self.rom_label = rom_label
        self.core.load_rom_bytes(self.rom_bytes, self.rom_label)
        self.is_running = False
        self._photo: tk.PhotoImage | None = None
        self._scaled: tk.PhotoImage | None = None
        self._keys = 0

        self.setup_ui()
        self._bind_keys()
        self.draw_screen()

    def setup_ui(self) -> None:
        control_frame = tk.Frame(self.root, bg=self.bg_color)
        control_frame.pack(fill=tk.X, padx=10, pady=10)

        btn_style = {
            "bg": self.button_bg,
            "fg": self.button_fg,
            "activebackground": self.text_color,
            "activeforeground": self.button_bg,
            "font": ("Arial", 9, "bold"),
            "bd": 1,
            "relief": "solid",
        }

        self.run_btn = tk.Button(control_frame, text="Play", command=self.toggle_execution, **btn_style)
        self.run_btn.pack(side=tk.LEFT, padx=5)

        reset_btn = tk.Button(control_frame, text="Reset", command=self.reset_emulator, **btn_style)
        reset_btn.pack(side=tk.LEFT, padx=5)

        self.status_label = tk.Label(
            control_frame,
            text=f"ROM: {self.rom_label} (paused)",
            bg=self.bg_color,
            fg=self.text_color,
            font=("Arial", 10),
        )
        self.status_label.pack(side=tk.LEFT, padx=10)

        self.display_canvas = tk.Canvas(
            self.root,
            width=480,
            height=320,
            bg=self.screen_bg,
            highlightthickness=1,
            highlightbackground=self.text_color,
        )
        self.display_canvas.pack(pady=5)

        tk.Label(
            self.root,
            text="Keys: Z=A  X=B  Arrows=D-pad  Q=L  E=R  Enter=Start  Backspace=Select",
            bg=self.bg_color,
            fg=self.text_color,
            font=("Arial", 8),
        ).pack(pady=(0, 6))

    def _bind_keys(self) -> None:
        for key in KEY_MAP:
            self.root.bind(f"<KeyPress-{key}>", self._on_key_down)
            self.root.bind(f"<KeyRelease-{key}>", self._on_key_up)
        self.root.focus_set()

    def _on_key_down(self, event: tk.Event) -> None:
        bit = KEY_MAP.get(event.keysym)
        if bit is not None:
            self._keys |= 1 << bit
            self.core.set_keys(self._keys)

    def _on_key_up(self, event: tk.Event) -> None:
        bit = KEY_MAP.get(event.keysym)
        if bit is not None:
            self._keys &= ~(1 << bit)
            self.core.set_keys(self._keys)

    def draw_screen(self) -> None:
        rows = []
        fb = self.core.framebuffer
        for y in range(SCREEN_H):
            row = []
            for x in range(SCREEN_W):
                i = (y * SCREEN_W + x) * 3
                row.append(f"#{fb[i]:02x}{fb[i + 1]:02x}{fb[i + 2]:02x}")
            rows.append("{" + " ".join(row) + "}")
        if self._photo is None:
            self._photo = tk.PhotoImage(width=SCREEN_W, height=SCREEN_H)
        self._photo.put(" ".join(rows), to=(0, 0))
        self._scaled = self._photo.zoom(2, 2)
        self.display_canvas.delete("all")
        self.display_canvas.create_image(240, 160, image=self._scaled)

    def reset_emulator(self) -> None:
        self.is_running = False
        self.run_btn.config(text="Play")
        self.core.load_rom_bytes(self.rom_bytes, self.rom_label)
        self.status_label.config(text=f"ROM: {self.rom_label} (paused)")
        self.draw_screen()

    def toggle_execution(self) -> None:
        if not self.core.is_loaded:
            messagebox.showwarning("Warning", "No ROM loaded.")
            return
        if not self.is_running:
            self.is_running = True
            self.run_btn.config(text="Pause")
            self.status_label.config(text=f"ROM: {self.rom_label} (running)")
            self.emulator_loop()
        else:
            self.is_running = False
            self.run_btn.config(text="Play")
            self.status_label.config(text=f"ROM: {self.rom_label} (paused)")

    def emulator_loop(self) -> None:
        if not self.is_running:
            return
        self.core.step_frame()
        self.draw_screen()
        self.root.after(16, self.emulator_loop)


def _load_startup_rom() -> tuple[bytes, str]:
    if len(sys.argv) >= 2:
        path = os.path.abspath(sys.argv[1])
        try:
            with open(path, "rb") as f:
                data = f.read()
            if data:
                return data, os.path.basename(path)
        except OSError as exc:
            messagebox.showerror("ROM Error", f"Could not load ROM:\n{exc}\nUsing built-in demo.")
    return DEFAULT_ROM, "Demo (built-in)"


if __name__ == "__main__":
    root = tk.Tk()
    rom, label = _load_startup_rom()
    MewGBAEmulator(root, rom, label)
    root.mainloop()
