#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdint.h>
#include <string.h>
#include <ctype.h>
#include <unistd.h>

#define MEMSIZE (1U<<20)
typedef uint32_t mval;
typedef  int32_t sval;
typedef uint8_t uchar;

#ifdef DEBUG
#define DD(CODE) CODE
#else
#define DD(code) 0
#endif

void die(const char *fmt, ...) {
  va_list ap;
  dprintf(2, "\n");
  va_start(ap, fmt);
  vdprintf(2, fmt, ap);
  va_end(ap);
  dprintf(2, "\n");
  exit(1);
}

/* Intel hex file parser -- more permissive than the spec */

FILE *hex_file;
int hex_sum;

int nextHexFileChar() {
  int ch;
  while (isspace(ch = fgetc(hex_file)));
  return ch;
}

mval readHexInt(int nBytes) {
  mval v = 0;
  for (int i = 1; i <= 2 * nBytes; ++i) {
    int ch = nextHexFileChar();
    if (!isxdigit(ch)) die("Unexpected '%c' in hex file", isprint(ch) ? ch : '?');
    if (!isdigit(ch)) ch += 9; // adjust A-Fa-f
    v = 0x10 * v + (ch & 0xf);
    if (i%2 == 0) hex_sum += v & 0xff;
  }
  return v;
}

mval mem_brk = 0;

mval readHexFile(const char *fname, char *mem, mval msize) {
  hex_file = fopen(fname, "r");
  if (!hex_file) die("Couldn't open hex file \"%s\"", fname);
  mval baseAddr = 0, startPC = 0, eofRecordSeen = 0;
  do {
    if (nextHexFileChar() != ':') die("Expected : in hex file");
    mval hex_sum = 0, sz = readHexInt(1), addr = baseAddr + readHexInt(2), typ = readHexInt(1);
    switch (typ) {
    case 0:
      for (mval i = addr; i < addr + sz; ++i) {
        if (i >= msize) die("'%s' address %08x exceeds memory limit %08x", i, msize);
        mem[i] = readHexInt(1);
        if (mem_brk <= i) mem_brk = i + 1;
      }
      break;
    case 1: eofRecordSeen = 1; break;
    case 2: baseAddr = readHexInt(2) * 0x10; break;
    case 3: startPC = readHexInt(2) * 0x10 + readHexInt(2); break;
    case 4: baseAddr = readHexInt(2) * 0x10000; break;
    case 5: startPC = readHexInt(4); break;
    default: die("Unknown hex record type %02X", typ);
    }
    int checkSum = readHexInt(1);
    if (hex_sum & 0xff) die("Bad checksum %2x in hex file", checkSum);
  } while (!eofRecordSeen);
  return startPC;
}

enum opcode_fmt {B_fmt, I_fmt, J_fmt, L_fmt, R_fmt, S_fmt, U_fmt, X_fmt};
enum regNum {Rzero, Rra, Rsp, Rgp, Rtp, Rt0, Rt1, Rt2, Rs0, Rs1, Ra0, Ra1, Ra2, Ra3, Ra4, Ra5,
             Ra6, Ra7, Rs2, Rs3, Rs4, Rs5, Rs6, Rs7, Rs8, Rs9, Rs10, Rs11, Rt3, Rt4, Rt5, Rt6};

char *regNames[] =
  {"zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
   "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"};

#define INSTRUCTION(MNE, FMT, MATCH, MASK, DO) MNE##_num,
typedef enum {
  #include "instructions.inc"
  NUM_OPCODES
} opcode_num;
#undef INSTRUCTION

#define INSTRUCTION(MNE, FMT, MATCH, MASK, DO) {#MNE, FMT##_fmt},
struct {char *name; enum opcode_fmt fmt;} opcode_info[NUM_OPCODES] = {
  #include "instructions.inc"
};
#undef INSTRUCTION

typedef struct {
  mval reg[32];
  mval pc;
} hart;

#define INSTRUCTION(MNE, FMT, MATCH, MASK, DO) {MATCH, MASK, MNE##_num},
typedef struct {mval match; mval mask; opcode_num opcode;} opcode_match;
opcode_match opcodes[NUM_OPCODES] = {
  #include "instructions.inc"
};
#undef INSTRUCTION

void compare_cpu(hart *cpu, hart *old_cpu) {
  dprintf(2, " pc: %08x", cpu->pc);
  for (int i=0; i<32; ++i) {
    mval v = cpu->reg[i];
    if (v != old_cpu->reg[i])
      dprintf(2, " x%d (%s) <= %x %d", i, regNames[i], v, v);
  }
  dprintf(2, "\n");
}

unsigned char mem[MEMSIZE];

mval setupArgcArgvEnv(mval memsz) {
  mval sp = (memsz - 3*sizeof(mval)) & ~0xf;
  mem[sp] = 0; // argc
  mem[sp + 4] = 0; // argv
  mem[sp + 8] = 0; // envp
  return sp;
}

void CHK(mval base, mval sz) {
  if (base >= MEMSIZE || (base + sz) > MEMSIZE) die("mem addr error %x (size %x)", base, sz);
}

void doECALL(hart *cpu) {
  mval *x = cpu->reg;
  switch (x[Ra7]) {
  case 57: x[Ra0] = x[Ra0] <= 2 ? 0 : close(x[Ra0]); break; // close
  case 64: CHK(x[Ra1], x[Ra2]); x[Ra0] = write(x[Ra0], mem + x[Ra1], x[Ra2]); break; // write
  case 80: x[Ra0] = -1; break; // fstat
  case 93: DD(dprintf(2, "exit(%d) called\n", x[Ra0])); exit(x[Ra0]);
  case 214: if (x[Ra0] == 0) x[Ra0] = mem_brk; else mem_brk = x[Ra0]; break; // brk
  default: dprintf(2, "Unknown ECALL %d\n", x[Ra7]); exit(1);
  }
}

mval load(mval addr, int sz) {
  CHK(addr, sz);
  mval r = 0;
  for (int i=0; i<sz; ++i) r |= mem[addr + i] << (i * 8);
  return (mval)r << ((4-sz)*8) >> ((4-sz)*8);
}

void store(mval addr, int sz, mval v) {
  CHK(addr, sz);
  for (int i=0; i<sz; ++i) mem[addr + i] = (v >> (i * 8)) & 0xff;
}

#define  FLD(H, L) (((mval)insn << (31 - (H))) >> (31 - ((H) - (L))))
#define SFLD(H, L) (((sval)insn << (31 - (H))) >> (31 - ((H) - (L))))

typedef struct {mval insn; char opcode; char rd; char rs1; char rs2; mval imm;} decoded_insn;

void disasm(mval pc, decoded_insn *isn) {
  char **name = regNames;
  mval rd = isn->rd, rs1 = isn->rs1, rs2 = isn->rs2, imm = isn->imm;
  dprintf(2, "%8x: %08x %6s ", pc, isn->insn, opcode_info[isn->opcode].name);
  switch (opcode_info[isn->opcode].fmt) {
  case R_fmt: dprintf(2, "%s, %s, %s\n", name[rd], name[rs1], name[rs2]); break;
  case I_fmt: dprintf(2, "%s, %s, %d # %x\n", name[rd], name[rs1], imm, imm); break;
  case L_fmt: dprintf(2, "%s, %d(%s)\n", name[rd], imm, name[rs1]); break;
  case S_fmt: dprintf(2, "%s, %d(%s)\n", name[rs2], imm, name[rs1]); break;
  case B_fmt: dprintf(2, "%s, %s, .%+d # %x\n", name[rs1], name[rs2], imm, pc + imm); break;
  case U_fmt: dprintf(2, "%s, %d # %x\n", name[rd], imm, imm); break;
  case J_fmt: dprintf(2, "%s, .%+d # %x\n", name[rd], imm, pc + imm); break;
  case X_fmt: dprintf(2, "\n"); break;
  }
}

int decode(decoded_insn *isn, mval insn) {
  mval rd = FLD(11,7), rs1 = FLD(19,15), rs2 = FLD(24,20), imm = 0;
  for (int i = 0; i < NUM_OPCODES; ++i) {
    opcode_match m = opcodes[i];
    if ((insn & m.mask) == m.match) {
      isn->opcode = m.opcode;
      mval imm = 0;
      switch (opcode_info[m.opcode].fmt) {
      case B_fmt:
        imm = SFLD(31,31)<<12 | FLD(30,25)<<5 | FLD(11,8)<<1 | FLD(7,7)<<11; rd = 0; break;
      case I_fmt:
      case L_fmt:
        imm = SFLD(31,20); rs2 = 0; break;
      case J_fmt:
        imm = SFLD(31,31)<<20 | FLD(30,21)<<1 | FLD(20,20)<<11 | FLD(19,12)<<12; rs1 = rs2 = 0; break;
      case R_fmt:
        break;
      case S_fmt:
        imm = SFLD(31,25)<<5 | FLD(11,7); rd = 0; break;
      case U_fmt:
        imm = SFLD(31,12)<<12; rs1 = rs2 = 0; break;
      case X_fmt:
        rd = rs1 = rs2 = 0; break;
      }
      isn->insn = insn; isn->rd = rd; isn->rs1 = rs1; isn->rs2 = rs2; isn->imm = imm;
      return 1;
    }
  }
  return 0;
}

int runCPU(mval pc) {
  hart cpu;
  memset(&cpu, 0, sizeof(cpu));
  cpu.reg[Rsp] = setupArgcArgvEnv(MEMSIZE);
  cpu.pc = pc;
  int exit_program = 0;
  do {
    DD(hart old_cpu = cpu); CHK(pc, 4);
    mval insn = *(mval*)(mem + pc);
    decoded_insn isn;
    if (!decode(&isn, insn)) {
      dprintf(2, "unknown insn %08x at %08x\n", insn, pc); exit_program = 1; break;
    }
    mval rd = cpu.reg[isn.rd], rs1 = cpu.reg[isn.rs1], rs2 = cpu.reg[isn.rs2], imm = isn.imm;
    DD(disasm(pc, &isn));
    switch (isn.opcode) {
      #define INSTRUCTION(MNE, FMT, MATCH, MASK, DO) case MNE##_num: DO; break;
      #include "instructions.inc"
      #undef INSTRUCTION
    };
    if (isn.rd != 0) cpu.reg[isn.rd] = rd;
    if (pc == cpu.pc) pc += 4;
    cpu.pc = pc;
    DD(compare_cpu(&cpu, &old_cpu));
  } while (!exit_program);
  return exit_program;
}

void printMem() {
  char buf[64];
  enum {SKIPPED=1, NORMAL=2} state = 0;
  for (mval base = 0; base < MEMSIZE; base += 16) {
    int seenNonZero = 0;
    char *p = buf;
    p += sprintf(p, "%8X:", base);
    for (int i = 0; i < 16; ++i) {
      unsigned char c = mem[base + i];
      p += sprintf(p, " %02X", c);
      seenNonZero |= !!c;
    }
    if (seenNonZero) {
      if (state == SKIPPED+NORMAL) dprintf(2, "\n");
      dprintf(2, "%s\n", buf);
      state = NORMAL;
    } else {
      state |= SKIPPED;
    }
  }
}

int main(int argc, char **argv) {
  if (argc != 2) die("Usage: %s intel_hex_file", argv[0]);
  mval start_pc = readHexFile(argv[1], mem, MEMSIZE);
  DD(printMem());
  int status = runCPU(start_pc);
  return status;
}
