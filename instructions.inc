INSTRUCTION(auipc,  U, 0x00000017, 0x0000007f, rd = pc + imm)
INSTRUCTION(lui,    U, 0x00000037, 0x0000007f, rd = imm)
INSTRUCTION(jal,    J, 0x0000006f, 0x0000007f, rd = pc + 4; pc += imm)
INSTRUCTION(jalr,   L, 0x00000067, 0x0000707f, rd = pc + 4; pc = (rs1 + imm) & ~1)

INSTRUCTION(lb,     L, 0x00000003, 0x0000707f, rd = load(rs1 + imm, 1))
INSTRUCTION(sb,     S, 0x00000023, 0x0000707f, store(rs1 + imm, 1, rs2))
INSTRUCTION(lh,     L, 0x00001003, 0x0000707f, rd = load(rs1 + imm, 2))
INSTRUCTION(sh,     S, 0x00001023, 0x0000707f, store(rs1 + imm, 2, rs2))
INSTRUCTION(lw,     L, 0x00002003, 0x0000707f, rd = load(rs1 + imm, 4))
INSTRUCTION(sw,     S, 0x00002023, 0x0000707f, store(rs1 + imm, 4, rs2))
INSTRUCTION(lbu,    L, 0x00004003, 0x0000707f, rd = load(rs1 + imm, 1) & 0xff)
INSTRUCTION(lhu,    L, 0x00005003, 0x0000707f, rd = load(rs1 + imm, 2) & 0xffff)

INSTRUCTION(beq,    B, 0x00000063, 0x0000707f, if (rs1 == rs2) pc += imm)
INSTRUCTION(bne,    B, 0x00001063, 0x0000707f, if (rs1 != rs2) pc += imm)
INSTRUCTION(blt,    B, 0x00004063, 0x0000707f, if ((sval)rs1 <  (sval)rs2) pc += imm)
INSTRUCTION(bge,    B, 0x00005063, 0x0000707f, if ((sval)rs1 >= (sval)rs2) pc += imm)
INSTRUCTION(bltu,   B, 0x00006063, 0x0000707f, if (rs1 <  rs2) pc += imm)
INSTRUCTION(bgeu,   B, 0x00007063, 0x0000707f, if (rs1 >= rs2) pc += imm)

INSTRUCTION(addi,   I, 0x00000013, 0x0000707f, rd = rs1 + imm)
INSTRUCTION(slti,   I, 0x00002013, 0x0000707f, rd = (sval)rs1 < (sval)imm)
INSTRUCTION(sltiu,  I, 0x00003013, 0x0000707f, rd = rs1 < imm)
INSTRUCTION(xori,   I, 0x00004013, 0x0000707f, rd = rs1 ^ imm)
INSTRUCTION(ori,    I, 0x00006013, 0x0000707f, rd = rs1 | imm)
INSTRUCTION(andi,   I, 0x00007013, 0x0000707f, rd = rs1 & imm)

INSTRUCTION(slli,   I, 0x00001013, 0xfe00707f, rd = rs1 << imm)
INSTRUCTION(srli,   I, 0x00005013, 0xfe00707f, rd = rs1 >> imm)
INSTRUCTION(srai,   I, 0x40005013, 0xfe00707f, rd = (sval)rs1 >> imm)

INSTRUCTION(add,    R, 0x00000033, 0xfe00707f, rd = rs1 + rs2)
INSTRUCTION(sub,    R, 0x40000033, 0xfe00707f, rd = rs1 - rs2)
INSTRUCTION(sll,    R, 0x00001033, 0xfe00707f, rd = rs1 << (rs2&31))
INSTRUCTION(slt,    R, 0x00002033, 0xfe00707f, rd = (sval)rs1 < (sval)rs2)
INSTRUCTION(sltu,   R, 0x00003033, 0xfe00707f, rd = rs1 < rs2)
INSTRUCTION(xor,    R, 0x00004033, 0xfe00707f, rd = rs1 ^ rs2)
INSTRUCTION(srl,    R, 0x00005033, 0xfe00707f, rd = rs1 >> rs2)
INSTRUCTION(sra,    R, 0x40005033, 0xfe00707f, rd = (sval)rs1 >> (rs2&31))
INSTRUCTION(or,     R, 0x00006033, 0xfe00707f, rd = rs1 | rs2)
INSTRUCTION(and,    R, 0x00007033, 0xfe00707f, rd = rs1 & rs2)

INSTRUCTION(ecall,  X, 0x00000073, 0xffffffff, doECALL(&cpu))
INSTRUCTION(ebreak, X, 0x00100073, 0xffffffff, 0)
