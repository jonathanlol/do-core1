use clap::Parser;

/// Simple program to greet a person
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    /// Encoded instruction and operand
    #[clap(short, long)]
    val: u32,
}


/// 2-operands instruction structure
///
/// opcode is the operation to perfor
/// op0 is the left operand
/// op1 is the right operand
#[derive(Debug)]
struct Instruction {
    opcode: OpCode,
    op0: u8,
    op1: u8,
}

impl Instruction {
    // Instruction constructor, a.k.a. disassembler.
    fn disassemble(insn: u32) -> Instruction {
        // Keep the first 6 bits only
        let opcode = OpCode::from_u8((insn & 0x3f) as u8);

        // Shift right by 6, keep only the first 5 bits.
        let op0 = ((insn >> 6) & 0x1f) as u8;

        // Shift right by 11, keep only the first 5 bits.
        let op1: u8 = ((insn >> 11) & 0x1f) as u8;

        Instruction { opcode, op0, op1 }
    }

    fn exec(&self) -> u32 {
        match self.opcode {
            OpCode::ADD => add(self.op0.into(), self.op1.into()),
            OpCode::XOR => xor(self.op0.into(), self.op1.into()),
            OpCode::SHR => shr(self.op0.into(), self.op1.into()),
            OpCode::SHL => shl(self.op0.into(), self.op1.into()),
            _ => panic!("Unknown opcode {:?}", self.opcode),
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, PartialEq)]
enum OpCode {
    LDW = 0x00,
    STW = 0x01,
    ADD = 0x02,
    XOR = 0x03,
    SHR = 0x04,
    SHL = 0x05,
}

impl OpCode {
    fn from_u8(opcode: u8) -> OpCode {
        match opcode {
            0x00 => OpCode::LDW,
            0x01 => OpCode::STW,
            0x02 => OpCode::ADD,
            0x03 => OpCode::XOR,
            0x04 => OpCode::SHR,
            0x05 => OpCode::SHL,
            _ => panic!("Unknown opcode {:?}", opcode),
        }
    }
}

/// Add and returns the two operands
fn add(op0: u32, op1: u32) -> u32 {
    op0 + op1
}

/// Exclusive or between the two operands
fn xor(op0: u32, op1: u32) -> u32 {
    op0 ^ op1
}

/// Right shift left operand by right operand bits
fn shr(op0: u32, op1: u32) -> u32 {
    op0 >> op1
}

/// Left shift right operand by right operand bits
fn shl(op0: u32, op1: u32) -> u32 {
    op0 << op1
}

fn main() {
    // ADD R1, R3 -> Opcode is 2 (ADD), op0 is 1 (R1) and op1 is 3 (R3)
    // The first 6 bits of the instruction are the opcode (2): 0b000010
    // Bits 6 to 10 are for op0 (1): 0b000001
    // Bits 11 to 15 are for op1 (3): 0b000011
    // The instruction for ADD R1, R3 is: 00011 | 00001 | 000010, i.e. 0b0001100001000010
    //
    // When splitting this binary representation in groups of 4 bits, this looks like:
    // 0001 1000 0100 0010
    //  1     8   4    2
    // 0b0001100001000010 = 0x1842
    let cli: Args = Args::parse();
    let insn: u32 = cli.val;
    let mut r1: u32 = 20;
    let r3: u32 = 12;

    println!(
        "do-core-1: instruction {:#x?} Initial CPU state [R1:{:#x?} R3:{:#x?}]",
        insn, r1, r3
    );

    let decoded_instruction = Instruction::disassemble(insn);
    println!(
        "do-core-1: instruction decoded into {:?}",
        decoded_instruction
    );

    match decoded_instruction.opcode {
        OpCode::ADD => r1 = add(r1, r3),
        OpCode::XOR => r1 = xor(r1, r3),
        OpCode::SHR => r1 = shr(r1, r3),
        OpCode::SHL => r1 = shl(r1, r3),
        _ => panic!("Unknown opcode {:?}", decoded_instruction.opcode),
    }

    println!(
        "do-core-1: instruction {:#x?} Final CPU state [R1:{:#x?} R3:{:#x?}]",
        insn, r1, r3
    );
}

#[cfg(test)]
mod tests {
    use crate::{Instruction, OpCode};

    #[test]
    fn test_instruction_disassemble_add_r1_r3() {
        let insn_bytes: u32 = 0x1842;
        let insn = Instruction::disassemble(insn_bytes);

        assert_eq!(insn.opcode, OpCode::ADD);
        assert_eq!(insn.op0, 1);
        assert_eq!(insn.op1, 3);
    }

    #[test]
    fn test_instruction_disassemble_add_r7_r2() {
        let insn_bytes: u32 = 0x11c2;
        let insn = Instruction::disassemble(insn_bytes);

        assert_eq!(insn.opcode, OpCode::ADD);
        assert_eq!(insn.op0, 7);
        assert_eq!(insn.op1, 2);
    }

    #[test]
    fn test_instruction_disassemble_ldw_r0_r1() {
        let insn_bytes: u32 = 0x0800;
        let insn = Instruction::disassemble(insn_bytes);

        assert_eq!(insn.opcode, OpCode::LDW);
        assert_eq!(insn.op0, 0);
        assert_eq!(insn.op1, 1);
    }

    #[test]
    fn test_instruction_disassemble_xor_r2_r3() {
        let insn_bytes: u32 = 0x1883;
        let insn = Instruction::disassemble(insn_bytes);

        assert_eq!(insn.opcode, OpCode::XOR);
        assert_eq!(insn.op0, 2);
        assert_eq!(insn.op1, 3);
    }

    #[test]
    fn test_instruction_disassemble_stw_r5_r0() {
        let insn_bytes: u32 = 0x0141;
        let insn = Instruction::disassemble(insn_bytes);

        assert_eq!(insn.opcode, OpCode::STW);
        assert_eq!(insn.op0, 5);
        assert_eq!(insn.op1, 0);
    }

    #[test]
    fn test_add_exec() {
        let insn_bytes: u32 = 0x1842;
        let insn = Instruction::disassemble(insn_bytes);
        let res = insn.exec();

        assert_eq!(insn.opcode, OpCode::ADD);
        assert_eq!(insn.op0, 1);
        assert_eq!(insn.op1, 3);
        assert_eq!(res, 4);
    }

    #[test]
    fn test_shl_exec() {
        //                     op1  | op0  | instr
        let insn_bytes: u32 = 2<<11 | 5<<6 | 0x05;
        let insn = Instruction::disassemble(insn_bytes);

        assert_eq!(insn.opcode, OpCode::SHL);
        assert_eq!(insn.op0, 5);
        assert_eq!(insn.op1, 2);
        assert_eq!(insn.exec(), 20);
    }

    #[test]
    fn test_shr_exec() {
        //                     op1  | op0  | instr
        let insn_bytes: u32 = 2<<11 | 5<<6 | 0x04;
        let insn = Instruction::disassemble(insn_bytes);

        assert_eq!(insn.opcode, OpCode::SHR);
        assert_eq!(insn.op0, 5);
        assert_eq!(insn.op1, 2);
        assert_eq!(insn.exec(), 1);
    }

    #[test]
    fn test_shl_exec_overflow() {
        //                     op1  |   op0   | instr
        let insn_bytes: u32 = 2<<11 | 0x1F<<6 | 0x05;
        let insn = Instruction::disassemble(insn_bytes);

        assert_eq!(insn.opcode, OpCode::SHL);
        assert_eq!(insn.op0, 0x1F);
        assert_eq!(insn.op1, 2);
        assert_eq!(insn.exec(), 0x7C);
    }

    #[test]
    fn test_shr_exec_underflow() {
        //                     op1  | op0  | instr
        let insn_bytes: u32 = 2<<11 |0x05<<6 | 0x04;
        let insn = Instruction::disassemble(insn_bytes);

        assert_eq!(insn.opcode, OpCode::SHR);
        assert_eq!(insn.op0, 0x05);
        assert_eq!(insn.op1, 2);
        assert_eq!(insn.exec(), 1);
    }
}
