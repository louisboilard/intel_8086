//! Intel 8086 CPU simulator.
//!
//! Instructions follow the 16 bits pattern:
//!
//! First byte: [6bits: op_code][1bit: d_flag][1bit: w_flag]
//!
//! second byte: [2bits: mod_flag][3bit: reg_flag][3bit: rm_flag]

// TODO: add new inst type for ADD/MOV->immediate to register/memory,
// we are currently using immediate to register in mov's and have started a shitty
// impl to add ADD's, but it's not the proper inst type

mod bitflag;
pub mod instructions;
mod opcode;
mod register;

use crate::opcode::{OpCode, OpKind};
use instructions::*;

/// Takes in an arbitrary number of 16 bits machine code instructions
/// `Returns a Vec<Instruction>`
pub fn read_instructions(instructions: &[u8]) -> Result<Vec<Instruction>, String> {
    // smallest potential nb of instruction since smallest inst is INSTRUCTION_SIZE
    let nb_instructions = instructions.len() / INSTRUCTION_SIZE;
    let mut instructions_vec: Vec<Instruction> = Vec::with_capacity(nb_instructions);

    let mut index = 0;
    while index < instructions.len() {
        match OpCode::from_binary(instructions[index]) {
            Some((_, op_kind)) => match op_kind {
                OpKind::MemoryOrRegToReg => {
                    match RegisterToRegisterInst::from_bytes(
                        instructions[index],
                        instructions[index + 1],
                    ) {
                        Ok(i) => {
                            index += i.get_width();
                            instructions_vec.push(Instruction::RegisterToRegister(i));
                        }
                        Err(e) => return Err(e),
                    }
                }
                OpKind::ImmediateRegister => {
                    match ImmediateRegisterInst::from_bytes(
                        instructions[index],
                        instructions[index + 1],
                        instructions[index + 2],
                    ) {
                        Ok(i) => {
                            index += i.get_width();
                            instructions_vec.push(Instruction::ImmediateToRegister(i));
                        }
                        Err(e) => return Err(e),
                    }
                }
                OpKind::ImmediateToRegisterOrMemory => {
                    match ImmediateToRegisterMemInst::from_bytes(
                        instructions[index],
                        instructions[index + 1],
                        instructions[index + 2],
                    ) {
                        Ok(mut i) => {
                            // Order: disp-lo, disp-hi, data, data-hi
                            // extra bytes are the optional disp-lo, disp-hi and data-hi
                            let inst_width = i.get_width();
                            const MIN_INST_WIDTH: usize = 3;
                            assert!(inst_width >= MIN_INST_WIDTH);

                            const MAX_NB_EXTRA_BYTES: usize = 3;
                            let extra_bytes = inst_width - MAX_NB_EXTRA_BYTES;

                            // 0 would means the inst is the minimum size of
                            // 3 bytes (high, low, data)
                            if extra_bytes > 0 {
                                let current_index = index + 3;
                                let index_after_inst = current_index + extra_bytes;
                                let inst_extra_bytes: &[u8] =
                                    &instructions[current_index..index_after_inst];
                                i.set_data(inst_extra_bytes);
                            }

                            index += inst_width;
                            instructions_vec.push(Instruction::ImmediateToRegisterOrMemory(i));
                        }
                        Err(e) => return Err(e),
                    }
                }
                _ => return Err("Unknown instruction".to_owned()),
            },
            None => return Err("Could not parse instruction".to_owned()),
        };
    }

    Ok(instructions_vec)
}

// ***********************************************************************
// =======================================================================
// ================================ TESTS ================================
// =======================================================================
// ***********************************************************************
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn assemble_test() {
        let bin = include_bytes!("../data/binary/single_register_mov.txt");
        let inst = RegisterToRegisterInst::from_bytes(bin[0], bin[1]).unwrap();
        let bin_from_inst = inst.assemble().unwrap();
        assert_eq!(bin_from_inst, bin.to_owned());
    }

    #[test]
    fn assemble_multiple_test() {
        let bin = include_bytes!("../data/binary/many_register_mov.txt");
        let instructions = read_instructions(bin).unwrap();
        // compare all individual instructions with binary equivalent
        let mut count = 0;
        for i in instructions.iter() {
            let bytes: [u8; 2] = [bin[count], bin[count + 1]];
            assert_eq!(i.assemble().unwrap(), bytes);
            count += 2;
        }
    }

    #[test]
    fn disassemble_multiple_test() {
        let bin = include_bytes!("../data/binary/many_register_mov.txt");
        let asm = include_str!("../data/asm/many_register_mov.asm");

        let instructions = read_instructions(bin).unwrap();

        let mut splitted_asm = asm.lines();

        // compare all individual instructions with asm equivalent
        for inst in instructions.iter() {
            let dissas = inst.disassemble();
            assert_eq!(dissas.unwrap(), splitted_asm.next().unwrap());
        }
    }

    #[test]
    fn disassemble_test() {
        let single_asm_inst = include_str!("../data/asm/single_register_mov.asm");
        let bin = include_bytes!("../data/binary/single_register_mov.txt");
        let inst = read_instructions(bin).unwrap()[0];
        assert_eq!(
            inst.disassemble().unwrap(),
            single_asm_inst.to_owned().strip_suffix('\n').unwrap()
        );
    }

    #[test]
    fn assemble_test_immediate_mode() {
        let bin = include_bytes!("../data/binary/immediate_to_register.txt");
        let inst = read_instructions(bin).unwrap();
        let i1 = inst[0];
        let i2 = inst[1];
        let bin_from_inst = i1.assemble().unwrap();
        let bin2 = i2.assemble().unwrap();
        assert_eq!(bin_from_inst, bin.to_owned()[0..3]);
        assert_eq!(bin2, bin.to_owned()[3..6]);
    }

    #[test]
    fn disassemble_test_immediate_mode() {
        let bin = include_bytes!("../data/binary/immediate_to_register.txt");
        let asm = include_str!("../data/asm/immediate_to_register.asm");

        let instructions = read_instructions(bin).unwrap();

        let mut splitted_asm = asm.lines();

        // compare all individual instructions with asm equivalent
        for inst in instructions.iter() {
            let dissas = inst.disassemble();
            assert_eq!(dissas.unwrap(), splitted_asm.next().unwrap());
        }
    }
}
