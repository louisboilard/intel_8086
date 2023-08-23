//! Intel 8086 CPU simulator.
//!
//! Instructions follow the 16 bits pattern:
//!
//! First byte: [6bits: op_code][1bit: d_flag][1bit: w_flag]
//!
//! second byte: [2bits: mod_flag][3bit: reg_flag][3bit: rm_flag]

use std::fmt;
use std::fmt::Display;
use std::str;
use std::str::FromStr;

// Instruction size in bytes
const INSTRUCTION_SIZE: usize = 2;

type InstructionTuple = (u8, u8);

/* ===============================================
*  =============== BIT MASKS =====================
*  ===============================================
*/

// MASKS FOR THE FIRST BYTE OF AN INSTRUCTION

// Instruction Mask. 6 highest bits represent the instruction.
const OPCODE_MASK: u8 = 0b1111_1100;
// D Flag Mask. 7th bit.
const D_FLAG_BITS_MASK: u8 = 0b0000_0010;
// D Flag Mask. LSB of the first byte.
const W_FLAG_BITS_MASK: u8 = 0b0000_0001;

// MASKS FOR THE SECOND BYTES OF AN INSTRUCTION

// Mod Flag Mask. 6 highest bits represent the instruction.
const MOD_FLAG_BITS_MASK: u8 = 0b1100_0000;
// REG Flag Mask. 7th bit.
const REG_FLAG_BITS_MASK: u8 = 0b0011_1000;
// RM Flag Mask. bits 6-7-8
const RM_FLAG_BITS_MASK: u8 = 0b0000_0111;

/* ===============================================
*  ===============================================
*  ===============================================
*/

/* ===============================================
*  ===============  OP CODE  =====================
*  ===============================================
*/

/// CPU Instructions
#[derive(Debug)]
pub enum OpCode {
    /// MOV DST, SRC (copy)
    MOV,
    /// Represents an unrecognized instruction.
    UNKNOWN,
}

impl OpCode {
    /// Returns a mnemonic variant based on the byte's value.
    pub fn from_binary(val: u8) -> Option<Self> {
        // remove extra 2 bits from the byte, since opcode width = 6bits
        let six_bits_value: u8 = val >> 2;
        match six_bits_value {
            // MOV is 100010 (34) with 6bits
            34 => Some(Self::MOV),
            _ => None,
        }
    }

    /// Returns a byte representing the 6bit for the opcode.
    pub fn to_byte(&self) -> Option<u8> {
        match self {
            Self::MOV => Some(136),
            _ => None,
        }
    }

    /// Returns a mnemonic variant based on asm op_code
    pub fn from_text(op_code: &str) -> Option<Self> {
        match op_code {
            "mov" | "MOV" => Some(Self::MOV),
            _ => None,
        }
    }
}

impl Display for OpCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/* ===============================================
*  ===============  REGISTER  ====================
*  ===============================================
*/

/// Registers. H -> High byte. L -> Low byte. X -> Full 16 bits
#[derive(Debug, PartialEq, Eq)]
pub enum Register {
    /// AX -> General purpose register A, using all 16 bits.
    Ax,
    /// Al -> General purpose register A, using the lower 8 bits.
    Al,
    /// Ah -> General purpose register A, using the upper 8 bits.
    Ah,
    /// Bx -> General purpose register B, using all 16 bits.
    Bx,
    /// Bl -> General purpose register B, using the lower 8 bits.
    Bl,
    /// Bh -> General purpose register B, using the upper 8 bits.
    Bh,
    /// Cx -> General purpose register C, using all 16 bits.
    Cx,
    /// Cl -> General purpose register C, using the lower 8 bits.
    Cl,
    /// Ch -> General purpose register C, using the upper 8 bits.
    Ch,
    /// Dx -> General purpose register D, using all 16 bits.
    Dx,
    /// Dl -> General purpose register D, using the lower 8 bits.
    Dl,
    /// Dh -> General purpose register D, using the upper 8 bits.
    Dh,
    Sp,
    Bp,
    Si,
    Di,
    /// An unrecognized register.
    UNKNOWN,
}

impl Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl FromStr for Register {
    type Err = ();

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        match input {
            "ax" => Ok(Self::Ax),
            "al" => Ok(Self::Al),
            "ah" => Ok(Self::Ah),
            "bx" => Ok(Self::Bx),
            "bl" => Ok(Self::Bl),
            "bh" => Ok(Self::Bh),
            "cx" => Ok(Self::Cx),
            "cl" => Ok(Self::Cl),
            "ch" => Ok(Self::Ch),
            "dx" => Ok(Self::Dx),
            "dl" => Ok(Self::Dl),
            "dh" => Ok(Self::Dh),
            "sp" => Ok(Self::Sp),
            "bp" => Ok(Self::Bp),
            "si" => Ok(Self::Si),
            "di" => Ok(Self::Di),
            _ => Err(()),
        }
    }
}

impl Register {
    /// Outputs which register the wide and register(REG/RM) flags represent.
    fn from_flags(wide_flag: u8, register_flag: u8) -> Self {
        // Wide is a bitflag of size 1. reg is 3bits wide.
        if wide_flag > 1 || register_flag > 7 {
            return Self::UNKNOWN;
        }

        // When wide == 1, the instruction is on 16bits.
        match wide_flag {
            1 => match register_flag {
                0 => Self::Ax,
                1 => Self::Cx,
                2 => Self::Dx,
                3 => Self::Bx,
                4 => Self::Sp,
                5 => Self::Bp,
                6 => Self::Si,
                7 => Self::Di,
                _ => Self::UNKNOWN,
            },
            // wide == 0 -> instruction is on 8bits.
            0 => match register_flag {
                0 => Self::Al,
                1 => Self::Cl,
                2 => Self::Dl,
                3 => Self::Bl,
                4 => Self::Ah,
                5 => Self::Ch,
                6 => Self::Dh,
                7 => Self::Bh,
                _ => Self::UNKNOWN,
            },
            _ => Self::UNKNOWN,
        }
    }

    /// Outputs the wide flag and the register flags from register values.
    /// Ex: dst src -> 0b0000_00(d, w), 0b(mod, reg, rm)
    fn to_flags(dst: Self, src: Self) -> Option<InstructionTuple> {
        if dst == Register::UNKNOWN || src == Register::UNKNOWN {
            return None;
        }
        // edge.edx.org/c4x/BITSPilani/EEE231/asset/8086_family_Users_Manual_1_.pdf
        // page 160

        // TODO: potential correction(s) here.

        // assuming d bit is always set to 0 ? -> probably not.
        let d_flag = Flag::new_d(None);
        let mut w_flag = Flag::new_w(None);
        // for general purpose registers it seems like mod is always 0b_0000_0011
        let mod_flag = Flag::new_mod(Some(3));
        let mut reg_flag = Flag::new_reg(None);
        let mut rm_flag = Flag::new_rm(None);

        // check src to set reg and dst to check rm

        // When wide == 1, instruction operates on 16bits.
        match src {
            Self::UNKNOWN => return None,
            // W_flag == 1;
            Self::Ax => {
                w_flag.set_value(1);
            }
            Self::Cx => {
                w_flag.set_value(1);
                reg_flag.set_value(1);
            }
            Self::Dx => {
                w_flag.set_value(1);
                reg_flag.set_value(2);
            }
            Self::Bx => {
                w_flag.set_value(1);
                reg_flag.set_value(3);
            }
            Self::Sp => {
                w_flag.set_value(1);
                reg_flag.set_value(4);
            }
            Self::Bp => {
                w_flag.set_value(1);
                reg_flag.set_value(5);
            }
            Self::Si => {
                w_flag.set_value(1);
                reg_flag.set_value(6);
            }
            Self::Di => {
                w_flag.set_value(1);
                reg_flag.set_value(7);
            }
            // W_flag == 0;
            Self::Al => (),
            Self::Cl => {
                reg_flag.set_value(1);
            }
            Self::Dl => {
                reg_flag.set_value(2);
            }
            Self::Bl => {
                reg_flag.set_value(3);
            }
            Self::Ah => {
                reg_flag.set_value(4);
            }
            Self::Ch => {
                reg_flag.set_value(5);
            }
            Self::Dh => {
                reg_flag.set_value(6);
            }
            Self::Bh => {
                reg_flag.set_value(7);
            }
        }

        // W_flag == 1;
        match dst {
            Self::UNKNOWN => return None,
            Self::Ax | Self::Al => {}
            Self::Cx | Self::Cl => {
                rm_flag.set_value(1);
            }
            Self::Dx | Self::Dl => {
                rm_flag.set_value(2);
            }
            Self::Bx | Self::Bl => {
                rm_flag.set_value(3);
            }
            Self::Sp | Self::Ah => {
                rm_flag.set_value(4);
            }
            Self::Bp | Self::Ch => {
                rm_flag.set_value(5);
            }
            Self::Si | Self::Dh => {
                rm_flag.set_value(6);
            }
            Self::Di | Self::Bh => {
                rm_flag.set_value(7);
            }
        }

        // d_flag at bit 1 and w_flag at bit 0
        let mut first_byte = d_flag.get_value() << 1;
        first_byte |= w_flag.get_value();

        let mut second_byte = mod_flag.get_value() << reg_flag.get_width() | reg_flag.get_value();
        second_byte = second_byte << rm_flag.get_width() | rm_flag.get_value();

        Some((first_byte, second_byte))
    }
}

/* ===============================================
*  ============== BITFLAG/FLAG ===================
*  ===============================================
*/
/// A variable width bit flag
pub struct BitFlag {
    /// The number of bits for the flag.
    width: u8,
    /// The flag's value. Defaults to 0.
    value: u8,
}

/// CPU Flag
pub enum Flag {
    /// 1 bit. Specifies if the REG flag represents SRC (when 0) or DST (when 1)
    D(BitFlag),
    /// 1 bit. Wide. 0 means the instruction is operating on 1byte. 1 means 16 bytes.
    W(BitFlag),
    /// 2 bits. Memory or register operation (register-register, register-mem..)
    MOD(BitFlag),
    /// 3 bit. Encodes a register.
    REG(BitFlag),
    /// 3 bit. Encodes a register or memory (depending on MOD).
    RM(BitFlag),
}

impl Flag {
    /// Returns the number of bits of a flag.
    pub fn get_width(&self) -> u8 {
        match self {
            Flag::D(flag) => flag.width,
            Flag::W(flag) => flag.width,
            Flag::MOD(flag) => flag.width,
            Flag::REG(flag) => flag.width,
            Flag::RM(flag) => flag.width,
        }
    }

    /// Returns the flag's value.
    pub fn get_value(&self) -> u8 {
        match self {
            Flag::D(flag) => flag.value,
            Flag::W(flag) => flag.value,
            Flag::MOD(flag) => flag.value,
            Flag::REG(flag) => flag.value,
            Flag::RM(flag) => flag.value,
        }
    }

    /// Sets the flag's value.
    pub fn set_value(&mut self, val: u8) {
        match self {
            Flag::D(flag) => flag.value = val,
            Flag::W(flag) => flag.value = val,
            Flag::MOD(flag) => flag.value = val,
            Flag::REG(flag) => flag.value = val,
            Flag::RM(flag) => flag.value = val,
        }
    }

    /// Creates a new D Instruction Flag.
    pub fn new_d(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::D(BitFlag {
                width: 1,
                value: val,
            }),
            None => Flag::D(BitFlag { width: 1, value: 0 }),
        }
    }

    /// Creates a new W Instruction Flag.
    pub fn new_w(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::W(BitFlag {
                width: 1,
                value: val,
            }),
            None => Flag::W(BitFlag { width: 1, value: 0 }),
        }
    }

    /// Creates a new MOD Instruction Flag.
    pub fn new_mod(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::MOD(BitFlag {
                width: 2,
                value: val,
            }),
            None => Flag::MOD(BitFlag { width: 2, value: 0 }),
        }
    }

    /// Creates a new REG Instruction Flag.
    pub fn new_reg(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::REG(BitFlag {
                width: 3,
                value: val,
            }),
            None => Flag::REG(BitFlag { width: 3, value: 0 }),
        }
    }

    /// Creates a new RM Instruction Flag.
    pub fn new_rm(value: Option<u8>) -> Self {
        match value {
            Some(val) => Flag::RM(BitFlag {
                width: 3,
                value: val,
            }),
            None => Flag::RM(BitFlag { width: 3, value: 0 }),
        }
    }
}

impl Display for Flag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let val = self.get_value();
        write!(
            f,
            "width: {}, value: {} -> {:#b}",
            self.get_width(),
            val,
            val
        )
    }
}

/* ===============================================
*  ============== INSTRUCTION ====================
*  ===============================================
*/

/// An intel_8086 Instruction
/// i.e: ```MOV AX,BX```
pub struct Instruction {
    /// Instruction's common name in asm (mov)
    mnemonic: OpCode,
    /// Number of bytes (2) for this instruction.
    width: usize,
    /// D bit flag
    pub d_flag: Flag,
    /// W bit flag
    pub w_flag: Flag,
    /// MOD bit flag
    pub mod_flag: Flag,
    /// REG bit flag
    pub reg_flag: Flag,
    /// RM bit flag
    pub rm_flag: Flag,
}

impl Instruction {
    pub fn new(
        mnemonic: OpCode,
        d_flag: Flag,
        w_flag: Flag,
        mod_flag: Flag,
        reg_flag: Flag,
        rm_flag: Flag,
    ) -> Self {
        Self {
            mnemonic,
            width: INSTRUCTION_SIZE,
            d_flag,
            w_flag,
            mod_flag,
            reg_flag,
            rm_flag,
        }
    }

    /// Converts to a String which represents the ASM instruction.
    /// Ex: ```MOV AX,BX`
    pub fn dissasemble(&self) -> String {
        let mut asm = self.mnemonic.to_string().to_ascii_lowercase() + " ";
        let dst = Register::from_flags(self.w_flag.get_value(), self.rm_flag.get_value());
        asm += dst.to_string().to_ascii_lowercase().as_str();
        asm += ", ";
        let src = Register::from_flags(self.w_flag.get_value(), self.reg_flag.get_value());
        asm += src.to_string().to_ascii_lowercase().as_str();
        asm
    }

    /// Converts to the 16bit binary representation of the instruction.
    pub fn assemble(&self) -> Result<[u8; 2], String> {
        // Opcode takes the first 6 bits of the first byte.
        let op_code = self.mnemonic.to_byte().unwrap();

        // First byte: [6bits: op code][1bit: d_flag][1bit: w_flag]
        let mut first_byte: u8 = op_code;

        let d_flag = self.d_flag.get_value();
        if d_flag > 1 {
            return Err(String::from("d_flag should be 0 or 1."));
        }
        // index of d_flag is 1
        first_byte |= d_flag << 1;
        let w_flag = self.w_flag.get_value();
        if w_flag > 1 {
            return Err(String::from("w_flag should be 0 or 1."));
        }
        // index of w_flag is 0
        first_byte |= w_flag;

        // mod_flag is 2 bits at MSB+ MSB-1 (11_000000)
        let mut second_byte: u8 = self.mod_flag.get_value();
        // reg_flag is 3 bits.
        second_byte = second_byte << self.reg_flag.get_width() | self.reg_flag.get_value();
        // rm flag is 3 bits.
        second_byte = second_byte << self.rm_flag.get_width() | self.rm_flag.get_value();

        Ok([first_byte, second_byte])
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "
{:?} instruction:
width: {},
d_flag: {},
w_flag: {},
mod_flag: {},
reg_flag: {},
rm_flag: {}
",
            self.mnemonic,
            self.width,
            self.d_flag,
            self.w_flag,
            self.mod_flag,
            self.reg_flag,
            self.rm_flag,
        )
    }
}
impl Default for Instruction {
    fn default() -> Self {
        Self {
            mnemonic: OpCode::MOV,
            width: 2,
            d_flag: Flag::new_d(None),
            w_flag: Flag::new_d(None),
            mod_flag: Flag::new_mod(None),
            reg_flag: Flag::new_reg(None),
            rm_flag: Flag::new_rm(None),
        }
    }
}

/// Takes in an arbitrary number of 16 bits machine code instructions
/// Returns a Vec<Instruction>
pub fn read_instructions(instructions: &[u8]) -> Result<Vec<Instruction>, String> {
    // The number of bytes passed will always be a multiple of INSTRUCTION_SIZE
    if instructions.len() % INSTRUCTION_SIZE != 0 {
        return Err(format!(
            "Invalid number of bytes: {}, instructions should be a multiple of {}",
            instructions.len(),
            INSTRUCTION_SIZE
        ));
    }
    // instruction width == INSTRUCTION_SIZE
    let nb_instructions = instructions.len() / INSTRUCTION_SIZE;

    // TODO: check for potential usage of &[]. Box, Rc.
    let mut instructions_vec: Vec<Instruction> = Vec::with_capacity(nb_instructions);

    let mut index = 0;
    while index < nb_instructions {
        match read_instruction(instructions[index], instructions[index + 1]) {
            Ok(i) => instructions_vec.push(i),
            Err(e) => return Err(e),
        }
        index += 2;
    }

    Ok(instructions_vec)
}
/// Transforms a 2 bytes raw instruction into it's type representation.
pub fn read_instruction(high_byte: u8, low_byte: u8) -> Result<Instruction, String> {
    let instruction_value = high_byte & OPCODE_MASK;
    let Some(instruction_mnemonic) = OpCode::from_binary(instruction_value) else {
        return Err(format!(
            "Invalid instruction of value {} is not a known instruction.",
            instruction_value
        ));
    };

    const BYTE_LENGTH: u8 = 8;
    // Get value + shift so that the set bits are at LSB in the byte.

    // mod has size 2 and starts at MSB.
    let mod_val = (low_byte & MOD_FLAG_BITS_MASK) >> (BYTE_LENGTH - 2);
    // reg has size 3 and starts at pos 3 from MSB (0011_1_000)
    let reg_val = (low_byte & REG_FLAG_BITS_MASK) >> 3;
    // rm has size 3 and starts at pos 6 from MSB
    let rm_val = low_byte & RM_FLAG_BITS_MASK;

    Ok(Instruction::new(
        instruction_mnemonic,
        Flag::new_d(Some(high_byte & D_FLAG_BITS_MASK)),
        Flag::new_w(Some(high_byte & W_FLAG_BITS_MASK)),
        Flag::new_mod(Some(mod_val)),
        Flag::new_reg(Some(reg_val)),
        Flag::new_rm(Some(rm_val)),
    ))
}

/// Transforms asm text into instruction into it's type level representation.
/// i.e ```mov cx, bx ->  0b10001001 0b11011001```
pub fn read_asm(asm_inst: &str) -> Result<Instruction, String> {
    let inst: Vec<&str> = asm_inst.split(' ').collect();
    const ASM_INST_COMPONENTS: usize = 3; // opcode, dst, src
    if inst.len() != ASM_INST_COMPONENTS {
        return Err(format!(
            "Instruction should be of length {} but is of length {}",
            ASM_INST_COMPONENTS,
            inst.len()
        ));
    }

    // first 6 bits of first byte represent the op code.
    let op_code = OpCode::from_text(inst[0]).expect("Can't interpret asm instruction op code.");
    let binary_op_code = op_code.to_byte().unwrap();

    let dst = inst[1].replace(',', "");
    let src = inst[2].replace('\n', "");

    let dst_str = Register::from_str(&dst as &str).unwrap();
    let src_str = Register::from_str(&src as &str).unwrap();
    let byte_tuple = Register::to_flags(dst_str, src_str).unwrap();

    // First byte is opcode, d_flag, w_flag
    // Put the op_code in the first 6 slots from MSB
    let mut first_byte = binary_op_code;
    let d_flag = byte_tuple.0 & D_FLAG_BITS_MASK;
    first_byte |= d_flag << 1; // 1 is pos 2 from LSB (d_flag pos)
    let w_flag = byte_tuple.0 & W_FLAG_BITS_MASK;
    first_byte |= w_flag; // 0 is pos 1/LSB (w_flag pos)

    read_instruction(first_byte, byte_tuple.1)
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
        let inst = read_instruction(bin[0], bin[1]).unwrap();
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
    fn dissasemble_multiple_test() {
        let bin = include_bytes!("../data/binary/many_register_mov.txt");
        let asm = include_str!("../data/asm/many_register_mov.asm");

        let instructions = read_instructions(bin).unwrap();

        let mut splitted_asm = asm.lines();

        // compare all individual instructions with asm equivalent
        for inst in instructions.iter() {
            let dissas = inst.dissasemble();
            assert_eq!(dissas, splitted_asm.next().unwrap());
        }
    }

    #[test]
    fn dissasemble_test() {
        let single_asm_inst = include_str!("../data/asm/single_register_mov.asm");
        let inst = read_asm(single_asm_inst).unwrap();
        assert_eq!(
            inst.dissasemble(),
            single_asm_inst.to_owned().strip_suffix('\n').unwrap()
        );
    }
}
