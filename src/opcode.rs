use std::fmt;
use std::fmt::Display;

/* ===============================================
*  ===============  OP CODE  =====================
*  ===============================================
*/

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum OpKind {
    /// Immediate to register
    ImmediateRegister,
    /// Immediate to register OR memory
    ImmediateToRegisterOrMemory,
    /// Mem/register to register
    MemoryOrRegToReg,
    Unknown,
}

/// CPU Instructions
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum OpCode {
    /// MOV DST, SRC (copy)
    Mov,
    /// Add DST, SRC (addition)
    Add,
    /// Sub DST, SRC (substraction)
    Sub,
    /// Cmp DST, SRC (comparison)
    Cmp,
    /// Represents an unrecognized instruction.
    Unknown,
}

impl OpCode {
    /// Returns a mnemonic variant based on the byte's value.
    /// second_byte required for certain type of instruction
    /// (namely immediate->register or memory)
    pub fn from_binary(val: u8, second_byte: Option<u8>) -> Option<(Self, OpKind)> {
        // register to register instructions have 6 bits op
        let register_to_register_op: u8 = val >> 2;

        // 4 bits
        let immediate_register_op: u8 = val >> 4;
        // 6 bits
        let immediate_register_or_memory_op: u8 = val >> 2;

        match register_to_register_op {
            // MOV is 100010 (34) with 6bits
            0b_0010_0010 => Some((Self::Mov, OpKind::MemoryOrRegToReg)),
            0b_0000_0000 => Some((Self::Add, OpKind::MemoryOrRegToReg)),
            0b_0000_1010 => Some((Self::Sub, OpKind::MemoryOrRegToReg)),
            0b_0000_1110 => Some((Self::Cmp, OpKind::MemoryOrRegToReg)),
            _ => {
                match immediate_register_or_memory_op {
                    0b_0011_0001 => Some((Self::Mov, OpKind::ImmediateToRegisterOrMemory)),
                    // Sub, SBB, CMP.. have the same first byte
                    // match against second byte's middle 3 bits
                    // (xx_YYY_xxx) to differentiate
                    0b_0010_0000 => {
                        match second_byte {
                            Some(b) => {
                                match b & 0b_0011_1000 {
                                    // 3 middle bits are 0s for add
                                    0b_0000_0000 => {
                                        Some((Self::Add, OpKind::ImmediateToRegisterOrMemory))
                                    }
                                    // 3 middle bits are 1s for cmp
                                    0b_0011_1000 => {
                                        Some((Self::Cmp, OpKind::ImmediateToRegisterOrMemory))
                                    }
                                    // 3 middle bits are 101 for sub
                                    0b_0010_1000 => {
                                        Some((Self::Sub, OpKind::ImmediateToRegisterOrMemory))
                                    }
                                    _ => None,
                                }
                            }
                            _ => Some((Self::Unknown, OpKind::ImmediateToRegisterOrMemory)),
                        }
                    }
                    _ => match immediate_register_op {
                        0b_0000_1011 => Some((Self::Mov, OpKind::ImmediateRegister)),
                        _ => None,
                    },
                }
            }
        }
    }

    /// Returns a byte representing the opcode.
    pub fn to_byte(self, kind: OpKind) -> Option<u8> {
        match kind {
            OpKind::MemoryOrRegToReg => match self {
                Self::Mov => Some(0b_1000_1000),
                Self::Add => Some(0b_0000_0000),
                Self::Sub => Some(0b_0010_1000),
                Self::Cmp => Some(0b_0011_1000),
                _ => None,
            },
            OpKind::ImmediateRegister => match self {
                Self::Mov => Some(0b_1011_0000),
                _ => None,
            },
            OpKind::ImmediateToRegisterOrMemory => match self {
                Self::Mov => Some(0b_1100_0011),
                Self::Add => Some(0b_1000_0000),
                Self::Sub => Some(0b_1000_0000),
                Self::Cmp => Some(0b_1000_0000),
                _ => None,
            },
            _ => None,
        }
    }
}

impl Display for OpCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
