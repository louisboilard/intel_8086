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
    /// ADD DST, SRC (addition)
    Add,
    /// Represents an unrecognized instruction.
    Unknown,
}

impl OpCode {
    /// Returns a mnemonic variant based on the byte's value.
    pub fn from_binary(val: u8) -> Option<(Self, OpKind)> {
        // register to register instructions have 6 bits op
        let register_to_register_op: u8 = val >> 2;

        // 4 bits
        let immediate_register_op: u8 = val >> 4;
        // 6 bits
        let immediate_register_or_memory_op: u8 = val >> 2;

        match register_to_register_op {
            // MOV is 100010 (34) with 6bits
            0b_0010_0010 => Some((Self::Mov, OpKind::MemoryOrRegToReg)),
            // TODO: change for real add
            0b_0010_0011 => Some((Self::Add, OpKind::MemoryOrRegToReg)),
            _ => {
                // check if facing an immediate register OP
                match immediate_register_op {
                    0b_0000_1011 => Some((Self::Mov, OpKind::ImmediateRegister)),
                    _ => match immediate_register_or_memory_op {
                        // Add op with s flag == 0
                        0b_0011_0001 => Some((Self::Mov, OpKind::ImmediateToRegisterOrMemory)),
                        // Add op with s flag == 0
                        0b_0010_0000 => Some((Self::Add, OpKind::ImmediateToRegisterOrMemory)),
                        // Add op with s flag == 1
                        0b_0010_0001 => Some((Self::Add, OpKind::ImmediateToRegisterOrMemory)),
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
                _ => None,
            },
            OpKind::ImmediateRegister => match self {
                Self::Mov => Some(0b_1011_0000),
                Self::Add => Some(0b_1000_0000),
                _ => None,
            },
            OpKind::ImmediateToRegisterOrMemory => match self {
                Self::Mov => Some(0b_0110_0011),
                Self::Add => Some(0b_0010_0000),
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
