use std::fmt;
use std::fmt::Display;
use std::str::FromStr;

/* ===============================================
*  ===============  REGISTER  ====================
*  ===============================================
*/

/// Registers. H -> High byte. L -> Low byte. X -> Full 16 bits
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
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
    /// Ip -> Instruction Pointer.
    Ip,
    /// An unrecognized register.
    Unknown,
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
            "ip" => Ok(Self::Ip),
            _ => Err(()),
        }
    }
}

impl Register {
    /// Outputs which register the wide and register(REG/RM) flags represent.
    pub fn from_flags(wide_flag: u8, register_flag: u8) -> Self {
        // Wide is a bitflag of size 1. reg is 3bits wide.
        if wide_flag > 0b_0000_0111 || register_flag > 0b_0000_0111 {
            return Self::Unknown;
        }

        // When wide == 1, instruction is on 16bits.
        match wide_flag {
            1 => match register_flag {
                0b_0000_0000 => Self::Ax,
                0b_0000_0001 => Self::Cx,
                0b_0000_0010 => Self::Dx,
                0b_0000_0011 => Self::Bx,
                0b_0000_0100 => Self::Sp,
                0b_0000_0101 => Self::Bp,
                0b_0000_0110 => Self::Si,
                0b_0000_0111 => Self::Di,
                _ => Self::Unknown,
            },
            // wide == 0 -> instruction is on 8bits.
            0 => match register_flag {
                0b_0000_0000 => Self::Al,
                0b_0000_0001 => Self::Cl,
                0b_0000_0010 => Self::Dl,
                0b_0000_0011 => Self::Bl,
                0b_0000_0100 => Self::Ah,
                0b_0000_0101 => Self::Ch,
                0b_0000_0110 => Self::Dh,
                0b_0000_0111 => Self::Bh,
                _ => Self::Unknown,
            },
            _ => Self::Unknown,
        }
    }
}

/// Registers: registers and their values
#[derive(Debug)]
#[allow(dead_code)]
pub struct Registers {
    ax: u16,
    al: u8,
    ah: u8,
    bx: u16,
    bl: u8,
    bh: u8,
    cx: u16,
    cl: u8,
    ch: u8,
    dx: u16,
    dl: u8,
    dh: u8,
    sp: u16,
    bp: u16,
    si: u16,
    di: u16,
    ip: u16,
}

impl Registers {
    pub fn new() -> Self {
        Self {
            ax: 0,
            al: 0,
            ah: 0,
            bx: 0,
            bl: 0,
            bh: 0,
            cx: 0,
            cl: 0,
            ch: 0,
            dx: 0,
            dl: 0,
            dh: 0,
            sp: 0,
            bp: 0,
            si: 0,
            di: 0,
            ip: 0,
        }
    }

    /// Given a Register variant, update the corresponding struct member.
    pub fn update_from_register(&mut self, register: &Register, value: u16) {
        match register {
            Register::Ax => self.ax = value,
            Register::Al => self.al = value as u8,
            Register::Ah => self.ah = value as u8,
            Register::Bx => self.bx = value,
            Register::Bl => self.bl = value as u8,
            Register::Bh => self.bh = value as u8,
            Register::Cx => self.cx = value,
            Register::Cl => self.cl = value as u8,
            Register::Ch => self.ch = value as u8,
            Register::Dx => self.dx = value,
            Register::Dl => self.dl = value as u8,
            Register::Dh => self.dh = value as u8,
            Register::Sp => self.sp = value,
            Register::Bp => self.bp = value,
            Register::Si => self.si = value,
            Register::Di => self.di = value,
            Register::Ip => self.ip = value,
            Register::Unknown => (),
        }
    }

    pub fn update_instr_ptr(&mut self, value: usize) {
        self.ip = value as u16;
    }
}
