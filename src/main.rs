use std::collections::HashMap;
use std::convert::TryFrom;


enum Rv64VmError {
    InvalidRegisterNumber(u16),
    InvalidOpCode(u32),
    InvalidMux2Control(u32),
    InvalidAluControl(u32),
}
type Error = Rv64VmError;

pub type Result<T> = ::std::result::Result<T, Rv64VmError>;

trait WriteMemory<T> {
    fn write(self: &mut Self, address: u32, value: T);
}

trait ReadMemory<T> {
    fn read(self: &mut Self, address: u32) -> T;
}

enum OpCode {
    BEQ     = 0b1100011,
    SW      = 0b0100011,
    LW      = 0b0000011,
    ADDI    = 0b0010011,
    RTYPE   = 0b0110011,
    HALT    = 0b0000000,
}

impl TryFrom<u32> for OpCode {
    type Error = Rv64VmError;
    fn try_from(code: u32) -> Result<OpCode> {
        Ok(match code {
            0b1100011 => OpCode::BEQ,
            0b0100011 => OpCode::SW,
            0b0000011 => OpCode::LW,
            0b0010011 => OpCode::ADDI,
            0b0110011 => OpCode::RTYPE,
            0b0000000 => OpCode::HALT,
            _ => return Err(Rv64VmError::InvalidOpCode(code)),
        })
    }
}

struct InstructionMemory {
    base_address    : u32,
    memory          : Vec<u32>,
    a               : u32,
    rd              : u32,
}

impl InstructionMemory {
    fn from_vec(instructions: Vec<u32>, base_address: u32) -> InstructionMemory {
        InstructionMemory { base_address: base_address
                          , memory      : instructions
                          , a           : 0
                          , rd          : 0
                          }
    }
    
    fn set_a(self: &mut Self, addr: u32) {
        self.a = addr;
    }

    fn clock_low(self: &mut Self) {
        self.rd = self.memory[self.a as usize];
    }

    fn clock_high(self: &mut Self) {

    }
}

impl ReadMemory<u32> for InstructionMemory {
    fn read(self: &mut Self, address: u32) -> u32 {
        return self.memory[(self.base_address + address) as usize];
    }
}

struct DataMemory {
    a               : u32,
    wd              : u32,
    we              : bool,
    rd              : u32,
    memory          : HashMap<u32, u32>,
}

impl DataMemory {
    fn set_a(self: &mut Self, val: u32) {
        self.a = val;
    }

    fn set_wd(self: &mut Self, val: u32) {
        self.wd = val;
    }

    fn set_we(self: &mut Self, val: bool) {
        self.we = val;
    }

    fn clock_low(self: &mut Self) {
        self.rd = *self.memory.entry(self.a).or_insert(0);
    }
    
    fn clock_high(self: &mut Self) {
        if self.we {
            self.memory.insert(self.a, self.wd);
        }
    }
}

struct RegisterFile {
    registers       : HashMap<u16, u32>,
    a1              : u16,
    a2              : u16,
    a3              : u16,
    wd3             : u32,
    we3             : bool,

    rd_1            : u32,
    rd_2            : u32,
}

impl RegisterFile {
    fn new() -> RegisterFile {
        RegisterFile { registers: HashMap::new()
                     , a1       : 0
                     , a2       : 0
                     , a3       : 0
                     , wd3      : 0
                     , we3      : false
                     , rd_1     : 0
                     , rd_2     : 0
                     }
    }

    fn set_a1(self: &mut Self, val: u16) -> Result<()> {
        if val > 2_u16.pow(5) {
            return Err(Rv64VmError::InvalidRegisterNumber(val));
        }
        self.a1 = val;
        Ok(())
    }

    fn set_a2(self: &mut Self, val: u16) -> Result<()> {
        if val > 2_u16.pow(5) {
            return Err(Rv64VmError::InvalidRegisterNumber(val));
        }
        self.a2 = val;
        Ok(())
    }

    fn set_a3(self: &mut Self, val: u16) -> Result<()> {
        if val > 2_u16.pow(5) {
            return Err(Rv64VmError::InvalidRegisterNumber(val));
        }
        self.a3 = val;
        Ok(())
    }

    fn set_wd3(self: &mut Self, val: u32) {
        self.wd3 = val;
    }

    fn set_we3(self: &mut Self, val: bool) {
        self.we3 = val;
    }

    fn clock_high(self: &mut Self) {
        if self.we3 {
            self.registers.insert(self.a3, self.wd3);
        }
    }

    // Reads take place on the falling edge of clock cycles. 
    fn clock_low(self: &mut Self) {
        self.rd_1 = *self.registers.entry(self.a1).or_insert(0);
        self.rd_2 = *self.registers.entry(self.a2).or_insert(0);
    }

    fn initialize_register(self: &mut Self, reg_num: u16, val: u32) {
        self.registers.insert(reg_num, val);
    }
}

struct Rv64Vm {
    program_counter     : u32,
    fd_register         : FDRegister,
    de_register         : DERegister,
    em_register         : EMRegister,
    mw_register         : MWRegister,
    wf_register         : WFRegister,
    instruction_memory  : InstructionMemory,
    data_memory         : DataMemory,
    register_file       : RegisterFile,
}

enum Rv64VmState {
    Idle,
    Halted,
}

impl Rv64Vm {
    fn execute_a_cycle(self: &mut Self) -> Result<Rv64VmState> {
        // If we have all the registers already, we should be able to start setting the input
        // values of all of the registers and memory units. 
        
        // BEGIN FETCH
        let pc = self.wf_register.pc_in;
        self.instruction_memory.set_a(pc);
        self.instruction_memory.clock_low();
    
        self.fd_register.pc_in = self.instruction_memory.rd;
        // END FETCH
        
        // BEGIN DECODE
        let instr = self.fd_register.instruction_out;
        let a1 = get_bits(19, 15, instr);
        let a2 = get_bits(24, 20, instr);

        // Don't really know what the better solutions for these casts is?
        self.register_file.set_a1(a1 as u16);
        self.register_file.set_a2(a2 as u16);
        self.register_file.clock_low();

        let rd_1 = self.register_file.rd_1;
        let rd_2 = self.register_file.rd_2;

        let inA = get_bits(31, 25, instr);
        let inB = get_bits(14, 12, instr);
        let inC = get_bits(6, 0, instr);
        
        let op_code = match OpCode::try_from(inC) {
            Ok(op_code) => op_code,
            Err(op_err) => return Err(op_err),
        };

        let (reg_write, mem_to_reg, mem_write, branch, alu_control, alu_src_a, alu_src_b) = 
            match op_code {
                OpCode::BEQ => (false, false, false, true, 0, 1, 0),
                OpCode::SW => (false, false, true, false, 0, 1, 1),
                OpCode::LW => (true, true, false, false, 0, 1, 1),
                OpCode::ADDI => (true, false, false, false, 0, 1, 1),
                OpCode::RTYPE => (true, false, false, false, inB, 0, 1),
                OpCode::HALT => (true, false, false, false, 0, 1, 1),
            };

        let immed = immed_gen(op_code, inA, inB);
        let rd = get_bits(11, 7, instr);
        
        self.de_register.reg_write_in = reg_write;
        self.de_register.mem_to_reg_in = mem_to_reg;
        self.de_register.mem_write_in = mem_write;
        self.de_register.branch_in = branch;
        self.de_register.alu_control_in = alu_control;
        self.de_register.alu_src_a_in = alu_src_a;
        self.de_register.alu_src_b_in = alu_src_b;
        // END DECODE
        
        // BEGIN EXECUTE
        let reg_write = self.de_register.reg_write_out;
        let mem_to_reg = self.de_register.mem_to_reg_out;
        let mem_write = self.de_register.mem_write_out;
        let branch = self.de_register.branch_out;
        let eq_comp = self.de_register.rd_1_out == self.de_register.rd_2_out;

        let alu_in_a = mux2(self.de_register.alu_src_a_out, self.de_register.pc_out, self.de_register.rd_1_out)?;
        let alu_in_b = mux2(self.de_register.alu_src_b_out, 
                            self.de_register.rd_2_out, self.de_register.immed_out)?;

        let alu_out = alu_comp(self.de_register.alu_control_out, alu_in_a as i32, alu_in_b as i32)?;
        let rd_2 = self.de_register.rd_2_out;
        let rd_1 = self.de_register.rd_1_out;
        
        self.em_register.reg_write_in = reg_write;
        self.em_register.mem_to_reg_in = mem_to_reg;
        self.em_register.mem_write_in = mem_write;
        self.em_register.branch_in = branch;
        self.em_register.eq_comp_in = eq_comp;
        self.em_register.alu_out_in = alu_out;
        self.em_register.rd_2_in = rd_2;
        self.em_register.rd_in = rd_1;
        // END EXECUTE

        // BEGIN MEM
        let reg_write = self.em_register.reg_write_out;
        let mem_to_reg = self.em_register.mem_to_reg_out;
        let alu_out = self.em_register.alu_out_out;

        self.data_memory.set_we(self.em_register.mem_write_out);
        self.data_memory.set_a(self.em_register.alu_out_out as u32);
        self.data_memory.set_wd(self.em_register.rd_2_out);
        self.data_memory.clock_low();
        let read_data = self.data_memory.rd;
        let rd = self.em_register.rd_out;

        self.mw_register.reg_write_in = reg_write;
        self.mw_register.mem_to_reg_in = mem_to_reg;
        self.mw_register.alu_out_in = alu_out as u32;
        self.mw_register.read_data_in = read_data;
        self.mw_register.rd_in = rd;
        // END MEM

        // BEGIN WB
        let result = mux2(self.mw_register.mem_to_reg_out as bool, self.mw_register.alu_out_out, 
                          self.mw_register.read_data_out);
        self.register_file.set_a3(self.mw_register.rd_out);
        self.register_file.set_wd3(result);
        self.register_file.set_we3(mw_register.reg_write_out);
        let and_result = match self.em_register.branch_out & self.em_register.eq_comp_out {
            0 => false,
            _ => true;
        };
        let pc = mux2(and_result, self.wf_register.pc_out + 4, self.em_register.alu_out_out)?;
        
        self.wf_register.pc_in = pc;
        Ok(Rv64VmState::Idle)
    }
}

struct FDRegister {
    pc_in           : u32,
    instruction_in  : u32,

    pc_out          : u32,
    instruction_out : u32,
}

struct DERegister {
    reg_write_in       : bool,
    mem_to_reg_in      : bool,
    mem_write_in       : bool,
    branch_in          : bool,
    alu_control_in     : u32,
    alu_src_a_in       : u32,
    alu_src_b_in       : u32,
    pc_in              : u32,
    rd_1_in            : u32,
    rd_2_in            : u32,
    immed_in           : u32,

    reg_write_out       : bool,
    mem_to_reg_out      : bool,
    mem_write_out       : bool,
    branch_out          : bool,
    alu_control_out     : u32,
    alu_src_a_out       : u32,
    alu_src_b_out       : u32,
    pc_out              : u32,
    rd_1_out            : u32,
    rd_2_out            : u32,
    immed_out           : u32,
}

struct EMRegister {
    reg_write_in       : bool,
    mem_to_reg_in      : bool,
    mem_write_in       : bool,
    branch_in          : bool,
    eq_comp_in         : bool,
    alu_out_in         : i32,
    rd_2_in            : u32,
    rd_in              : u32,

    reg_write_out       : bool,
    mem_to_reg_out      : bool,
    mem_write_out       : bool,
    branch_out          : bool,
    eq_comp_out         : bool,
    alu_out_out         : i32,
    rd_2_out            : u32,
    rd_out              : u32,
}

struct MWRegister {
    reg_write_in       : bool,
    mem_to_reg_in      : bool,
    alu_out_in         : u32,
    read_data_in       : u32,
    rd_in              : u32, 

    reg_write_out       : bool,
    mem_to_reg_out      : bool,
    alu_out_out         : u32,
    read_data_out       : u32,
    rd_out              : u32, 
}

struct WFRegister {
    pc_in             : u32,

    pc_out              : u32,
}

// BEGIN HELPERS
fn alu_comp(alu_control: u32, alu_in_a: i32, alu_in_b: i32) -> Result<i32> {
    Ok(match alu_control {
        0b000 => alu_in_a + alu_in_b,
        0b010 => if alu_in_a < alu_in_b {1} else {0},
        _ => return Err(Error::InvalidAluControl(alu_control)),
    })
}

fn get_bits(hi: u32, lo: u32, word: u32) -> u32 {
   (word >> lo) & (2_u32.pow(hi-lo)-1)
}

fn splice_bits(hi: u32, lo: u32, dest: u32, source: u32) -> u32 {
    ((source & (2_u32.pow(hi-lo)-1)) << lo) | dest
}

fn mux2(control: u32, a_in: u32, b_in: u32) -> Result<u32> {
    Ok(match control {
        0 => a_in,
        1 => b_in,
        _ => return Err(Error::InvalidMux2Control(control)),
    })
}

fn immed_gen(op_code: OpCode, inA: u32, inB: u32) -> i32 {
    match op_code {
        OpCode::BEQ => {
            let reconstructed  = (inA << 20) | inB;
            let bit_12 = get_bits(31, 31, reconstructed);
            let bits_10_to_5 = get_bits(30, 25, reconstructed);
            let bits_4_to_1 = get_bits(11, 8, reconstructed);
            let bit_11 = get_bits(7, 7, reconstructed);
            
            let mut dest_word: u32 = 0;
            dest_word = splice_bits(12, 12, dest_word, bit_12);
            dest_word = splice_bits(10, 5, dest_word, bits_10_to_5);
            dest_word = splice_bits(4, 1, dest_word, bits_4_to_1);
            dest_word = splice_bits(11, 11, dest_word, bit_11);
            
            dest_word as i32
        },
        OpCode::SW => {
            let reconstructed = (inA << 20) | inB;
            ((get_bits(31, 25, reconstructed) << 5) | get_bits(11, 7, reconstructed)) as i32
        },
        _ => {
            inA as i32
        },
    }
}
// END HELPERS
fn main() {
    println!("Hello, world!");
    let mut register_file = RegisterFile::new();
    register_file.initialize_register(10, 0x1001_0000);
    register_file.initialize_register(11, 0x1001_0014);
    register_file.initialize_register(12, 0x1212_1212);
    register_file.initialize_register(13, 0x0000_0000);
    register_file.initialize_register(14, 0x1414_1414);
}
