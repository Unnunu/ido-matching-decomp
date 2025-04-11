#include "common_p.h"

var
    float_li_flag: boolean;
    fp_pool_flag: boolean;
    current_mem_tag: 0..16383; { 14 bits }

procedure emitfli(op: opcodes; reg1: registers; arg2: integer); external;
function emit_fp_const(arg0: UnkFPStruct; arg1: boolean; arg2: boolean; arg3: Byte; var arg4: integer): PUnkAlpha; external;

procedure enforce_destreg(reg: registers; arg1: integer);
begin
end;

procedure genfpmultiple(arg0: asmcodes; arg1: registers; arg2: PUnkAlpha; arg3: integer; arg4: integer; arg5: integer; arg6: boolean; arg7: integer);
begin
end;

procedure gendouble(arg0: asmcodes; arg1: registers; arg2: PUnkAlpha; arg3: integer; arg4: registers; arg5: boolean);
begin
end;

procedure do_parseafra{(arg0: asmcodes; arg1: registers; arg2: PUnkAlpha; arg3: integer; arg4: registers)};
begin
end;

function check_if_gp_relative(arg0: PUnkALpha; arg1: integer): boolean;
begin
    return true;
end;

procedure parseafra{(fasm: asmcodes)};
var
    spDF: registers;
    spDE: registers;
    spD8: integer;
    spD4: PUnkAlpha;
    spD3: Byte; { enum ? }
    a2: PUnkALpha; 

    function func_0045FB50(arg0: registers; arg1: integer; arg2: PUnkAlpha): Byte;
    begin
        return 0;
    end;

    procedure func_004616A4(arg0: asmcodes; arg1: registers; arg2: PUnkAlpha; arg3: integer; arg4: registers);
    begin
    end;
begin
    with binasmfyle^ do begin
        current_mem_tag := mem_tag;
        spD4 := nil;
        spDF := reg1;
        spD8 := immediate;

        if symno <> 0 then begin
            spD4 := stp(symno);
            spD4^.unk3D := true;
        end;

        spDE := reg2;

        if (fasm = zdla) and diag_flag then begin
            if not((spDE = xnoreg) or (spDE = xr0)) then begin
                p_assertion_failed("(lbase = xnoreg) or (lbase = xr0)\0", "parsera.p", 1771);
            end;
            emitalui(op_zlui, spDF, xr0, 0);
            _setrld(spD4, 4, bbindex + proc_instr_base);
            emitalui(op_zori, spDF, spDF, 0);
            _setrld(spD4, 5, bbindex + proc_instr_base);
            emitshift(op_zdsll, spDF, spDF, 16);
            emitalui(op_zori, spDF, spDF, disp(true, spD8));
            _setrld(spD4, 2, bbindex + proc_instr_base);
            emitshift(op_zdsll, spDF, spDF, 16);
            emitalui(op_zdaddiu, spDF, spDF, disp(false, spD8));
            _setrld(spD4, 3, bbindex + proc_instr_base);
            return;
        end;
        
        if formextn <> franone then begin
            spD3 := func_0045FB50(spDE, spD8, spD4);
            func_004616A4(fasm, spDF, spD4, spD8, spDE);
            return;
        end;

        if sixtyfour_bit and (spD4 <> nil) and not check_if_gp_relative(spD4, spD8) then begin
            if not atflag then begin
                macro_error();
            end;
            a2 := emit_dword_item(-integer(spD8 < 0), spD8, spD4);
        end;
    end;
end;

procedure parseafri_fp{(fasm: asmcodes)};
var
    sp104: GString;
    v0: integer; { position on stack ? }
    spFC: PUnkAlpha;
    spEC: binasm;
    unused2: integer;
    spD8: UnkFPStruct;
    spD4: integer;
    spD3: Byte; { TODO enum }    
    spCC: integer;
    spCB: boolean;
    spCA: boolean;
    spC4: boolean;
    reg: registers;
    unused: integer;
    
    procedure func_0046303C(fasm: asmcodes; reg: registers; arg1: UnkFPStruct; var arg2: binasm);
    begin
    end;
begin

    if fasm = fli_e then begin
        PostError("li.e not yet supported", emptystring, ErrorLevel_1);
        fasm := fli_d;
    end;

    spEC := binasmfyle^;
    sp104.f := get_fp_string(spEC.immediate);

    if fasm = fli_s then begin
        spD3 := 13;
    end else begin
        spD3 := 11;
    end;

    string_to_fpoverlay(sp104, spD3, spD8, spCB, spCA);

    spC4 := (spEC.reg1 >= xfr0) and (spEC.reg1 < xfr31);

    if float_li_flag and spC4 then begin
        if fasm = fli_s then begin
            v0 := short_s(spD8.unk_00[1]);
        end else begin
            v0 := short_d(spD8.unk_00[1], spD8.unk_00[2]);
        end;
        if v0 <> 1024 then begin
            emitfli(asm2op[fasm], spEC.reg1, v0);
            return;
        end;
    end;

    reg := spEC.reg1;

    if fp_pool_flag and spC4 and (gprelsize >= 4 + 4 * integer(fasm = fli_d)) then begin
        func_0046303C(fasm, reg, spD8, spEC);
        return;
    end;

    if generate_as_immediate(fasm, reg, spD8.unk_00[1], spD8.unk_00[2]) then begin
        return;
    end;

    if fasm = fli_s then begin
        fasm := fl_s;
        spD4 := 1;
        spD3 := 13;
    end else begin
        fasm := fl_d;
        spD4 := 2;
        spD3 := 11;
        if isa <= ISA_MIPS2 then begin
            spD4 := 2;
            spD3 := 11;
            enforce_destreg(spEC.reg1, 2);
        end;
    end;

    spFC := emit_fp_const(spD8, spCB, spCA, spD3, spCC);

    if spC4 then begin
        genfpmultiple(fasm, spEC.reg1, spFC, 0, 0, spD4, isa >= ISA_MIPS2, 0);
    end else begin
        if not(fasm = fl_d) then begin
            p_assertion_failed("fasm = fl_d\0", "parsera.p", 2144);
        end;

        if isa <= ISA_MIPS2 then begin
            gendouble(zld, spEC.reg1, spFC, 0, xnoreg, false);
        end else begin
            do_parseafra(zld, spEC.reg1, spFC, 0, xnoreg);
        end;
    end;

    dispose(sp104.z);
end;