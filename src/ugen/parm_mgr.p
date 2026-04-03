#include "tree.h"
#include "tree_utils.h"
#include "report.h"
#include "ugen_regdef.h"

var
    fix_amt: array [0..3] of boolean;
    pars: array [0..3] of integer;

{ Эта функция вызывается либо для Upar, то есть параметра для вызова другой функции, 
либо для Updef, то есть входного параметра текущей функции
Для них Ival - это смещение в пространстве регистров, т.е. 0 - это gpr_zero, 4 - gpr_at  и так далее.
Соответственно, если Ival равно -1, то этот параметр нельзя передавать в регистре }
function pass_in_reg(parm: PTree): boolean;
begin
    Assert(parm^.u.Opc in [Upar, Updef]);
    return parm^.u.Constval.Ival <> -1;
end;

function parm_reg(parm: PTree): registers;
begin
    Assert(parm^.u.Opc in [Upar, Updef, Urpar, Uvreg]);

    if parm^.u.Constval.Ival = -1 then begin
        return xnoreg;
    end;

    if basicint = 0 then begin
        return registers(parm^.u.Constval.Ival div 4);
    end else begin
        return registers(parm^.u.Constval.Ival div 8);
    end;
end;


procedure map_pdefs_to_regs(pdef_list: PTree; stdarg_size: integer);
var
    parm_offset: integer;
    i: cardinal;
begin
    for i := 1 to n_fp_parm_regs do begin
        if pdef_list = nil then begin
            return;
        end;
            
        Assert(pdef_list^.u.Opc = Updef);

        if not (pdef_list^.u.Dtype in [Qdt, Rdt, Xdt]) then begin
            break;
        end;

        if (stdarg_size <> -1) and (stdarg_size < integer((i - 1) * 2) * 4) then begin
            break;
        end;

        pdef_list^.u.Constval.Ival := integer((i - 1) * 2) * 4 + ord(fpr_fa0) * 4;
        pdef_list := pdef_list^.next;                
    end;

    while pdef_list <> nil do begin
        Assert(pdef_list^.u.Opc = Updef);
        
        parm_offset := abs(pdef_list^.u.Offset - first_pmt_offset);

        if (basicint = 0) then begin
            if parm_offset < n_parm_regs * 4 then begin
                pdef_list^.u.Constval.Ival := parm_offset + 16;
            end else begin
                pdef_list^.u.Constval.Ival := -1;
            end;
        end else begin
            if parm_offset < (n_parm_regs * 8) then begin
                pdef_list^.u.Constval.Ival := parm_offset + 32;
            end else begin
                pdef_list^.u.Constval.Ival := -1;
            end;
        end;

        pdef_list := pdef_list^.next;
    end;
end;


procedure map_pars_to_regs(stmt: PTree; num_stdargs: integer);
label done;
var
    i: cardinal;
    parm_offset: integer;
    num_pars: integer;
    mst: ^Tree;
begin
    assert(stmt^.u.Opc = Umst);
    stmt^.u.I1 := 0;
    mst := stmt;
    
    num_pars := 4;
    for i := 0 to num_pars - 1 do pars[i] := -1;

    stmt := stmt^.next;
    for i := 1 to n_fp_parm_regs do begin
        
        if (stmt^.u.Opc in [Ucia, Ucup, Uicuf, Urcuf]) then begin
            goto done;
        end;

        while (stmt^.u.Opc <> Upar) and (stmt^.u.Opc <> Upmov) do begin
            if (stmt^.u.Opc in [Ucia, Ucup, Uicuf, Urcuf]) then begin
                goto done;
            end;
            stmt := stmt^.next;
        end;

        if not (stmt^.u.Dtype in [Qdt, Rdt, Xdt]) then begin
            break;
        end;
        
        if (num_stdargs <> -1) and (i >= num_stdargs) then begin
            break;
        end;

        parm_offset := abs(stmt^.u.Offset - first_pmt_offset);

        stmt^.u.Offset2 := (i - 1) * 8 + ord(fpr_fa0) * 4;
        pars[parm_offset div 4] := stmt^.u.Offset2;
        stmt := stmt^.next;
    end;

    while not (stmt^.u.Opc in [Ucia, Ucup, Uicuf, Urcuf]) do begin
        while (stmt^.u.Opc <> Upar) and (stmt^.u.Opc <> Upmov) do begin
            if stmt^.u.Opc in [Ucia, Ucup, Uicuf, Urcuf] then begin
                goto done;
            end;
            stmt := stmt^.next;
        end;

        parm_offset := abs(stmt^.u.Offset - first_pmt_offset);
        if basicint = 0 then begin        
            if stmt^.u.Opc <> Upmov then begin
                if parm_offset < n_parm_regs * 4 then begin
                    stmt^.u.Offset2 := parm_offset + 4 * ord(gpr_a0);
                    pars[parm_offset div 4] := stmt^.u.Offset2;
                end else begin
                    stmt^.u.Offset2 := -1;
                end;
            end;
        end else begin
            if stmt^.u.Opc <> Upmov then begin
                if parm_offset < n_parm_regs * 8 then begin
                    stmt^.u.Offset2 := parm_offset + 8 * ord(gpr_a0);
                    pars[parm_offset div 8] := stmt^.u.Offset2;
                end else begin
                    stmt^.u.Offset2 := -1;
                end;
            end;
        end;
        stmt := stmt^.next;
    end;
    
done:
    if (stmt^.u.Opc = Ucup) and IS_REALLOC_ARG_ATTR(stmt^.u.Extrnal) then begin
        mst^.u.I1 := 1;
    end;
end;

function check_amt(arg0: PTree): integer;
begin
    Assert(arg0^.u.Offset >= 0);

    if basicint = 0 then begin
        if (arg0^.u.Offset >= n_parm_regs * 4) or (arg0^.u.Offset >= cardinal(n_fp_parm_regs * 2) * 4) then begin
            return -1;
        end;
        return pars[arg0^.u.Offset div 4];
    end else begin
        if (arg0^.u.Offset >= n_parm_regs * 8) or (arg0^.u.Offset >= cardinal(n_fp_parm_regs * 2) * 4) then begin
            return -1;
        end;
        return pars[arg0^.u.Offset div 8];
    end;
end;

procedure check_amt_ref(arg0: ^tree);
label loop;
var
    temp_val: integer;
begin

    loop:
    arg0 := arg0;
    temp_val := 4; {Required to match}
    
    if (basicint = 0) then begin
        if (((arg0^.u.Opc = Ulod) and (arg0^.u.Mtype = Amt)) and ((arg0^.u.Offset < (n_parm_regs * 4)) 
            or (arg0^.u.Offset < (n_fp_parm_regs * 2 * temp_val)))) then begin
            pars[arg0^.u.Offset div 4] := -1;
            fix_amt[arg0^.u.Offset div 4] := true;
            return;
        end;
    end else if (((arg0^.u.Opc = Ulod) and (arg0^.u.Mtype = Amt)) and ((arg0^.u.Offset < (n_parm_regs * 8)) or (arg0^.u.Offset < (n_fp_parm_regs * 4 * temp_val)))) then begin
        pars[arg0^.u.Offset div 8] := -1;
        fix_amt[arg0^.u.Offset div 8] := true;
        return;
    end;
    
    if ((arg0^.op1 <> nil) and (arg0^.u.opc <> Ucg2)) then begin
        check_amt_ref(arg0^.op1);
    end;
    if (arg0^.op2 <> nil) then begin
	check_amt_ref(arg0^.op2);
    end;
    
end;

procedure fix_amt_ref(arg0: ^tree);
var
    i: integer; {s2}
    temp_v1: integer;
    temp_v0: ^tree;
    var_s0: ^tree; {s0}
    
begin
    temp_v1 := 3;
    
    for i := 0 to temp_v1 do begin
        fix_amt[i] := false;
    end;

    var_s0 := arg0^.next;
    while not (var_s0^.u.Opc in [Ucia, Ucup, Uicuf, Urcuf]) do begin        
        if (var_s0^.u.Opc = Upar) then begin
            check_amt_ref(var_s0^.op1);
        end;
        var_s0 := var_s0^.next;
    end;

    for i := 0 to temp_v1 do begin
        if (fix_amt[i]) then begin
            temp_v0 := build_op(Ulod);
            temp_v0^.u.Dtype := addr_dtype;
            temp_v0^.u.Mtype := Rmt;
            temp_v0^.u.Length := unitsperaddr;
            temp_v0^.u.Lexlev := 0;
            temp_v0^.u.Offset := (i + 4) * unitsperaddr;

            temp_v0 := build_1op(Ustr, temp_v0);
            temp_v0^.u.Dtype := addr_dtype;
            temp_v0^.u.Mtype := Amt;
            if true then; {FAKE}
            temp_v0^.u.Length := unitsperaddr;
            temp_v0^.u.Lexlev := 0;
            temp_v0^.u.Offset := i * unitsperaddr;

            temp_v0^.next := arg0^.next;
            arg0^.next := temp_v0;
        end;
    end;
    
end;
