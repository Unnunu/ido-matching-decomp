#ifndef PARM_MGR_H
#define PARM_MGR_H

function pass_in_reg(parm: PTree): boolean; external;
function parm_reg(parm: PTree): registers; external;

procedure fix_amt_ref(arg0: ^tree); external;
procedure map_pars_to_regs(arg0: ^Tree; arg1: integer); external;
function check_amt(arg0: ^Tree): integer; external;

#endif /* PARM_MGR_H */
