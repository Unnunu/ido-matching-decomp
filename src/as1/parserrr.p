#include "common_p.h"

procedure smul(mult: cardinal; dreg: registers; sreg: registers);
var
    i: cardinal;
begin
    if mult = 1 then begin
        emitalu3(op_zaddu, dreg, sreg, xr0);
    end else if (mult mod 2) <> 0 then begin
        if bitand(mult, 2) <> 0 then begin
            smul(mult + 1, dreg, sreg);
            emitalu3(op_zsubu, dreg, dreg, sreg);
        end else begin
            smul(mult - 1, dreg, sreg);
            emitalu3(op_zaddu, dreg, dreg, sreg);
        end;
    end else begin
        i := 0;
        while (mult mod 2) = 0 do begin
            mult := mult div 2;
            i := i + 1;
        end;

        if mult = 1 then begin
            emitshift(op_zsll, dreg, sreg, i);
        end else begin
            smul(mult, dreg, sreg);
            emitshift(op_zsll, dreg, dreg, i);
        end;
    end;
end;

