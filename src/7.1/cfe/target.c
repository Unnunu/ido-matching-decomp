#include "common.h"

typedef struct UnkTargetStruct {
    /* 0x00 */ char* name;
    /* 0x04 */ int name_length;
    /* 0x08 */ int offset;
    /* 0x0C */ int type;
} UnkTargetStruct; // size = 0x10

char* ident = "$Header: /hosts/bonnie/proj/irix6.4-ssg/isms/cmplrs/targucode/cfe/RCS/target.c,v 1.2 1993/01/07 17:49:29 rdahl Exp $";

char* sc_names[] = {
    "Template_sc",
    "Local_sc",
    "Heap_sc",
    "Param_sc",
    "Readonly_sc",
    "Static_sc",
    "Text_sc",
    "Register_sc"
};

int bit_size[] = {
    0,
    8,
    16,
    32,
    32,
    64,
    32,
    64,
    64,
    32
};

static UnkTargetStruct D_1001D81C[4] = {
    { "__$2", 4, 0, Int_type },
    { "__$f0", 5, 0, Float_type },
    { "__$do", 5, 0, Double_type },
    { "__$sp", 5, 0, Pointer_type }
};

void enter_registers(void) {
    int i;
    TreeNode* t;
    TreeNode* type;

    D_1001D81C[0].offset = bit_size[9] * 2;
    D_1001D81C[1].offset = bit_size[9] * 32;
    D_1001D81C[2].offset = bit_size[9] * 32;
    D_1001D81C[3].offset = bit_size[9] * 29;

    for (i = 0; i < 4; i++) {
        t = make(Id_decl, -1, string_to_symbol(D_1001D81C[i].name, D_1001D81C[i].name_length));
        ID_DECL(t).offset = D_1001D81C[i].offset;

        switch (D_1001D81C[i].type) {
            case Int_type:
                type = int_type;
                break;
            case Float_type:
                type = float_type;
                break;
            case Double_type:
                type = double_type;
                break;
            case Pointer_type:
                type = make_pointer(uchar_type);
                TREE_TYPE(type) = uchar_type;
                break;
        }

        declarator(t, 0, 7, 4, 0, type);
        enter_id(t);
    }
}