#include "common.h"

// .data
static int D_1001D430 = 0;
static unsigned int D_1001D434 = 0;

// .bss
static TreeNode*** B_1002BAC0;
static unsigned int* B_1002BAC4;
static unsigned int* B_1002BAC8;

static int func_00419B80(TreeNode* arg0, TreeNode* arg1);
static void func_0041894C(TreeNode* t);

static TreeNode* func_00417880(TreeNode* type) {
    unsigned int level;
    int s0;
    unsigned int i;

    switch (TREE_CODE(type)) {
        case Struct_type:
            if (STRUCT_TYPE(type).sname == NULL) {
                __assert("STRUCT_TYPE(type).sname != EMPTY", "symtab.c", 114);
            }
            level = ID_DECL(STRUCT_TYPE(type).sname).level;
            break;

        case Enum_type:
            if (ENUM_TYPE(type).ename == NULL) {
                __assert("ENUM_TYPE(type).ename != EMPTY", "symtab.c", 118);
            }
            level = ID_DECL(ENUM_TYPE(type).ename).level;
            break;
        default:
            __assert("FALSE", "symtab.c", 122);
            break;
    }

    if (level >= D_1001D434) {
        s0 = D_1001D434 + 16;
        if (D_1001D434 == 0) {
            B_1002BAC0 = Malloc(0x40);
            B_1002BAC4 = Malloc(0x40);
            B_1002BAC8 = Malloc(0x40);
        } else {
            B_1002BAC0 = Realloc(B_1002BAC0, s0 * 4);
            B_1002BAC4 = Realloc(B_1002BAC4, s0 * 4);
            B_1002BAC8 = Realloc(B_1002BAC4, s0 * 4); // @BUG should be B_1002BAC8 instead of B_1002BAC4
        }

        for (i = D_1001D434; i < s0; i++) {
            B_1002BAC0[i] = NULL;
            B_1002BAC4[i] = 0;
            B_1002BAC8[i] = 0;
        }

        D_1001D434 = s0;
    }

    if (B_1002BAC8[level] <= B_1002BAC4[level]) {
        s0 = B_1002BAC8[level] + 32;
        if (B_1002BAC8[level] == 0) {
            B_1002BAC0[level] = Malloc(0x80);
        } else {
            B_1002BAC0[level] = Realloc(B_1002BAC0[level], s0 * 4);
        }

        B_1002BAC8[level] = s0;
    }

    B_1002BAC0[level][B_1002BAC4[level]] = type;
    B_1002BAC4[level]++;

    return type;
}

static void func_00417BD8(int level) {
    unsigned int i;
    TreeNode* type;
    TreeNode** s0;

    if (level < D_1001D434) {
        s0 = B_1002BAC0[level];
        for (i = 0; i < B_1002BAC4[level]; i++) {
            type = s0[i];

            switch (TREE_CODE(type)) {
                case Struct_type:
                    TREE_TYPE(type) = NULL;
                    TREE_ATTRIBUTE(type) = NULL;
                    STRUCT_TYPE(type).sname = NULL;
                    STRUCT_TYPE(type).members = NULL;
                    s0[i] = NULL;
                    break;

                case Enum_type:
                    TREE_TYPE(type) = NULL;
                    TREE_ATTRIBUTE(type) = NULL;
                    ENUM_TYPE(type).ename = NULL;
                    ENUM_TYPE(type).literals = NULL;
                    s0[i] = NULL;
                    break;

                default:
                    __assert("FALSE", "symtab.c", 216);
                    break;
            }
        }

        B_1002BAC4[level] = 0;
    }
}

static TreeNode* func_00417D1C(TreeNode* t) {
    int pad;
    TreeNode* copy;
    MemCtx* sp24;

    sp24 = tree_handle;
    tree_handle = general_handle;
    copy = duplicate_node(t);
    tree_handle = sp24;
    return copy;
}

static TreeNode* func_00417D74(TreeNode* t) {
    TreeNode* sp34;
    TreeNode* s1;
    TreeNode* s2;
    TreeNode* v0;
    TreeNode* a;
    TreeNode* b;

    if (t == NULL) {
        return NULL;
    }

    if (t->id <= last_stdtree_id) {
        return t;
    }

    switch (TREE_CODE(t)) {
        case Array_type:
            sp34 = duplicate_node(t);
            ARRAY_TYPE(sp34).index_type = func_00417D74(ARRAY_TYPE(t).index_type);
            TREE_TYPE(sp34) = func_00417D74(TREE_TYPE(t));
            break;

        case Struct_type:
            if (!(TREE_ATTRIBUTE(t) & TYPEDEF_ATTRIBUTE) &&
                !(TREE_ATTRIBUTE(t) & (VOLATILE_ATTRIBUTE | CONST_ATTRIBUTE | UNALIGNED_ATTRIBUTE)) &&
                STRUCT_TYPE(t).sname != NULL && ID_DECL(STRUCT_TYPE(t).sname).level == 2) {
                return t;
            }

            sp34 = duplicate_node(t);
            if ((TREE_CODE(t) == Struct_type ||
                 (TREE_CODE(t) == Enum_type && !(TREE_ATTRIBUTE(t) & PACKED_ATTRIBUTE))) &&
                TREE_TYPE(t) != NULL &&
                (TREE_ATTRIBUTE(t) & (VOLATILE_ATTRIBUTE | CONST_ATTRIBUTE | TYPEDEF_ATTRIBUTE))) {
                t = TREE_TYPE(t);
            }

            if (STRUCT_TYPE(t).sname != NULL) {
                if (ID_DECL(STRUCT_TYPE(t).sname).level == 2) {
                    return sp34;
                } else {
                    return func_00417880(sp34);
                }
            }

            TREE_TYPE(sp34) = NULL;
            TREE_ATTRIBUTE(sp34) = NULL;
            STRUCT_TYPE(sp34).sname = NULL;
            STRUCT_TYPE(sp34).members = NULL;
            break;

        case Func_type:
            sp34 = duplicate_node(t);
            s2 = NULL;

            for (s1 = FUNC_TYPE(sp34).params; s1 != NULL; s1 = TREE_LINK(s1)) {
                v0 = func_00417D1C(s1);
                TREE_LINK(v0) = NULL;
                TREE_TYPE(v0) = func_00417D74(TREE_TYPE(s1));

                if (s2 == NULL) {
                    s2 = v0;
                } else {
                    a = s2;
                    b = s2;
                    while (a != NULL) {
                        b = a;
                        a = TREE_LINK(a);
                    }
                    TREE_LINK(b) = v0;
                }
            }

            FUNC_TYPE(sp34).params = s2;
            TREE_TYPE(sp34) = func_00417D74(TREE_TYPE(t));
            break;

        case Enum_type:
            if (!(TREE_ATTRIBUTE(t) & TYPEDEF_ATTRIBUTE) &&
                !(TREE_ATTRIBUTE(t) & (VOLATILE_ATTRIBUTE | CONST_ATTRIBUTE | UNALIGNED_ATTRIBUTE)) &&
                ENUM_TYPE(t).ename != NULL && ID_DECL(ENUM_TYPE(t).ename).level == 2) {
                return t;
            }

            sp34 = duplicate_node(t);
            if ((TREE_CODE(t) == Struct_type ||
                 (TREE_CODE(t) == Enum_type && !(TREE_ATTRIBUTE(t) & PACKED_ATTRIBUTE))) &&
                TREE_TYPE(t) != NULL &&
                (TREE_ATTRIBUTE(t) & (VOLATILE_ATTRIBUTE | CONST_ATTRIBUTE | TYPEDEF_ATTRIBUTE))) {
                t = TREE_TYPE(t);
            }

            if (ENUM_TYPE(t).ename != NULL) {
                if (ID_DECL(ENUM_TYPE(t).ename).level == 2) {
                    return sp34;
                } else {
                    return func_00417880(sp34);
                }
            }

            TREE_TYPE(sp34) = NULL;
            TREE_ATTRIBUTE(sp34) = NULL;
            ENUM_TYPE(sp34).ename = NULL;
            ENUM_TYPE(sp34).literals = NULL;
            break;

        case Pointer_type:
            sp34 = duplicate_node(t);
            TREE_TYPE(sp34) = func_00417D74(TREE_TYPE(t));
            if (TREE_TYPE(t) != POINTER_TYPE(t).base_type) {
                POINTER_TYPE(sp34).base_type = func_00417D74(POINTER_TYPE(sp34).base_type);
            }
            break;

        default:
            sp34 = duplicate_node(t);
            break;
    }

    return sp34;
}

static void func_004181C8(TreeNode* t, TreeNode* arg1) {
    TreeNode* sp54;
    TreeNode* s7;
    MemCtx* sp4C;
    TreeNode* v0;
    TreeNode* a2;
    TreeNode* s0;

    sp54 = TREE_TYPE(t);
    sp4C = tree_handle;
    a2 = NULL;

    if (TREE_ATTRIBUTE(t) & EXTERN_ATTRIBUTE) {
        ID_DECL(t).flags |= 0x100;
    }

    for (s7 = arg1; s7 != NULL; s7 = ID_DECL(s7).hidden) {
        for (s0 = s7; s0 != NULL; s0 = ID_DECL(s0).overloads) {
            if ((TREE_ATTRIBUTE(s0) & EXTERN_ATTRIBUTE) && ID_DECL(s0).level == 2 ||
                (TREE_ATTRIBUTE(s0) & STATIC_ATTRIBUTE) && ID_DECL(s0).level == 2) {
                if (ID_DECL(s0).level != ID_DECL(t).level &&
                    (!(TREE_ATTRIBUTE(s0) & (EXTERN_ATTRIBUTE | STATIC_ATTRIBUTE)) || ID_DECL(s0).context == NULL ||
                     ID_DECL(s0).level != 2 || TREE_LOCATION(s0) != -1)) {
                    func_00419B80(t, s0);
                }
                a2 = s0;
            }
        }
    }

    if (a2 != NULL && ID_DECL(a2).level == 2) {
        if (TREE_ATTRIBUTE(a2) & INTR_ATTRIBUTE) {
            TREE_ATTRIBUTE(t) |= INTR_ATTRIBUTE;
        }
    } else {
        tree_handle = general_handle;
        v0 = duplicate_node(t);
        if (a2 != NULL) {
            ID_DECL(v0).blkno = ID_DECL(a2).blkno;
        }
        ID_DECL(v0).flags &= ~0x100;
        TREE_TYPE(v0) = sp54;
        ID_DECL(v0).level = 2;
        ID_DECL(v0).st_list = NULL;
        ID_DECL(v0).overloads = NULL;
        ID_DECL(v0).hidden = NULL;
        TREE_TYPE(v0) = func_00417D74(sp54);

        enter_id(v0);

        if (!options[OPTION_CPLUSPLUS] && !(options[OPTION_ANSI_MODE] & 1) && (TREE_ATTRIBUTE(v0) & EXTERN_ATTRIBUTE)) {
            ID_DECL(v0).context = NULL;
        }

        TREE_ATTRIBUTE(t) = TREE_ATTRIBUTE(v0);
        tree_handle = sp4C;
    }
}

void enter_id(TreeNode* id) {
    TreeNode* s1;
    TreeNode* v0;
    TreeNode* t1;
    int a0;

    if (TREE_CODE(id) != Id_decl) {
        __assert("TREE_CODE(id) == Id_decl", "symtab.c", 489);
    }

    if (ID_DECL(id).id == anonymous || ID_DECL(id).id == NULL) {
        mips_st(id);
        return;
    }

    if (TREE_ATTRIBUTE(id) & WEAK_ATTRIBUTE) {
        mips_st(id);
        return;
    }

    if (debug_arr['T'] > 0) {
        fprintf(dbgout,
                "Entering '%s'(overload class %d, symbol %x, scope %d, overloads %x, hidden %x) from instance table\n",
                ID_DECL(id).id->name, ID_DECL(id).oclass, ID_DECL(id).id, ID_DECL(id).level, ID_DECL(id).overloads,
                ID_DECL(id).hidden);
    }

    s1 = ID_DECL(id).id->constVal;
    if (s1 == NULL) {
        if ((!(TREE_ATTRIBUTE(id) & EXTERN_ATTRIBUTE) &&
                 !(!(TREE_ATTRIBUTE(id) & STATIC_ATTRIBUTE) && TREE_CODE(TREE_TYPE(id)) == Func_type &&
                   ID_DECL(id).init_value == NULL) ||
             ID_DECL(id).level != 2 || ID_DECL(id).context == NULL) &&
            ID_DECL(id).sclass != 7) {
            mips_st(id);
        }

        ID_DECL(id).id->constVal = id;
        ID_DECL(id).id->unk_10 = 0;
    } else {
        while (ID_DECL(s1).level > ID_DECL(id).level && ID_DECL(s1).hidden != NULL) {
            s1 = ID_DECL(s1).hidden;
        }

        if (ID_DECL(id).level == ID_DECL(s1).level) {
            if (func_00419B80(id, s1) &&
                ((TREE_ATTRIBUTE(id) & EXTERN_ATTRIBUTE) || TREE_CODE(TREE_TYPE(id)) == Func_type) &&
                ID_DECL(id).level >= FUNCTION_SCOPE()) {
                func_004181C8(id, s1);
            }

            return;
        }

        if (((TREE_ATTRIBUTE(id) & EXTERN_ATTRIBUTE) || TREE_CODE(TREE_TYPE(id)) == Func_type) &&
            ID_DECL(id).level >= FUNCTION_SCOPE()) {

            for (t1 = s1, a0 = FALSE; t1 != NULL && !a0; t1 = ID_DECL(t1).hidden) {
                for (v0 = t1; v0 != NULL && !a0; v0 = ID_DECL(v0).overloads) {
                    if ((TREE_ATTRIBUTE(v0) & EXTERN_ATTRIBUTE) ||
                        (!(TREE_ATTRIBUTE(v0) & STATIC_ATTRIBUTE) && TREE_CODE(TREE_TYPE(v0)) == Func_type &&
                         ID_DECL(v0).init_value == NULL) ||
                        (ID_DECL(v0).sclass == 5 || ID_DECL(v0).sclass == 6) && ID_DECL(v0).level == 2) {
                        a0 = TRUE;
                        ID_DECL(id).blkno = ID_DECL(v0).blkno;
                    }
                }
            }
        }

        if (ID_DECL(id).level < ID_DECL(s1).level && ID_DECL(s1).hidden == NULL) {
            if ((!(TREE_ATTRIBUTE(id) & EXTERN_ATTRIBUTE) &&
                     !(!(TREE_ATTRIBUTE(id) & STATIC_ATTRIBUTE) && TREE_CODE(TREE_TYPE(id)) == Func_type &&
                       ID_DECL(id).init_value == NULL) ||
                 ID_DECL(id).level != 2 || ID_DECL(id).context == NULL) &&
                ID_DECL(id).sclass != 7) {
                mips_st(id);
            }

            ID_DECL(s1).hidden = id;
        } else {
            if ((!(TREE_ATTRIBUTE(id) & EXTERN_ATTRIBUTE) &&
                     !(!(TREE_ATTRIBUTE(id) & STATIC_ATTRIBUTE) && TREE_CODE(TREE_TYPE(id)) == Func_type &&
                       ID_DECL(id).init_value == NULL) ||
                 ID_DECL(id).level != 2 || ID_DECL(id).context == NULL) &&
                ID_DECL(id).sclass != 7) {
                mips_st(id);
            }

            ID_DECL(id).hidden = s1;
            ID_DECL(id).id->constVal = id;
        }
    }

    func_0041894C(id);

    if (((TREE_ATTRIBUTE(id) & EXTERN_ATTRIBUTE) || TREE_CODE(TREE_TYPE(id)) == Func_type) &&
        ID_DECL(id).level >= FUNCTION_SCOPE()) {
        func_004181C8(id, s1);
    }
}

static void func_0041894C(TreeNode* id) {
    Scope* v0;
    TreeNode* type;

    v0 = current_scope;
    type = TREE_TYPE(id);

    if (ID_DECL(id).level != current_scope->unk_04) {
        if (ID_DECL(id).level == 2) {
            v0 = file_scope;
        } else if (id != NULL && TREE_CODE(id) == Id_decl && ID_DECL(id).init_value != NULL &&
                   TREE_CODE(TREE_TYPE(id)) == Func_type) {
            v0 = current_scope->unk_08;
        } else if (TREE_CODE(type) == Label_type) {
            v0 = function_scope;
        } else {
            __assert("FALSE", "symtab.c", 590);
        }
    }

    if (TREE_CODE(TREE_TYPE(id)) == Func_type && ID_DECL(id).level == 2) {
        if (v0->unk_18 == NULL) {
            ID_DECL(id).st_list = v0->unk_00;
            v0->unk_18 = id;
            v0->unk_00 = id;
        } else {
            ID_DECL(id).st_list = ID_DECL(v0->unk_18).st_list;
            ID_DECL(v0->unk_18).st_list = id;
        }
    } else {
        ID_DECL(id).st_list = v0->unk_00;
        v0->unk_00 = id;
    }
}

#pragma GLOBAL_ASM("asm/7.1/functions/cfe/symtab/lookup_id.s")

#pragma GLOBAL_ASM("asm/7.1/functions/cfe/symtab/push_scope.s")

#pragma GLOBAL_ASM("asm/7.1/functions/cfe/symtab/pop_scope.s")

#pragma GLOBAL_ASM("asm/7.1/functions/cfe/symtab/func_004194B4.s")

// #pragma GLOBAL_ASM("asm/7.1/functions/cfe/symtab/func_00419B80.s")
static int func_00419B80(TreeNode* arg0, TreeNode* arg1) {
    return 0;
}

#pragma GLOBAL_ASM("asm/7.1/functions/cfe/symtab/mark_id_used.s")

#pragma GLOBAL_ASM("asm/7.1/functions/cfe/symtab/check_static_functions.s")
