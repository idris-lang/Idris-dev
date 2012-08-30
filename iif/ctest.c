#include <idris_rts.h>

void plus(VM* vm, VAL* oldbase) {
    INITFRAME;
    RESERVE(2);
    ADDTOP(2);

    switch(TAG(LOC(0))) {
    case 0:
        PROJECT(vm, LOC(0), 2, 0);
        RVAL = LOC(1);
        TOPBASE(0);
        REBASE;
        break;
    case 1:
        PROJECT(vm, LOC(0), 2, 1);
        RESERVE(2);
        TOP(0) = LOC(2);
        TOP(1) = LOC(1);
        STOREOLD;
        BASETOP(0);
        ADDTOP(2);
        CALL(plus);
        LOC(3) = RVAL;
        RVAL = MKCON(vm, 1, 1, LOC(3));
        TOPBASE(0);
        REBASE;
        break;
    }
}

void natToInt(VM* vm, VAL* oldbase) {
    INITFRAME;
    RESERVE(3);
    ADDTOP(3);

    switch(TAG(LOC(0))) {
    case 0:
        PROJECT(vm, LOC(0), 2, 0);
        RVAL = MKINT(0);
        TOPBASE(0);
        REBASE;
        break;
    case 1:
        PROJECT(vm, LOC(0), 1, 1);
        RESERVE(1);
        TOP(0) = LOC(1);
        STOREOLD;
        BASETOP(0);
        ADDTOP(1);
        CALL(natToInt);
        LOC(2) = RVAL;
        RVAL = ADD(LOC(2), MKINT(1));
        TOPBASE(0);
        REBASE;
        break;
    }
}

int do_main(VM* vm, VAL* oldbase) {
    INITFRAME;
    RESERVE(2);
    ADDTOP(2);

    LOC(0) = MKCON(vm, 0, 0);
    LOC(0) = MKCON(vm, 1, 1, LOC(0));
    LOC(0) = MKCON(vm, 1, 1, LOC(0));

    dumpVal(LOC(0));
    printf("\n");

    LOC(1) = MKCON(vm, 0, 0);
    LOC(1) = MKCON(vm, 1, 1, LOC(1));
    LOC(1) = MKCON(vm, 1, 1, LOC(1));

    RESERVE(2);
    TOP(0) = LOC(0);
    TOP(1) = LOC(1);

    STOREOLD;
    BASETOP(0);
    ADDTOP(2);
    CALL(plus);
    LOC(0) = RVAL;    

    RESERVE(1);
    TOP(0) = LOC(0);
    SLIDE(vm, 1);
    TOPBASE(1);
    TAILCALL(natToInt);
/*    STOREOLD;
    BASETOP(0);
    ADDTOP(1);
    CALL(natToInt);
    TOPBASE(0);
    REBASE; */
}

int main() {
    VM* vm = init_vm(100,100);

    do_main(vm, NULL);
    printf("%ld\n", GETINT(RVAL));    

    printf("%d %d %d\n", vm->valstack, vm->valstack_base, vm->valstack_top);
}
