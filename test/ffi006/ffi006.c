#include "testHdr.h"

int main() {

    VM* vm = idris_vm();

    ListInt x = cons(vm, 10, cons(vm, 20, nil(vm)));
    ListInt y = cons(vm, 30, cons(vm, 40, nil(vm)));
    ListInt z = addLists(vm, x, y);

    printf("%s\n", showList(vm, z));

    close_vm(vm);
}
