int main(int argc, char* argv[]) {
    VM* vm = init_vm(1024000, 1024000);

    _idris_main(vm, NULL);
#ifdef IDRIS_DEBUG
    printf("\nStack: %p %p\n", vm->valstack, vm->valstack_top); 
#endif
}
