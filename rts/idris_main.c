int main(int argc, char* argv[]) {
    VM* vm = init_vm(1024000, 1024000);
    _idris__123_runMain0_125_(vm, NULL);
    //_idris_main(vm, NULL);
#ifdef IDRIS_TRACE
    printf("\nStack: %p %p\n", vm->valstack, vm->valstack_top); 
    printf("Total allocations: %d\n", vm->allocations);
    printf("GCs: %d\n", vm->collections);
    printf("Final heap size %d\n", (int)(vm->heap_size));
    printf("Final heap use %d\n", (int)(vm->heap_next - vm->heap));
    gc(vm);
    printf("Final heap use after GC %d\n", (int)(vm->heap_next - vm->heap));
#endif
}
