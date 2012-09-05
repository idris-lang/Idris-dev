int main(int argc, char* argv[]) {
    VM* vm = init_vm(1024000, 1024000);

    _idris_main(vm, NULL);
#ifdef IDRIS_DEBUG
    printf("\nStack: %p %p\n", vm->valstack, vm->valstack_top); 
    printf("GCs: %d\n", vm->collections);
    printf("Final heap size %d\n", (int)(vm->heap_size));
    printf("Final heap use %d\n", (int)(vm->heap_next - vm->heap));
    gc(vm);
    printf("Final heap use after GC %d\n", (int)(vm->heap_next - vm->heap));
#endif
}
