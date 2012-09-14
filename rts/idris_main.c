int main(int argc, char* argv[]) {
    VM* vm = init_vm(4096000, 2048000); // 1024000);
    _idris__123_runMain0_125_(vm, NULL);
    //_idris_main(vm, NULL);
#ifdef IDRIS_TRACE
    gcInfo(vm, 1);
#endif
}
