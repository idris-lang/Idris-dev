int main(int argc, char* argv[]) {
    VM* vm = init_vm(1024000, 1024000);

    _idris_main(vm, NULL);
}
