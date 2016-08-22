#include <stdio.h>
#include <stdlib.h>

void doSystem(const char cmd[]) {
  printf("exit1: Executing cmd '%s'\n", cmd);
  int exitStatus = system(cmd);
  printf("exit1: raw exitStatus = %d\n", exitStatus); // XXX: Probably not portable (hide from expected file).
  if (WIFEXITED(exitStatus)) {
    printf("exit1: WEXITSTATUS(exitStatus) = %d\n", WEXITSTATUS(exitStatus));
  }
}

int main() {
  doSystem("exit 1");
  doSystem("./does-not-exist");
  return 1;
}
