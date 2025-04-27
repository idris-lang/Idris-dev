# Idris RTS on FreeRTOS
The Idris RTS compiled without libc ontop of FreeRTOS tasks, using FreeRTOS queues as IPC. This
enables using Idris when programming microcontrollers and smaller systems, but it is also a step
towards the goal of building an Idris Unikernel.

FreeRTOS was chosen as abstraction layer towards the hardware since it's easy to port to new
architectures, since it's small, and since there already are a lot of port available.

## How to run Idris on FreeRTOS
See the instructions in the repository,
[mokshasoft/FreeRTOS-community-ports](https://github.com/mokshasoft/FreeRTOS-community-ports/tree/master/Demo/ARM926ejs-GCC-Idris).
