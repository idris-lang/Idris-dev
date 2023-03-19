/*
 * Copyright 2020, Mokshasoft AB (mokshasoft.com)
 *
 * Redistribution and use in source and binary forms, with or without modification, are permitted
 * provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this list of
 * conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of
 * conditions and the following disclaimer in the documentation and/or other materials provided
 * with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
 * FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

/* The UART part of this code depends on the print driver of the versatilepb, remove or port
 * this part of the code if compiling for another platform.
 */

#include "idris_gmp.h"
#include "idris_opts.h"
#include "idris_rts.h"
#include "idris_stats.h"
#include "print.h"
#include <FreeRTOS.h>
#include <task.h>

void _idris__123_runMain_95_0_125_(VM* vm, VAL* oldbase);

RTSOpts opts = {
    .init_heap_size = 10000,
    .max_stack_size = 5000,
    .show_summary   = 0
};

static void uartLog(const char* msg) {
    vDirectPrintMsg(msg);
}

static void halt() {
    for (; ;);
}

void vRootThread(void* pvParameters) {
    VM* vm = init_vm(opts.max_stack_size, opts.init_heap_size, 1);
    init_gmpalloc();
    init_nullaries();
    _idris__123_runMain_95_0_125_(vm, NULL);
}

int main() {
    // Init print
    if (pdFAIL == printInit(0)) {
        uartLog("Init print failed\r\n");
        halt();
    }

    // Create root thread
    if (pdPASS != xTaskCreate(vRootThread, "root", 2000, NULL, 0, NULL)) {
        uartLog("Failed to create root thread\r\n");
        halt();
    }

    // Start the FreeRTOS scheduler
    vTaskStartScheduler();

    // Will not get here unless there is insufficient RAM
    uartLog("will not get here\r\n");
    return EXIT_SUCCESS;
}
