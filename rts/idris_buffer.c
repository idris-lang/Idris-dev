#include "idris_rts.h"
#include "idris_buffer.h"

typedef struct {
    int size;
    uint8_t* data;
} Buffer;

void* idris_newBuffer(int bytes) {
    Buffer* buf = malloc(sizeof(Buffer) + bytes*sizeof(uint8_t));
    if (buf == NULL) {
        return NULL;
    }

    buf->size = bytes;
    buf->data = (uint8_t*)(buf+1);
    memset(buf->data, 0, bytes);

    return buf;
}

void idris_copyBuffer(void* from, int start, int len,
                      void* to, int loc) {
    Buffer* bfrom = from;
    Buffer* bto = to;

    if (loc >= 0 && loc+len <= bto->size) {
        memcpy((bto->data)+loc, (bfrom->data)+start, len);
    }
}

int idris_getBufferSize(void* buffer) {
    return ((Buffer*)buffer)->size;
}

void idris_setBufferByte(void* buffer, int loc, uint8_t byte) {
    Buffer* b = buffer;
    if (loc >= 0 && loc < b->size) {
        b->data[loc] = byte;
    }
}

void idris_setBufferString(void* buffer, int loc, char* str) {
    Buffer* b = buffer;
    int len = strlen(str);

    if (loc >= 0 && loc+len <= b->size) {
        memcpy((b->data)+loc, str, len);
    }
}

uint8_t idris_getBufferByte(void* buffer, int loc) {
    Buffer* b = buffer;
    if (loc >= 0 && loc < b->size) {
        return b->data[loc];
    } else {
        return 0;
    }
}

int idris_readBuffer(FILE* h, void* buffer, int loc, int max) {
    Buffer* b = buffer;
    size_t len;

    if (loc >= 0 && loc < b->size) {
        if (loc + max > b->size) {
            max = b->size - loc;
        }
        len = fread((b->data)+loc, sizeof(uint8_t), (size_t)max, h);
        return len;
    } else {
        return 0;
    }
}

void idris_writeBuffer(FILE* h, void* buffer, int loc, int len) {
    Buffer* b = buffer;

    if (loc >= 0 && loc < b->size) {
        if (loc + len > b->size) {
            len = b->size - loc;
        }
        fwrite((b->data)+loc, sizeof(uint8_t), len, h);
    }
}

