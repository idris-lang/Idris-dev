#include "idris_rts.h"
#include "idris_buffer.h"

typedef struct {
    int size;
    uint8_t data[0];
} Buffer;

void* idris_newBuffer(int bytes) {
    Buffer* buf = malloc(sizeof(Buffer) + bytes*sizeof(uint8_t));
    if (buf == NULL) {
        return NULL;
    }

    buf->size = bytes;
    memset(buf->data, 0, bytes);

    return buf;
}

void idris_copyBuffer(void* from, int start, int len,
                      void* to, int loc) {
    Buffer* bfrom = from;
    Buffer* bto = to;

    if (loc >= 0 && loc+len <= bto->size) {
        memcpy(bto->data + loc, bfrom->data + start, len);
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

void idris_setBufferInt(void* buffer, int loc, int val) {
    Buffer* b = buffer;
    if (loc >= 0 && loc+3 < b->size) {
        b->data[loc] = val & 0xff;
        b->data[loc+1] = (val >> 8) & 0xff;
        b->data[loc+2] = (val >> 16) & 0xff;
        b->data[loc+3] = (val >> 24) & 0xff;
    }
}

void idris_setBufferDouble(void* buffer, int loc, double val) {
    Buffer* b = buffer;
    // I am not proud of this
    if (loc >= 0 && loc + sizeof(double) <= b->size) {
        unsigned char* c = (unsigned char*)(& val);
        int i;
        for (i = 0; i < sizeof(double); ++i) {
            b->data[loc+i] = c[i];
        }
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

int idris_getBufferInt(void* buffer, int loc) {
    Buffer* b = buffer;
    if (loc >= 0 && loc+3 < b->size) {
        return b->data[loc] +
               (b->data[loc+1] << 8) +
               (b->data[loc+2] << 16) +
               (b->data[loc+3] << 24);
    } else {
        return 0;
    }
}

double idris_getBufferDouble(void* buffer, int loc) {
    Buffer* b = buffer;
    double d;
    // I am even less proud of this
    unsigned char *c = (unsigned char*)(& d);
    if (loc >= 0 && loc + sizeof(double) <= b->size) {
        int i;
        for (i = 0; i < sizeof(double); ++i) {
            c[i] = b->data[loc+i];
        }
        return d;
    }
    else {
        return 0;
    }
}

VAL idris_getBufferString(void* buffer, int loc, int len) {
    Buffer* b = buffer;
    char * s = (char*)(b->data + loc);
    size_t sz = loc >= 0 && loc+len <= b->size? len : 0;
    return MKSTRlen(get_vm(), s, sz);
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
