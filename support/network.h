#include <stdio.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <string.h>
#include <closure.h>

typedef struct {
    int sock;
    struct sockaddr_in addr;
} Connection;

typedef struct {
    unsigned port;
    char* buf;
    char* server;
} Recv;

int netTest(char* strTest, int num);
void* net_UDP_serverSocket(int port);
void* net_UDP_clientSocket(char* server, int port);

int nullPtr(void *ptr);

int net_sendUDP(void* conn, char* server, int port, char* stuff);
void* net_recvUDP(void* conn);

char* get_recvBuf(void* recv);
char* get_recvServer(void* recv);
int get_recvPort(void* recv);

void net_sendRaw(void* conn, char* server, int port, VAL pkt);
VAL net_recvRaw(void* conn);
void dumpPkt(VAL pkt);
