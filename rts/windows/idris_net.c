// C-Side of the Idris network library
// (C) Simon Fowler, 2014
// MIT Licensed. Have fun!
#include "../idris_net.h"

#include <errno.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <Winsock2.h>
#include <Ws2tcpip.h>


// inet_ntop isn't defined in the old mingw delivered with GHC,
// so put the prototype here, cribbed from a newer version of it
WINSOCK_API_LINKAGE LPCSTR WSAAPI InetNtopA(INT Family, PVOID pAddr,
        LPSTR pStringBuf, size_t StringBufSize);

static int socket_inited = 0;
static WSADATA wsa_data;

void* idrnet_malloc(int size) {
    return malloc(size);
}

void idrnet_free(void* ptr) {
    free(ptr);
}

static void clean_sockets(void) {
    WSACleanup();
}

static int check_init(void)
{
    if (!socket_inited) {
        int result = WSAStartup(MAKEWORD(2, 2), &wsa_data);
        if (result == NO_ERROR) {
            socket_inited = 1;
            atexit(clean_sockets);
        }
    }
    return socket_inited;
}

int idrnet_bind(int sockfd, int family, int socket_type, char* host, int port) {
    struct addrinfo hints;
    struct addrinfo* address_res;
    // Convert port into string
    char str_port[8];
    sprintf(str_port, "%d", port);

    if (!check_init()) {
        return -1;
    }
    // Set up hints structure
    memset(&hints, 0, sizeof(hints)); // zero out hints
    hints.ai_family = family;
    hints.ai_socktype = socket_type;

    // If the length of the hostname is 0 (i.e, it was set to Nothing in Idris)
    // then we want to instruct the C library to fill in the IP automatically
    if (strlen(host) == 0) {
        hints.ai_flags = AI_PASSIVE; // fill in IP automatically
    }

    int addr_res = getaddrinfo(host, str_port, &hints, &address_res);
    if (addr_res == -1) {
        return -1;
    }

    int bind_res = bind(sockfd, address_res->ai_addr, address_res->ai_addrlen);
    if (bind_res == -1) {
        return -1;
    }

    return 0;
}

int idrnet_connect(int sockfd, int family, int socket_type, char* host, int port) {
    char str_port[8];
    sprintf(str_port, "%d", port);
    struct addrinfo hints;
    struct addrinfo* remote_host;

    if (!check_init()) {
        return -1;
    }
    // Set up hints structure for getaddrinfo
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = family;
    hints.ai_socktype = socket_type;

    // Get info about the remote host (DNS lookup etc)
    int addr_res = getaddrinfo(host, str_port, &hints, &remote_host);
    if (addr_res == -1) {
        return -1;
    }

    int connect_res = connect(sockfd, remote_host->ai_addr, remote_host->ai_addrlen);
    if (connect_res == -1) {
        return -1;
    }

    return 0;
}


int idrnet_sockaddr_family(void* sockaddr) {
    struct sockaddr* addr = (struct sockaddr*) sockaddr;
    return (int) addr->sa_family;
}

char* idrnet_sockaddr_ipv4(void* sockaddr) {
    struct sockaddr_in* addr = (struct sockaddr_in*) sockaddr;
    char* ip_addr = (char*) malloc(sizeof(char) * INET_ADDRSTRLEN);
    InetNtopA(AF_INET, &(addr->sin_addr), ip_addr, INET_ADDRSTRLEN);
    return ip_addr;
}

void* idrnet_create_sockaddr() {
    return malloc(sizeof(struct sockaddr_storage));
}


int idrnet_accept(int sockfd, void* sockaddr) {
    struct sockaddr* addr = (struct sockaddr*) sockaddr;
    socklen_t addr_size = 0;
    if (!check_init()) {
        return -1;
    }
    return accept(sockfd, addr, &addr_size);
}

int idrnet_send(int sockfd, char* data) {
    int len = strlen(data); // For now.
    if (!check_init()) {
        return -1;
    }
    return send(sockfd, (void*) data, len, 0);
}

int idrnet_send_buf(int sockfd, void* data, int len) {
    if (!check_init()) {
        return -1;
    }
    return send(sockfd, data, len, 0);
}

void* idrnet_recv(int sockfd, int len) {
    if (!check_init()) {
        return NULL;
    }
    idrnet_recv_result* res_struct =
        (idrnet_recv_result*) malloc(sizeof(idrnet_recv_result));

    char* buf = malloc(len + 1);
    int recv_res = recv(sockfd, buf, len, 0);
    res_struct->result = recv_res;

    if (recv_res > 0) { // Data was received
        buf[recv_res + 1] = 0x00; // Null-term, so Idris can interpret it
    }
    res_struct->payload = (void*) buf;
    return (void*) res_struct;
}

int idrnet_recv_buf(int sockfd, void* buf, int len) {
    if (!check_init()) {
        return -1;
    }
    return recv(sockfd, buf, len, 0);
}

int idrnet_get_recv_res(void* res_struct) {
    return (((idrnet_recv_result*) res_struct)->result);
}

char* idrnet_get_recv_payload(void* res_struct) {
    return (((idrnet_recv_result*) res_struct)->payload);
}

void idrnet_free_recv_struct(void* res_struct) {
    idrnet_recv_result* i_res_struct =
        (idrnet_recv_result*) res_struct;
    if (i_res_struct->payload != NULL) {
        free(i_res_struct->payload);
    }
    free(res_struct);
}

int idrnet_errno() {
    return errno;
}

int idrnet_geteagain() {
    return EAGAIN;
}

