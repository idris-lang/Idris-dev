// C-Side of the Idris network library
// (C) Simon Fowler, 2014
// MIT Licensed. Have fun!
#include "idris_net.h"
#include <errno.h>
#include <netdb.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

void buf_htonl(void* buf, int len) {
    int* buf_i = (int*) buf;
    int i;
    for (i = 0; i < (len / sizeof(int)) + 1; i++) {
        buf_i[i] = htonl(buf_i[i]);
    }
}

void buf_ntohl(void* buf, int len) {
    int* buf_i = (int*) buf;
    int i;
    for (i = 0; i < (len / sizeof(int)) + 1; i++) {
        buf_i[i] = ntohl(buf_i[i]);
    }
}

void* idrnet_malloc(int size) {
    return malloc(size);
}

void idrnet_free(void* ptr) {
    free(ptr);
}

// We call this from quite a few functions. Given a textual host and an int port,
// populates a struct addrinfo.
int idrnet_getaddrinfo(struct addrinfo** address_res, char* host, int port,
                       int family, int socket_type) {

    struct addrinfo hints;
    // Convert port into string
    char str_port[8];
    sprintf(str_port, "%d", port);

    // Set up hints structure
    memset(&hints, 0, sizeof(hints)); // zero out hints
    hints.ai_family = family;
    hints.ai_socktype = socket_type;

    // If the length of the hostname is 0 (i.e, it was set to Nothing in Idris)
    // then we want to instruct the C library to fill in the IP automatically
    if (strlen(host) == 0) {
        hints.ai_flags = AI_PASSIVE; // fill in IP automatically
        return getaddrinfo(NULL, str_port, &hints, address_res);
    }
    return getaddrinfo(host, str_port, &hints, address_res);

}

int idrnet_bind(int sockfd, int family, int socket_type, char* host, int port) {
    struct addrinfo* address_res;
    int addr_res = idrnet_getaddrinfo(&address_res, host, port, family, socket_type);
    if (addr_res == -1) {
        //printf("Lib err: bind getaddrinfo\n");
        return -1;
    }

    int bind_res = bind(sockfd, address_res->ai_addr, address_res->ai_addrlen);
    if (bind_res == -1) {
        //freeaddrinfo(address_res);
        //printf("Lib err: bind\n");
        return -1;
    }
    return 0;
}

int idrnet_connect(int sockfd, int family, int socket_type, char* host, int port) {
    struct addrinfo* remote_host;
    int addr_res = idrnet_getaddrinfo(&remote_host, host, port, family, socket_type);
    if (addr_res == -1) {
        return -1;
    }

    int connect_res = connect(sockfd, remote_host->ai_addr, remote_host->ai_addrlen);
    if (connect_res == -1) {
        freeaddrinfo(remote_host);
        return -1;
    }
    freeaddrinfo(remote_host);
    return 0;
}


int idrnet_sockaddr_family(void* sockaddr) {
    struct sockaddr* addr = (struct sockaddr*) sockaddr;
    return (int) addr->sa_family;
}

char* idrnet_sockaddr_ipv4(void* sockaddr) {
    struct sockaddr_in* addr = (struct sockaddr_in*) sockaddr;
    char* ip_addr = (char*) malloc(sizeof(char) * INET_ADDRSTRLEN);
    inet_ntop(AF_INET, &(addr->sin_addr), ip_addr, INET_ADDRSTRLEN);
    //printf("Lib: ip_addr: %s\n", ip_addr);
    return ip_addr;
}

int idrnet_sockaddr_ipv4_port(void* sockaddr) {
    struct sockaddr_in* addr = (struct sockaddr_in*) sockaddr;
    return ((int) ntohs(addr->sin_port));
}

void* idrnet_create_sockaddr() {
    return malloc(sizeof(struct sockaddr_storage));
}


int idrnet_accept(int sockfd, void* sockaddr) {
    struct sockaddr* addr = (struct sockaddr*) sockaddr;
    socklen_t addr_size = 0;
    return accept(sockfd, addr, &addr_size);
}

int idrnet_send(int sockfd, char* data) {
    int len = strlen(data); // For now.
    return send(sockfd, (void*) data, len, 0);
}

int idrnet_send_buf(int sockfd, void* data, int len) {
    void* buf_cpy = malloc(len);
    memset(buf_cpy, 0, len);
    memcpy(buf_cpy, data, len);
    buf_htonl(buf_cpy, len);
    int res = send(sockfd, buf_cpy, len, 0);
    free(buf_cpy);
    return res;
}

void* idrnet_recv(int sockfd, int len) {
    idrnet_recv_result* res_struct =
        (idrnet_recv_result*) malloc(sizeof(idrnet_recv_result));
    char* buf = malloc(len + 1);
    memset(buf, 0, len + 1);
    int recv_res = recv(sockfd, buf, len, 0);
    res_struct->result = recv_res;

    if (recv_res > 0) { // Data was received
        buf[recv_res + 1] = 0x00; // Null-term, so Idris can interpret it
    }
    res_struct->payload = buf;
    return (void*) res_struct;
}

int idrnet_recv_buf(int sockfd, void* buf, int len) {
    int recv_res = recv(sockfd, buf, len, 0);
    if (recv_res != -1) {
        buf_ntohl(buf, len);
    }
    return recv_res;
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


int idrnet_sendto(int sockfd, char* data, char* host, int port, int family) {

    struct addrinfo* remote_host;
    int addr_res = idrnet_getaddrinfo(&remote_host, host, port, family, SOCK_DGRAM);
    if (addr_res == -1) {
        return -1;
    }

    int send_res = sendto(sockfd, data, strlen(data), 0,
                        remote_host->ai_addr, remote_host->ai_addrlen);
    freeaddrinfo(remote_host);
    return send_res;
}

int idrnet_sendto_buf(int sockfd, void* buf, int buf_len, char* host, int port, int family) {

    struct addrinfo* remote_host;
    int addr_res = idrnet_getaddrinfo(&remote_host, host, port, family, SOCK_DGRAM);
    if (addr_res == -1) {
        //printf("lib err: sendto getaddrinfo \n");
        return -1;
    }

    buf_htonl(buf, buf_len);

    int send_res = sendto(sockfd, buf, buf_len, 0,
                        remote_host->ai_addr, remote_host->ai_addrlen);
    if (send_res == -1) {
        perror("lib err: sendto \n");
    }
    //freeaddrinfo(remote_host);
    return send_res;
}



void* idrnet_recvfrom(int sockfd, int len) {
/*
 * int recvfrom(int sockfd, void *buf, int len, unsigned int flags,
             struct sockaddr *from, int *fromlen);
*/
    // Allocate the required structures, and nuke them
    struct sockaddr_storage* remote_addr =
        (struct sockaddr_storage*) malloc(sizeof(struct sockaddr_storage));
    char* buf = (char*) malloc(len + 1);
    idrnet_recvfrom_result* ret =
        (idrnet_recvfrom_result*) malloc(sizeof(idrnet_recvfrom_result));
    memset(remote_addr, 0, sizeof(struct sockaddr_storage));
    memset(buf, 0, len + 1);
    memset(ret, 0, sizeof(idrnet_recvfrom_result));
    socklen_t fromlen = sizeof(struct sockaddr_storage);

    int recv_res = recvfrom(sockfd, buf, len, 0, (struct sockaddr*) remote_addr, &fromlen);
    ret->result = recv_res;
    // Check for failure...
    if (recv_res == -1) {
        free(buf);
        free(remote_addr);
    } else {
        // If data was received, process and populate
        ret->result = recv_res;
        ret->remote_addr = remote_addr;
        // Ensure the last byte is NULL, since in this mode we're sending strings
        buf[len] = 0x00;
        ret->payload = (void*) buf;
    }

    return ret;
}

void* idrnet_recvfrom_buf(int sockfd, void* buf, int len) {
    // Allocate the required structures, and nuke them
    struct sockaddr_storage* remote_addr =
        (struct sockaddr_storage*) malloc(sizeof(struct sockaddr_storage));
    idrnet_recvfrom_result* ret =
        (idrnet_recvfrom_result*) malloc(sizeof(idrnet_recvfrom_result));
    memset(remote_addr, 0, sizeof(struct sockaddr_storage));
    memset(ret, 0, sizeof(idrnet_recvfrom_result));
    socklen_t fromlen = 0;

    int recv_res = recvfrom(sockfd, buf, len, 0, (struct sockaddr*) remote_addr, &fromlen);
    // Check for failure... But don't free the buffer! Not our job.
    ret->result = recv_res;
    if (recv_res == -1) {
        free(remote_addr);
    }
    // Payload will be NULL -- since it's been put into the user-specified buffer. We
    // still need the return struct to get our hands on the remote address, though.
    if (recv_res > 0) {
        buf_ntohl(buf, len);
        ret->payload = NULL;
        ret->remote_addr = remote_addr;
    }
    return ret;
}

int idrnet_get_recvfrom_res(void* res_struct) {
    return (((idrnet_recvfrom_result*) res_struct)->result);
}

char* idrnet_get_recvfrom_payload(void* res_struct) {
    return (((idrnet_recvfrom_result*) res_struct)->payload);
}

void* idrnet_get_recvfrom_sockaddr(void* res_struct) {
    idrnet_recvfrom_result* recv_struct = (idrnet_recvfrom_result*) res_struct;
    return recv_struct->remote_addr;
}

int idrnet_get_recvfrom_port(void* res_struct) {
    idrnet_recvfrom_result* recv_struct = (idrnet_recvfrom_result*) res_struct;
    if (recv_struct->remote_addr != NULL) {
        struct sockaddr_in* remote_addr_in =
            (struct sockaddr_in*) recv_struct->remote_addr;
        return ((int) ntohs(remote_addr_in->sin_port));
    }
    return -1;
}

void idrnet_free_recvfrom_struct(void* res_struct) {
    idrnet_recvfrom_result* recv_struct = (idrnet_recvfrom_result*) res_struct;
    if (recv_struct != NULL) {
        if (recv_struct->payload != NULL) {
            free(recv_struct->payload);
        }
        if (recv_struct->remote_addr != NULL) {
            free(recv_struct->remote_addr);
        }
    }
}

int idrnet_geteagain() {
    return EAGAIN;
}

