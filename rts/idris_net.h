#ifndef IDRISNET_H
#define IDRISNET_H

struct sockaddr_storage;
struct addrinfo;

typedef struct idrnet_recv_result {
    int result;
    void* payload;
} idrnet_recv_result;

// Same type of thing as idrnet_recv_result, but for UDP, so stores some 
// address information
typedef struct idrnet_recvfrom_result {
    int result;
    void* payload;
    struct sockaddr_storage* remote_addr;
} idrnet_recvfrom_result;

// Memory management functions
void* idrnet_malloc(int size);
void idrnet_free(void* ptr);

// Gets value of errno
int idrnet_errno(); 

// Bind
int idrnet_bind(int sockfd, int family, int socket_type, char* host, int port);

// Connect
int idrnet_connect(int sockfd, int family, int socket_type, char* host, int port);

// Accessor functions for struct_sockaddr
int idrnet_sockaddr_family(void* sockaddr);
char* idrnet_sockaddr_ipv4(void* sockaddr);
int idrnet_sockaddr_ipv4_port(void* sockaddr);
void* idrnet_create_sockaddr();

// Accept
int idrnet_accept(int sockfd, void* sockaddr);

// Send
int idrnet_send(int sockfd, char* data);
int idrnet_send_buf(int sockfd, void* data, int len);

// Receive
// Creates a result structure containing result and payload
void* idrnet_recv(int sockfd, int len);
// Receives directly into a buffer
int idrnet_recv_buf(int sockfd, void* buf, int len);

// UDP Send
int idrnet_sendto(int sockfd, char* data, char* host, int port, int family);
int idrnet_sendto_buf(int sockfd, void* buf, int buf_len, char* host, int port, int family);


// UDP Receive
void* idrnet_recvfrom(int sockfd, int len);
void* idrnet_recvfrom_buf(int sockfd, void* buf, int len);

// Receive structure accessors
int idrnet_get_recv_res(void* res_struct);
char* idrnet_get_recv_payload(void* res_struct);
void idrnet_free_recv_struct(void* res_struct);

// Recvfrom structure accessors
int idrnet_get_recvfrom_res(void* res_struct);
char* idrnet_get_recvfrom_payload(void* res_struct);
void* idrnet_get_recvfrom_sockaddr(void* res_struct);
void idrnet_free_recvfrom_struct(void* res_struct);


int idrnet_getaddrinfo(struct addrinfo** address_res, char* host, 
    int port, int family, int socket_type);

int idrnet_geteagain();

#endif
