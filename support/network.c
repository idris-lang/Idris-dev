#include <stdio.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <string.h>
#include <fcntl.h>
#include <errno.h>
#include <closure.h>

#include "network.h"

int isReadable(int sd, int timeOut) { // milliseconds
    fd_set socketReadSet;
    FD_ZERO(&socketReadSet);
    FD_SET(sd,&socketReadSet);
    struct timeval tv;
    if (timeOut) {
	tv.tv_sec  = timeOut / 1000;
	tv.tv_usec = (timeOut % 1000) * 1000;
    } else {
	tv.tv_sec  = 0;
	tv.tv_usec = 0;
    } // if
    if (select(sd+1,&socketReadSet,0,0,&tv) == -1) {
	printf("READ ERROR!\n");
	return 0;
    } // if
    return FD_ISSET(sd,&socketReadSet) != 0;
} /* isReadable */

void* net_UDP_clientSocket(char* server, int port) {
    srand(12345); //time(NULL));

    Connection* con = (Connection*)EMALLOC(sizeof(Connection));
    int s;
    struct sockaddr_in si_me, si_other;

    if ((s=socket(AF_INET, SOCK_DGRAM, 0))==-1) {
	printf("FAIL 1\n");
	return NULL;
    }

    memset((char *) &si_other, 0, sizeof(si_other));
    si_other.sin_family = AF_INET;
    si_other.sin_port = htons(port);

    if (inet_aton(server, &si_other.sin_addr)==0) {
	printf("FAIL 2\n");
	return NULL;
    }

    // Bind, so we can receive replies.
    si_me.sin_family = AF_INET;
    si_me.sin_port = htons(0);
    si_me.sin_addr.s_addr = htonl(INADDR_ANY);

    if (bind(s, (struct sockaddr*)&si_me, sizeof(si_me))<0) {
	return NULL;
    }

    con->sock = s;
    con->addr = si_other;

//    printf("Opened client socket %d\n", s);
    return con;
}

void* net_UDP_serverSocket(int port) {
    srand(time(NULL));

    Connection* con = (Connection*)EMALLOC(sizeof(Connection));
    int s;
    struct sockaddr_in si_me;

    if ((s=socket(AF_INET, SOCK_DGRAM, 0))==-1) {
	return NULL;
    }

    memset((char *) &si_me, 0, sizeof(si_me));
    si_me.sin_family = AF_INET;
    si_me.sin_port = htons(port);
    si_me.sin_addr.s_addr = htonl(INADDR_ANY);
    if (bind(s, (struct sockaddr*)&si_me, sizeof(si_me))==-1) {
	return NULL;
    }

    con->sock = s;
    con->addr = si_me;

//    printf("Opened server socket %d\n", s);
    return con;
}

int net_sendUDP(void* conn, char* server, int port, char* stuff) {
//    printf("Socket is %d\n", conn);
    if (0) { //rand()%50000 == 0) {
	printf("DROP\n");
	return 0;
    }


    Connection* c = (Connection*)conn;
    int s = c->sock;
    struct sockaddr_in other = c->addr;
    memset((char *) &other, 0, sizeof(other));
    other.sin_family = AF_INET;
    other.sin_port = htons(port);
    if (inet_aton(server, &other.sin_addr)==0) {
	printf("FAIL 3\n");
	return -1;
    }

    if (sendto(s, stuff, strlen(stuff), 0, (struct sockaddr*)&other, 
	       sizeof(other))==-1) {
	printf("Send FAIL\n");
	return -1;
    }
//    printf("Send WIN, to %s %d %d\n", inet_ntoa(other.sin_addr),
//	   ntohs(other.sin_port), port);
    return 0;
}

void* net_recvUDP(void* conn) {
    struct sockaddr_in other;
    Connection* c = (Connection*)conn;
    int s = c->sock;
    socklen_t slen = sizeof(other);
    struct sockaddr_in me = c->addr;

    // TMP HACK: 512 should be enough for the purposes of this experiment...
    // Do it properly some time.
    char* buf = (char*)EMALLOC(512*sizeof(char));

//    printf("Waiting to receive\n");

    int error;
//    while (!isReadable(s,100)) printf(".");

    if (!isReadable(s, 1000)) {
	printf("Nothing\n");
	return NULL;
    }

    if (recvfrom(s, buf, 512, 0, (struct sockaddr *)&other, &slen)==-1) { 
	printf("Nothing\n");
	return NULL;
    } 

/*    printf("Received %s from %s:UDP%u\n", 
	   buf,inet_ntoa(other.sin_addr),
	   ntohs(other.sin_port));
*/
    // return a structure with the received value, and where it came from.
    Recv* r = (Recv*)EMALLOC(sizeof(Recv));
    r->buf = buf;
    r->server = inet_ntoa(other.sin_addr);
    r->port = ntohs(other.sin_port);

    return (void*)r;
}

char* get_recvBuf(void* recv) {
    return ((Recv*)recv)->buf;
}

char* get_recvServer(void* recv) {
    return ((Recv*)recv)->server;
}

int get_recvPort(void* recv) {
    return ((Recv*)recv)->port;
}

int nullPtr(void *ptr) {
    return ptr==NULL;
}

// Just to see if the idris FFI is working, and happily talking to .o files...
int netTest(char* strTest, int num) {
    int i;
    for(i=0;i<num;++i) {
	printf("%s\n",strTest);
    }

    return i;
}

void net_sendRaw(void* conn, char* server, int port, VAL pkt)
{
    int seq = GETINT(PROJECT(pkt, 0));
    VAL ty = PROJECT(pkt, 1);
    int pty;

    switch(TAG(ty)) {
    case 0:
	pty = 0;
	break;
    case 1:
	pty = 1;
	break;
    case 2:
	pty = TAG(PROJECT(ty,0)) + 2;
    }

    char* buf = (char*)EMALLOC(512*sizeof(char));
    sprintf(buf, "%d %d", seq, pty);

    net_sendUDP(conn, server, port, buf);
}

VAL net_recvRaw(void* conn)
{
    int seq, pty;

    void* dat = net_recvUDP(conn);
    if (dat==NULL) {
	return CONSTRUCTOR(1,0,NULL); // Nothing
    }
    else {
	char* recvBuf = get_recvBuf(dat);

	sscanf(recvBuf, "%d %d", &seq, &pty); 
	VAL ptyc = NULL;
	if (pty<2) {
	    ptyc = CONSTRUCTOR(pty,0,NULL);
	} else {
	    ptyc = CONSTRUCTOR1(2, CONSTRUCTOR(pty-2,0,NULL));
	}
	VAL pkt = CONSTRUCTOR2(0, MKINT(seq), ptyc);
	printf("Received %d %d\n", seq, pty);
	
	VAL recvpkt = CONSTRUCTOR3(0, pkt, MKSTR(get_recvServer(dat)),
				   MKINT(get_recvPort(dat)));

	return CONSTRUCTOR1(0, recvpkt); // Just pkt
    }
    
}

void dumpPkt(VAL pkt)
{
    int seq = GETINT(PROJECT(pkt, 0));
    VAL ty = PROJECT(pkt, 1);
    int pty;

    switch(TAG(ty)) {
    case 0:
	pty = 0;
	break;
    case 1:
	pty = 1;
	break;
    case 2:
	pty = TAG(PROJECT(ty,0)) + 2;
    }

    printf("%d %d\n", seq, pty);
}
