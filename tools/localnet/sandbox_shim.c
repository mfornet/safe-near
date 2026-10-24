/* Test-harness shim for restricted sandboxes, preloaded by localnet.py (and nothing else).
 *
 * 1. neard refuses to start when the hard RLIMIT_NOFILE is below 65535.  It only checks the limit; a
 *    localnet needs a few hundred descriptors, so getrlimit reports the required value.
 * 2. `neard localnet` reserves its ports by binding IPv6 loopback sockets, which kernels without IPv6
 *    reject.  Those sockets are bound to the same port on 127.0.0.1 instead; localnet.py rewrites every
 *    generated address to IPv4 afterwards. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <string.h>

#define REQUIRED 65535

static int (*real_get)(__rlimit_resource_t, struct rlimit *);
static int (*real_get64)(__rlimit_resource_t, struct rlimit64 *);

int getrlimit(__rlimit_resource_t resource, struct rlimit *limit) {
    if (!real_get) real_get = dlsym(RTLD_NEXT, "getrlimit");
    int result = real_get(resource, limit);
    if (result == 0 && resource == RLIMIT_NOFILE) {
        if (limit->rlim_cur < REQUIRED) limit->rlim_cur = REQUIRED;
        if (limit->rlim_max < REQUIRED) limit->rlim_max = REQUIRED;
    }
    return result;
}

int getrlimit64(__rlimit_resource_t resource, struct rlimit64 *limit) {
    if (!real_get64) real_get64 = dlsym(RTLD_NEXT, "getrlimit64");
    int result = real_get64(resource, limit);
    if (result == 0 && resource == RLIMIT_NOFILE) {
        if (limit->rlim_cur < REQUIRED) limit->rlim_cur = REQUIRED;
        if (limit->rlim_max < REQUIRED) limit->rlim_max = REQUIRED;
    }
    return result;
}

static int ipv6_missing(void) {
    static int cached = -1;
    if (cached < 0) {
        int (*real_socket)(int, int, int) = dlsym(RTLD_NEXT, "socket");
        int fd = real_socket(AF_INET6, SOCK_STREAM, 0);
        cached = fd < 0;
        if (fd >= 0) close(fd);
    }
    return cached;
}

int socket(int domain, int type, int protocol) {
    int (*real_socket)(int, int, int) = dlsym(RTLD_NEXT, "socket");
    if (domain == AF_INET6 && ipv6_missing()) domain = AF_INET;
    return real_socket(domain, type, protocol);
}

int bind(int fd, const struct sockaddr *address, socklen_t length) {
    int (*real_bind)(int, const struct sockaddr *, socklen_t) = dlsym(RTLD_NEXT, "bind");
    if (address->sa_family == AF_INET6 && ipv6_missing()) {
        const struct sockaddr_in6 *six = (const struct sockaddr_in6 *)address;
        struct sockaddr_in four;
        memset(&four, 0, sizeof four);
        four.sin_family = AF_INET;
        four.sin_port = six->sin6_port;
        four.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
        return real_bind(fd, (const struct sockaddr *)&four, sizeof four);
    }
    return real_bind(fd, address, length);
}
