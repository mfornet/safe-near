/* Test-harness shim for sandboxes whose hard RLIMIT_NOFILE is below neard's 65535 start-up requirement.
 * neard only checks the limit; a localnet needs a few hundred descriptors.  Preloaded by localnet.py. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <sys/resource.h>

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
