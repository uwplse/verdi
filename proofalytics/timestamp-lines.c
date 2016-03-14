#include <stdlib.h>
#include <stdio.h>
#include <time.h>

// OS X does not have clock_gettime, use clock_get_time
#ifdef __MACH__
#include <mach/clock.h>
#include <mach/mach.h>
#endif

int
main() {
#ifdef __MACH__
  clock_serv_t cclock;
  mach_timespec_t mts;
  host_get_clock_service(mach_host_self(), SYSTEM_CLOCK, &cclock);
#endif
  struct timespec ts;
  char *line = NULL;
  size_t cap = 0;
  size_t len = 0;
  while((len = getline(&line, &cap, stdin)) != -1) {
#ifdef __MACH__
    clock_get_time(cclock, &mts); \
    ts.tv_sec = mts.tv_sec; \
    ts.tv_nsec = mts.tv_nsec;
#else
    clock_gettime(CLOCK_REALTIME, &ts);
#endif
    printf("%20f ", ts.tv_sec * 1.0e9 + ts.tv_nsec);
    fwrite(line, len, 1, stdout);
  }
#ifdef __MACH__
  mach_port_deallocate(mach_task_self(), cclock);
#endif
  return 0;
}
