#include "common.h"
#include "signal.h"

char* ident =
    "$Header: /hosts/bonnie/proj/irix6.4-ssg/isms/cmplrs/targucode/cfe/RCS/os.c,v 1.2 1992/08/12 21:07:39 wsj Exp $";

static int D_1001D864[] = { -1, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41,
                            42, 43, 44, 45, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59 };

void report_crash(int signo) {
    if (signo >= 1 && signo < NSIG) {
        error(D_1001D864[signo], LEVEL_FATAL, -1, infile);
    } else {
        error(0x40002, LEVEL_FATAL, -1, signo, infile);
    }
}

void catchall(void) {
    int signo;

    signal(SIGHUP, SIG_IGN);

    for (signo = SIGINT; signo < NSIG; signo++) {
        if (signo != SIGTSTP && signo != SIGCONT && signo != SIGWINCH && signo != SIGCHLD &&
            signal(signo, report_crash) == SIG_IGN) {
            signal(signo, SIG_IGN);
        }
    }
}
