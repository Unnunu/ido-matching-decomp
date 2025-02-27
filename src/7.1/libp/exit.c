#include "pascalio.h"
#include <sys/prctl.h>

// TODO: include rld_interface.h
extern void *_rld_new_interface(int operation, ...);
#define _SHUT_DOWN              0 
extern void	_exithandle(void);
extern void	_cleanup(void);
extern void	_DYNAMIC_LINK();

void
exit (code)
     int code;
{
    /* Delete /tmp files. */
    register unsigned i;
    for (i = _libp_pascal_file_counter; i != 0; i-= 1) {
        unsigned char namebuf[TMP_LENGTH];
        unsigned char *name = namebuf;
        sprintf (name, TMP_FILE, i, getpid());
        unlink (name);
    }

    if (prctl(PR_GETNSHARE) <= 1) {
        /* ANSI - call functions registered with atexit() */
		_exithandle();
		if (_DYNAMIC_LINK != 0) _rld_new_interface(_SHUT_DOWN);
    }

    _cleanup();
    _exit(code);
}