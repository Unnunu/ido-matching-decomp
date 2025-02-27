#include "pascalio.h"
#define L_SET 0

extern void _getbuf(register FILE *iop, register unsigned rsize);

void
rewrite (fref, name, namelength, size)
     register struct pascal_file *fref;
     register unsigned char *name;
     register unsigned namelength;
     register unsigned size;	/* Zero for text file, else record size */
{
    register FILE *f;
    register unsigned char *n;

    f = fref->stdiofile;
    while (namelength != 0 && name[namelength-1] == ' ') namelength -= 1;
    if (namelength != 0) {
	/* Remember supplied name for reset/rewrite with no name. */
	n = malloc(namelength+1);
	memcpy (n, name, namelength);
	n[namelength] = '\0';
	fref->name = n;
    }
    else {
        n = fref->name;
	if (n == NULL) {
	    /* No name, and no previous name.  Use a file in /tmp. */
	    if (f != NULL) {
		fseek (f, 0, L_SET);
		return;
	    }
	    n = malloc(TMP_LENGTH);
	    _libp_pascal_file_counter += 1;
	    sprintf(n, TMP_FILE, _libp_pascal_file_counter, getpid());
	    fref->name = n;
	}
    }
    if (f != NULL) {
	    f = freopen(n, "w", f);
        if (f == NULL) {
            fprintf(stderr, "Permission Denied, rewrite to a protected file\n");
            exit(13);
        }
    } else {
	    f = fopen(n, "w");
    }
    if (f != NULL) {
	if (f->_base == NULL) {
	    _getbuf (f, size != 0 ? size : 1);
	}
    }
    fref->stdiofile = f;
}