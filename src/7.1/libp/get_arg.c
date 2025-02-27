extern unsigned __Argc;
extern unsigned char **__Argv;

void get_arg(i, s, l)
     register unsigned i;
     register unsigned char *s;
     register unsigned l;
{
    register unsigned char *e = s + l;
    if (i < __Argc) {
	register unsigned char *p = __Argv[i];
	register unsigned c;
	while (s != e && (c = *p++) != '\0') {
	    *s++ = c;
	}
    }
    while (s != e) {
	*s++ = ' ';
    }
}