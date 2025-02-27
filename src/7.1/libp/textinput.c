/* Pascal text input routines. */

#include "pascalio.h"
extern double ldexp();
extern double _atod();

/* We don't want __filbuf to consume a character, so we go to some difficulty
  to push it back onto the input */
static int ctemp;
#define FEOF(f) (f->_cnt <= 0 && \
  (((ctemp = __filbuf(f)) == EOF) ? 1 : (ungetc(ctemp, f), 0)) \
  )

boolean
eof (f)
     register FILE *f;
{
    return ((f == NULL) || (f->_flag & _IOWRT) || FEOF(f));
}

boolean
eoln (f)
     register FILE *f;
{
    return ((f == NULL) || (f->_flag & _IOWRT) || FEOF(f) || *f->_ptr == '\n');
}

unsigned
peek_char (f)
     register FILE *f;
{
    register unsigned c;

    if (f == NULL || FEOF(f)) return (' ');
    c = *f->_ptr;
    if (c == '\n') c = ' ';
    return (c);
}

void
next_char (f)
     register FILE *f;
{
    if (f != NULL) {
	getc (f);
    }
}

unsigned
read_char (f)
     register FILE *f;
{
    register unsigned c;

    if (f == NULL || (c = getc(f), c == '\n' || c == EOF)) c = ' ';
    return (c);
}


unsigned
read_char_range (f, llimit, hlimit)
     register FILE *f;
     register unsigned llimit, hlimit;
{
    register unsigned c;

    if (f == NULL || (c = getc(f), c == '\n' || c == EOF)) c = ' ';

    if (c < llimit || c > hlimit)
	fprintf(stderr, "Exceeds range in read_char; input is '%c'.\n", c);
    return (c);
}

void
readln (f)
     register FILE *f;
{
    register unsigned c;
    if (f == NULL) {
        fprintf(stderr, "Warning: readln attempted from unopened file.\n");
        return;
    }
    while (c = getc(f), c != '\n' && c != EOF) ;
}

void
read_string (f,cptr,len)
     register FILE *f;
     register unsigned char *cptr;
     register long len;
{
    register unsigned c;
    if (f == NULL) {
        fprintf(stderr, "Warning: read of a string attempted from unopened file.\n");
        *cptr = 0;
        return;
    }
    while (c = getc(f), c != '\n' && c != EOF && len > 0)
      {
      *cptr++ = c;
      len--;
      }
    if (c == '\n') ungetc(c, f);
    while (len > 0)
      {
      *cptr++ = ' ';
      len--;
      }
}

long
read_boolean (f)
     register FILE *f;
{
    register unsigned c;
    unsigned char buffer[129];
    register unsigned char *bptr;

    if (f == NULL) {
        fprintf(stderr, "Warning: read of a boolean attempted from unopened file.\n");
        return 0;
    }

    while (c = getc(f), c == ' ' || c == '\t' || c == '\n') ;

    bptr = buffer;
    while ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) {
	if (c >= 'A' && c <= 'Z') 
	    c = c + 0x20;	/* convert to lower case */
	*bptr++ = c;
	c = getc(f);
    }
    ungetc(c, f);
    *bptr = '\0';

    bptr = buffer;
    if (strcmp(bptr, "false") == 0) return(0);
    if (strcmp(bptr, "true") == 0) return(1);

    fprintf(stderr, "Illegal boolean value '%s'.\n", bptr);
    return(0);
}


long
read_enum (f, z, e, s)
     register FILE *f;
     register unsigned char *s;
     register long z;
     register long e;
{
    register unsigned c;
    unsigned char buffer[129];
    register unsigned char *bptr;
    register unsigned char e1 = e;

    if (f == NULL) {
        fprintf(stderr, "Warning: read of enumerated type attempted from unopened file.\n");
        return 0;
    }

    while (c = getc(f), c == ' ' || c == '\t' || c == '\n') ;

    bptr = buffer;
    while ((c >= 'a' && c <= 'z')
	   || (c >= 'A' && c <= 'Z')
	   || (c >= '0' && c <= '9')
	   || (c == '$')
	   || (c == '_') ) {
	*bptr++ = c;
	c = getc(f);
    }
    ungetc(c, f);
    *bptr = '\0';

    bptr = buffer;
    while (e >= 0) {
	if (strcmp(s, bptr) == 0) return(e1-e);
	while (*s++ != '\0');
    c = ' ';
	if (*s == c) {
	    while (*s++ == c);
	    s--;
	}
	e--;
    }
    fprintf(stderr, "Enumerated value '%s' not within type.\n", bptr);
    return(0);
}

private unsigned char digit_value[128] = {
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
    -1, -1, -1, -1, -1, -1, -1, -1,
     0,  1,  2,  3,  4,  5,  6,  7,
     8,  9, -1, -1, -1, -1, -1, -1,
    -1, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32,
    33, 34, 35, -1, -1, -1, -1, -1,
    -1, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24,
    25, 26, 27, 28, 29, 30, 31, 32,
    33, 34, 35, -1, -1, -1, -1, -1 };

long int
read_integer (f, radix)
     register FILE *f;
     register unsigned radix;
{
    register unsigned long c, sign, i, d;
    register boolean overflow;
#define MAXINT 2147483648

    if (f == NULL) {
        fprintf(stderr, "Warning: read of integer attempted from unopened file.\n");
        return 0;
    }

    while (c = getc(f), c == ' ' || c == '\t' || c == '\n') ;
    sign = c;
    if (sign == '-' || sign == '+') {
	c = getc(f);
    }
    overflow = false;
    if (radix == 10) {
	c -= '0';
	if (c >= 10) {
	    fprintf(stderr, "Digit expected in read_integer; input is '%c'.\n",
		    c + '0');
	    return (0);
	}
	i = c;
	for (;;) {
	    if (FEOF(f)) break;
	    c = *f->_ptr - '0';
	    if (c >= 10) break;
	    if (i >= -(MAXINT/10) && (i > -(MAXINT/10) || c > -(MAXINT%10))) overflow = true;
	    i = i * 10 + c;
	    f->_cnt -= 1;
	    f->_ptr += 1;
	}
	if (!(c == '#' - '0' && 2 <= i && i <= 35 && !_libp_ansi_pascal)) goto dosign;
	radix = i;
	f->_cnt -= 1;		/* skip '#' */
	f->_ptr += 1;
	c = getc(f);
    }
    d = digit_value[c];
    if (d >= radix) {
	fprintf(stderr, "Digit expected in read_integer; input is '%c'.\n", c);
	return (0);
    }
    i = d;
    for (;;) {
	if (FEOF(f)) break;
	c = *f->_ptr & 0177;
	d = digit_value[c];
	if (d >= radix) break;
	i = i * radix + d;
	f->_cnt -= 1;
	f->_ptr += 1;
    }
dosign:
    if (overflow || (i == MAXINT && sign != '-')) {
	fprintf(stderr, "Overflow in read_integer.\n");
    }
    if (sign == '-') return (-i);
    return (i);
#undef MAXINT
}


long int
read_integer_range (f, llimit, hlimit, radix)
     register FILE *f;
     register int llimit, hlimit;
     register unsigned radix;
{
    register int i;
    i = read_integer(f, radix);
    if (i < llimit || i > hlimit)
	fprintf(stderr, "Exceeds range in read_integer; input is '%d'.\n", i);
    return (i);
}


unsigned long
read_cardinal (f, radix)
     register FILE *f;
     register unsigned radix;
{
    register unsigned long c, i, d;
    register boolean overflow;
#define MAXINT ((unsigned long)-1)

    if (f == NULL) {
        fprintf(stderr, "Warning: read of cardinal attempted from unopened file.\n");
        return 0;
    }

    while (c = getc(f), c == ' ' || c == '\t' || c == '\n') ;
    overflow = false;
    if (radix == 10) {
	c -= '0';
	if (c >= 10) {
	    fprintf(stderr, "Digit expected in read_cardinal; input is '%c'.\n",
		    c + '0');
	    return (0);
	}
	i = c;
	for (;;) {
	    if (FEOF(f)) break;
	    c = *f->_ptr - '0';
	    if (c >= 10) break;
	    if (i >= MAXINT/10 && (i > MAXINT/10 || c > MAXINT%10)) overflow = true;
	    i = i * 10 + c;
	    f->_cnt -= 1;
	    f->_ptr += 1;
	}
	if (!(c == '#' - '0' && 2 <= i && i <= 35 && !_libp_ansi_pascal)) return (i);
	radix = i;
	f->_cnt -= 1;		/* skip '#' */
	f->_ptr += 1;
	c = getc(f);
    }
    d = digit_value[c];
    if (d >= radix) {
	fprintf(stderr, "Digit expected in read_cardinal; input is '%c'.\n", c);
	return (0);
    }
    i = d;
    for (;;) {
	if (FEOF(f)) break;
	c = *f->_ptr & 0177;
	d = digit_value[c];
	if (d >= radix) break;
	i = i * radix + d;
	f->_cnt -= 1;
	f->_ptr += 1;
    }
    if (overflow) {
	fprintf(stderr, "Overflow in read_cardinal.\n");
    }
    return (i);
#undef MAXINT
}

double
read_double (f)
     register FILE *f;
{
    register unsigned c, sign, radix;
    register double v, dradix;
    register boolean decimal_point, use_atod;
    register int exp;
    register char *p;
#define MAXDIGITS 17
    char digits[MAXDIGITS];

    if (f == NULL) {
        fprintf(stderr, "Warning: read of double attempted from unopened file.\n");
        return 0.0;
    }


    /* Skip leading whitespace */
    while (c = getc(f), c == ' ' || c == '\t' || c == '\n') ;
    /* Read and remember sign if any */
    sign = c;
    if (sign == '-' || sign == '+') {
	c = getc(f);
    }
    /* Read digits of double, or of radix specification */
    c -= '0';
    if (c >= 10) {
	fprintf(stderr, "Digit expected in read_double; input is '%c'.\n",
		c + '0');
	return (0.0);
    }
    p = digits;
    if (c != 0) {
	*p++ = c;
    }
    radix = c;
    decimal_point = 0;
    exp = 0;
    for (;;) {
	if (FEOF(f)) break;
	c = *f->_ptr;
	if (c == '.' && !decimal_point) {
	    decimal_point = 1;
	} else {
	    c -= '0';
	    if (c >= 10) break;
	    if (p == digits+MAXDIGITS) {
		/* ignore more than 17 digits, but adjust exponent */
		if (!decimal_point) {
		    exp += 1;
		}
	    }
	    else {
		if (p == digits && c == 0) {
		    /* ignore leading zeros */
		}
		else {
		    *p++ = c;
		}
		exp -= decimal_point;
	    }
	    radix = radix * 10 + c;
	}
	f->_cnt -= 1;
	f->_ptr += 1;
    }

    use_atod = true;
    if (c == '#' - '0'
	&& !decimal_point
	&& (2 <= radix && radix <= 35)
	&& !_libp_ansi_pascal) {

	/* Radix specified. */
	register unsigned d;

	dradix = v;
	f->_cnt -= 1;		/* skip '#' */
	f->_ptr += 1;
	c = getc(f) & 0177;
	d = digit_value[c];
	if (d >= radix) {
	    fprintf(stderr, "Digit expected in read_double; input is '%c'.\n", c);
	    return (0);
	}
	v = d;
	for (;;) {
	    if (FEOF(f)) break;
	    c = *f->_ptr & 0177;
	    d = digit_value[c];
	    if (d < radix) {
		v = v * dradix + d;
		if (decimal_point) exp -= 1;
	    } else if (c == '.' && !decimal_point) {
		decimal_point = true;
	    } else {
		break;
	    }
	    f->_cnt -= 1;
	    f->_ptr += 1;
	}
	/* Allow '#' to terminate numbers where 'e' is a digit. */
	if (c == '#') {
	    f->_cnt -= 1;		/* skip '#' */
	    f->_ptr += 1;
	    if (!FEOF(f)) c = *f->_ptr;
	}
	c -= '0';
	use_atod = false;
    }
    if (c == 'e' - '0' || c == 'E' - '0') {
	/* Read exponent */
	register unsigned c, esign, i;
	f->_cnt -= 1;			/* skip 'e' */
	f->_ptr += 1;
	c = getc(f);
	esign = c;
	if (c == '-' || c == '+') c = getc(f);
	c -= '0';
	if (c >= 10) {
	    fprintf(stderr, "Digit expected in exponent in read_double; input is '%c'.\n",
		    c + '0');
	    return (0.0);
	}
	i = c;
	for (;;) {
	    if (FEOF(f)) break;
	    c = *f->_ptr - '0';
	    if (c >= 10) break;
	    i = i * 10 + c;
	    f->_cnt -= 1;
	    f->_ptr += 1;
	}
	if (esign == '-') exp -= i;
	else exp += i;
    }
    if (use_atod) {
	if (p == digits || exp < -340) {
	    v = 0.0;
	}
	else if (exp > 308) {
	    v = 1.0e+999;	/* Infinity */
	}
	else {
	    v = _atod (digits, p - digits, exp);
	}
    }
    else if (exp != 0) {		/* Scale input */
	register unsigned exp1;
	register double scale;

	/* Create scale factor. */
	exp1 = abs(exp);
	scale = 1.0;
	dradix /= 16;		/* avoid overflow in construction of scale */
	for (;;) {
	    if (exp1 & 1) scale *= dradix;
	    exp1 >>= 1;
	    if (exp1 == 0) break;
	    dradix *= dradix;
	}
	/* Apply scale factor */
	if (exp < 0) v /= scale;
	else v *= scale;
	v = ldexp(v, exp*4);
    }
    return (sign == '-' ? -v : v);
}

/*** This works with MOXIE because you can truncate a double and get a
     single.  For IEEE, this will need to be written in Pascal or
     something to avoid C conversion. ***/
float
read_real (f)
     register FILE *f;
{
    return (read_double(f));
}

long long int
read_int64 (f, radix)
     register FILE *f;
     register unsigned radix;
{
    register unsigned long c, sign;
    register unsigned long long i, d;
    register boolean overflow;
#define MAXINT 2147483647
    long long MAXLONGLONG;
    long long longmax = MAXINT;
    long long ulongmax = longmax * 2 + 1;
    MAXLONGLONG = ulongmax + longmax * 2 * (longmax + 1);

    if (f == NULL) {
        fprintf(stderr, "Warning: read of int64 attempted from unopened file.\n");
        return 0;
    }

    while (c = getc(f), c == ' ' || c == '\t' || c == '\n') ;
    sign = c;
    if (sign == '-' || sign == '+') {
	c = getc(f);
    }
    overflow = false;
    if (radix == 10) {
	c -= '0';
	if (c >= 10) {
	    fprintf(stderr, "Digit expected in read_integer64; input is '%c'.\n",
		    c + '0');
	    return (0);
	}
	i = c;
	for (;;) {
	    if (FEOF(f)) break;
	    c = *f->_ptr - '0';
	    if (c >= 10) break;
	    if (i >= MAXLONGLONG/10 && (i > MAXLONGLONG/10 || c > MAXLONGLONG%10)) overflow = true;
	    i = i * 10 + c;
	    f->_cnt -= 1;
	    f->_ptr += 1;
	}
	if (!(c == '#' - '0' && 2 <= i && i <= 35 && !_libp_ansi_pascal)) goto dosign;
	radix = i;
	f->_cnt -= 1;		/* skip '#' */
	f->_ptr += 1;
	c = getc(f);
    }
    d = digit_value[c];
    if (d >= radix) {
	fprintf(stderr, "Digit expected in read_integer64; input is '%c'.\n", c);
	return (0);
    }
    i = d;
    for (;;) {
	if (FEOF(f)) break;
	c = *f->_ptr & 0177;
	d = digit_value[c];
	if (d >= radix) break;
	i = i * radix + d;
	f->_cnt -= 1;
	f->_ptr += 1;
    }
dosign:
    if (overflow || (i == MAXLONGLONG && sign != '-')) {
	fprintf(stderr, "Overflow in read_integer64.\n");
    }
    if (sign == '-') return (-i);
    return (i);
#undef MAXINT
}

long long int
read_int64_range (f, llimit, hlimit, radix)
     register FILE *f;
     register long long llimit, hlimit;
     register unsigned long long radix;
{
    register long long i;
    i = read_integer(f, radix);
    if (i < llimit || i > hlimit)
	fprintf(stderr, "Exceeds range in read_integer64; input is '%d'.\n", i);
    return (i);
}

unsigned long long
read_card64 (f, radix)
     register FILE *f;
     register unsigned radix;
{
    register unsigned long c;
    register unsigned long long i;
    register boolean overflow;
    register unsigned long d;    
#define MAXINT 2147483647
    unsigned long long MAXULONGLONG;
    long long MAXLONGLONG;
    long long longmax;
    long long ulongmax;

    longmax = MAXINT;
    ulongmax = longmax * 2 + 1;
    MAXLONGLONG = ulongmax + longmax * 2 * (MAXLONGLONG + 1); // @BUG: MAXLONGLONG uninitialized
    MAXULONGLONG = MAXLONGLONG * 2 + 1;

    if (f == NULL) {
        fprintf(stderr, "Warning: read of cardinal attempted from unopened file.\n");
        return 0;
    }

    while (c = getc(f), c == ' ' || c == '\t' || c == '\n') ;
    overflow = false;
    if (radix == 10) {
	c -= '0';
	if (c >= 10) {
	    fprintf(stderr, "Digit expected in read_cardinal64; input is '%c'.\n",
		    c + '0');
	    return (0);
	}
	i = c;
	for (;;) {
	    if (FEOF(f)) break;
	    c = *f->_ptr - '0';
	    if (c >= 10) break;
	    if (i >= MAXULONGLONG/10 && (i > MAXULONGLONG/10 || c > MAXULONGLONG%10)) overflow = true;
	    i = i * 10 + c;
	    f->_cnt -= 1;
	    f->_ptr += 1;
	}
	if (!(c == '#' - '0' && 2 <= i && i <= 35 && !_libp_ansi_pascal)) return (i);
	radix = i;
	f->_cnt -= 1;		/* skip '#' */
	f->_ptr += 1;
	c = getc(f);
    }
    d = digit_value[c];
    if (d >= radix) {
	fprintf(stderr, "Digit expected in read_cardinal64; input is '%c'.\n", c);
	return (0);
    }
    i = d;
    for (;;) {
	if (FEOF(f)) break;
	c = *f->_ptr & 0177;
	d = digit_value[c];
	if (d >= radix) break;
	i = i * radix + d;
	f->_cnt -= 1;
	f->_ptr += 1;
    }
    if (overflow) {
	fprintf(stderr, "Overflow in read_cardinal64.\n");
    }
    return (i);
#undef MAXINT
}