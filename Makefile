PREFIX?=	${LOCALBASE:U/usr/local}
BINDIR?=	${PREFIX}/bin
SHAREDIR?=	${PREFIX}/share

PROG_CXX=	cheribsd-update

MAN=	cheribsd-update.8

WARNS?=		6

# Statically link to ensure that it doesn't break itself by deleting old shared
# libraries, given it uses a set that does see SONAME bumps, otherwise a failed
# update could leave you unable to resume.
NO_SHARED=
LDADD=	-larchive	\
	-lz		\
	-lbz2		\
	-llzma		\
	-lbsdxml	\
	-lprivatezstd	\
	-lfetch		\
	-lssl		\
	-lcrypto	\
	-lmd		\
	-lpthread

.include <bsd.prog.mk>
