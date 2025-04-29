/*-
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2024-2025 Jessica Clarke
 */

#include <sys/param.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/sysctl.h>

#include <err.h>
#include <fcntl.h>
#include <fnmatch.h>
#include <fts.h>
#include <glob.h>
#include <libgen.h>
#include <spawn.h>
#include <unistd.h>
#include <vis.h>

#include <cassert>
#include <cstdarg>
#include <cstdio>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <archive.h>
#include <archive_entry.h>

#include <fetch.h>

#include <sha256.h>

#include "file_lock.h"
#include "progress_bar.h"
#include "scoped_chdir.h"
#include "status_entries.h"

extern char **environ;

static std::string destdir;

static std::string	get_machine(), get_machine_arch();

enum class CopyAct {
	COPY,
	ABORT,
	PRUNE,
	READ,
	TRAVERSE,
};

static void
usage()
{
	fprintf(stderr, "Usage: %s [-D destdir] command [options]\n",
	    getprogname());
	fprintf(stderr, "       %s -h\n",
	    getprogname());
	fprintf(stderr, "\n");
	fprintf(stderr, "Commands:\n");
	fprintf(stderr, "       update [-y] [-a arch] <current> <new>\n");
	fprintf(stderr, "       resume\n");
	fprintf(stderr, "       abort [-f]\n");
}

static void
banner(std::initializer_list<std::string> lines)
{
	fprintf(stderr, "\n");
	fprintf(stderr,
	    "--------------------------------------------------------------\n");
	for (const auto &line : lines)
		fprintf(stderr, ">>> %s\n", line.c_str());
	fprintf(stderr,
	    "--------------------------------------------------------------\n");
}

static std::string
get_db_dir()
{
	return (destdir + "/var/db/cheribsd-update");
}

static std::string
get_lock_path()
{
	return (get_db_dir() + "/lock");
}

static std::string
get_status_path()
{
	return (get_db_dir() + "/status");
}

static std::string
get_new_status_path()
{
	return (get_db_dir() + "/.status.new");
}

static std::string
get_work_dir()
{
	return (get_db_dir() + "/work");
}

static std::string
get_old_tree_dir()
{
	return (get_work_dir() + "/old");
}

static std::string
get_new_tree_dir()
{
	return (get_work_dir() + "/new");
}

static std::string
get_etc_tarball_path()
{
	return (get_work_dir() + "/etc.tar");
}

static std::string
get_tmp_dir()
{
	return (get_work_dir() + "/tmp");
}

static std::string
get_old_kernel_dir()
{
	return ("/boot/kernel.old");
}

static std::string
get_debug_dir()
{
	return ("/usr/lib/debug");
}

static const char *
path_without_prefix(const char *path, const char *prefix)
{
	size_t len;

	len = strlen(prefix);
	if (strncmp(path, prefix, len) != 0 ||
	    (path[len] != '\0' && path[len] != '/' &&
	     (prefix[0] != '/' || prefix[1] != '\0')))
		return (NULL);

	for (path = path + len; *path == '/'; ++path)
		;

	return (path);
}

static bool
read_status(status_entries &entries, const std::string &path)
{
	uint8_t block[4096], *b, *e, *p;
	status_entry_encval raw;
	std::string key;
	uint64_t len;
	int version;
	size_t r;
	bool ret;
	FILE *f;

	ret = false;
	f = fopen(path.c_str(), "r");
	if (f == NULL) {
		warn("%s: could not open", path.c_str());
		goto done;
	}

	version = fgetc(f);
	if (version != STATUS_VERSION) {
		if (version == EOF) {
			if (ferror(f))
				goto read_error;
			warnx("%s: missing version", path.c_str());
			goto done;
		}
		warnx("%s: bad version: %d != %d",
		    path.c_str(), version, STATUS_VERSION);
		goto done;
	}

	for (;;) {
		r = fread(block, 1, sizeof(block), f);
		if (r < sizeof(block)) {
			if (ferror(f) && errno == EINTR)
				clearerr(f);
			else if (r == 0)
				break;
		}
		raw.insert(raw.end(), block, block + r);
	}

	if (ferror(f)) {
read_error:
		warn("%s: could not read", path.c_str());
		goto done;
	}

	for (b = raw.data(), e = b + raw.size(), p = b; p < e; p += len) {
		if (size_t(e - p) < sizeof(len) + 1) {
			warnx("%s: missing key header at %#tx",
			    path.c_str(), p - b);
			goto done;
		}
		memcpy(&len, p, sizeof(len));
		len = le64toh(len);
		p += sizeof(len);
		if (uint64_t(e - p) < len) {
			warnx("%s: short file at %#tx; "
			    "needed %" PRIu64 " bytes, have %td",
			    path.c_str(), p - b, len, e - p);
			goto done;
		}
		key = std::string(p, p + len);
		p += len;
		if (size_t(e - p) < sizeof(len) + 1) {
			warnx("%s: missing value header at %#tx",
			    path.c_str(), p - b);
			goto done;
		}
		memcpy(&len, p, sizeof(len));
		len = le64toh(len);
		p += sizeof(len);
		if (uint64_t(e - p) < len) {
			warnx("%s: short file at %#tx; "
			    "needed %" PRIu64 " bytes, have %td",
			    path.c_str(), p - b, len, e - p);
			goto done;
		}
		entries[key] = status_entry_encval(p, p + len);
	}

	ret = true;
done:
	if (f != NULL)
		fclose(f);

	return (ret);
}

static bool
read_status(status_entries &entries)
{
	return (read_status(entries, get_status_path()));
}

static bool
write_status(const status_entries &entries)
{
	std::string newpath, path;
	status_entry_encval raw;
	uint8_t *b, *e, *p;
	uint64_t len;
	int error;
	size_t w;
	bool ret;
	FILE *f;

	raw.push_back(STATUS_VERSION);
	for (const auto &entry : entries) {
		len = htole64(entry.first.size());
		raw.insert(raw.end(), (char *)&len, (char *)(&len + 1));
		raw.insert(raw.end(), entry.first.begin(), entry.first.end());
		append_wrapped_status_entry(raw, entry.second);
	}

	ret = false;
	newpath = get_new_status_path();
	f = fopen(newpath.c_str(), "w");
	if (f == NULL) {
		warn("%s: could not open", newpath.c_str());
		goto done;
	}

	for (b = raw.data(), e = b + raw.size(), p = b; p < e; p += w) {
		w = fwrite(p, 1, e - p, f);
		if (w < size_t(e - p)) {
			if (ferror(f) && errno == EINTR)
				clearerr(f);
			else if (w == 0)
				break;
		}
	}

	if (ferror(f)) {
		warn("%s: could not write", newpath.c_str());
		goto done;
	}

	fclose(f);
	f = NULL;
	sync();
	path = get_status_path();
	error = rename(newpath.c_str(), path.c_str());
	if (error != 0) {
		warn("could not rename %s to %s",
		    newpath.c_str(), path.c_str());
		goto unlink;
	}
	sync();
	ret = true;

done:
	if (f != NULL) {
		fclose(f);
unlink:
		error = unlink(newpath.c_str());
		if (error != 0)
			warn("could not clean up %s", newpath.c_str());
	}

	return (ret);
}

static bool
delete_status()
{
	std::string path;
	int error;

	path = get_status_path();
	error = unlink(path.c_str());
	if (error != 0) {
		warn("could not remove %s", path.c_str());
		return (false);
	}

	return (true);
}

static void
remove_dir_contents(const std::string &path, bool skiproot = false)
{
	char * const paths[2] = { __DECONST(char *, path.c_str()), NULL };
	FTSENT *ftse;
	FTS *fts;
	int ret;

	fts = fts_open(paths, FTS_NOCHDIR | FTS_PHYSICAL, NULL);
	if (fts == NULL)
		err(1, "cannot fts_open %s for deletion", path.c_str());

	while ((ftse = fts_read(fts)) != NULL) {
		switch (ftse->fts_info) {
		case FTS_D:
			continue;
		case FTS_DP:
		case FTS_F:
		case FTS_DEFAULT:
		case FTS_SL:
		case FTS_SLNONE:
			break;
		case FTS_DC:
			errx(1, "cannot handle directory cycle: %s",
			    ftse->fts_path);
		case FTS_DNR:
		case FTS_ERR:
		case FTS_NS:
			errc(1, ftse->fts_errno, "cannot read %s",
			    ftse->fts_path);
		case FTS_DOT:
		case FTS_NSOK:
		default:
			errx(1, "unexpected fts_info for %s: %d",
			    ftse->fts_path, ftse->fts_info);
		}

		if (skiproot && ftse->fts_level == 0)
			continue;

		/* Ignore any errors here, we'll fail later if the flags matter */
		if (ftse->fts_statp->st_flags != 0)
			chflags(ftse->fts_path, 0);

		if (ftse->fts_info == FTS_DP)
			ret = rmdir(ftse->fts_path);
		else
			ret = unlink(ftse->fts_path);

		if (ret != 0)
			err(1, "could not delete %s", ftse->fts_path);
	}

	ret = fts_close(fts);
	if (ret != 0)
		err(1, "cannot fts_close %s for deletion",
		    path.c_str());
}

static bool
exists(const std::string &path, bool follow = true,
    struct stat *sbp = NULL)
{
	struct stat sb;
	int error;

	if (sbp == NULL)
		sbp = &sb;

	if (follow)
		error = stat(path.c_str(), sbp);
	else
		error = lstat(path.c_str(), sbp);

	return (error == 0);
}

static bool
file_exists(const std::string &path, bool follow = true,
    struct stat *sbp = NULL)
{
	struct stat sb;

	if (sbp == NULL)
		sbp = &sb;

	return (exists(path, follow, sbp) && S_ISREG(sbp->st_mode));
}

static bool
dir_exists(const std::string &path, bool follow = true,
    struct stat *sbp = NULL)
{
	struct stat sb;

	if (sbp == NULL)
		sbp = &sb;

	return (exists(path, follow, sbp) && S_ISDIR(sbp->st_mode));
}

static bool
create_owned_dir(const std::string &path, bool allow_exist = false)
{
	struct stat sb;
	int error;
	bool ret;

	ret = true;
	error = mkdir(path.c_str(), S_IRUSR | S_IWUSR | S_IXUSR);
	if (allow_exist && error != 0 && errno == EEXIST) {
		error = stat(path.c_str(), &sb);
		if (error == 0 && !S_ISDIR(sb.st_mode)) {
			error = -1;
			errno = EEXIST;
		} else
			ret = false;
	}
	if (error != 0)
		err(1, "cannot create directory %s", path.c_str());

	return (ret);
}

static void
ensure_db_dir()
{
	create_owned_dir(get_db_dir(), true);
}

static void
print_lock_acquire_error()
{
	if (errno == EACCES && getuid() != 0)
		warnx("failed to acquire lock, re-run as root");
	else if (errno == EWOULDBLOCK)
		warnx("failed to acquire lock, "
		    "is cheribsd-update already running?");
	else
		warn("failed to acquire lock");
}

static void
split_arch(std::string arch, std::string &machine,
    std::string &machine_arch)
{
	size_t i;

	/* Either machine or machine[./]machine_arch */
	i = arch.find_first_of("./");
	if (i != std::string::npos) {
		machine = arch.substr(0, i);
		machine_arch = arch.substr(i + 1);
	} else {
		machine = arch;
		machine_arch = arch;
	}
}

static std::string
version_to_url(std::string version, const std::string &machine,
    const std::string &machine_arch)
{
	std::string url;
	size_t i;
	char *p;

	/*
	 * Anything with a ':' is considered a URL, and anything else with a
	 * '/' is considered a path to a directory, unless it has an '@' and
	 * doesn't start with a / or ., in which case we prefer treating it as
	 * branch@version.
	 */
	if (version.find(":") != std::string::npos) {
		url = version;
	} else if (version.find("/") != std::string::npos &&
	    (version.find("@") == std::string::npos ||
	     version.front() == '/' || version.front() == '.')) {
		if (version.front() != '/') {
			p = getcwd(NULL, 0);
			if (p == NULL)
				err(1, "getcwd");

			version = std::string(p) + "/" + version;
			free(p);
		}
		url = "file://" + version;
	} else {
		url = "https://download.cheribsd.org/";

		/* Snapshots are "branch@version" */
		i = version.find("@");
		if (i != std::string::npos) {
			url += "snapshots/" + version.substr(0, i);
			version = version.substr(i + 1);
		} else
			url += "releases";

		url += "/" + machine + "/" + machine_arch;
		url += "/" + version + "/ftp";
	}

	if (url.back() != '/')
		url += "/";

	return (url);
}

static int
vask_yn(bool &res, bool def, const char *fmt, va_list ap)
{
	std::string line;
	size_t len;
	char *p;

	p = NULL;
retry:
	if (p != NULL)
		fprintf(stderr, "Invalid answer: %s\n", line.c_str());

	vfprintf(stderr, fmt, ap);
	if (def)
		fprintf(stderr, " [Y/n] ");
	else
		fprintf(stderr, " [y/N] ");

	p = fgetln(stdin, &len);
	if (p == NULL) {
		if (ferror(stdin))
			return (1);
		res = def;
		return (0);
	}

	if (len > 0 && p[len - 1] == '\n')
		--len;

	line = std::string(p, len);
	if (line.empty()) {
		res = def;
		return (0);
	}
	if (line == "Y" || line == "y") {
		res = true;
		return (0);
	}
	if (line == "N" || line == "n") {
		res = false;
		return (0);
	}
	goto retry;
}

static int
ask_yn(bool &res, bool def, const char *fmt, ...)
{
	va_list ap;
	int ret;

	va_start(ap, fmt);
	ret = vask_yn(res, def, fmt, ap);
	va_end(ap);
	return (ret);
}

static bool
download_file(const std::string &url, const std::string &path)
{
	progress_bar progress;
	char block[4096], *p;
	struct url_stat us;
	FILE *in, *out;
	size_t r, w;
	off_t total;

	fprintf(stderr, "Downloading %s\n", url.c_str());
	in = fetchXGetURL(url.c_str(), &us, "");
	if (in == NULL) {
		warnx("fetch: %s", fetchLastErrString);
		return (false);
	}

	out = fopen(path.c_str(), "w");
	if (out == NULL) {
		warn("fopen");
		fclose(in);
		return (false);
	}

	total = 0;
	progress.start(stderr, us.size < 0 ? -1 : 0);
	for (;;) {
		r = fread(block, 1, sizeof(block), in);
		if (r < sizeof(block)) {
			if (ferror(in) && errno == EINTR)
				clearerr(in);
			else if (r == 0)
				break;
		}

		for (p = block; r > 0; p += w, r -= w) {
			w = fwrite(p, 1, r, out);
			total += w;
			if (w < r) {
				if (ferror(out) && errno == EINTR)
					clearerr(out);
				else if (w == 0)
					break;
			}
		}

		if (us.size > 0)
			progress.update((total * 100) / us.size);
		else if (us.size == 0)
			progress.update(100);

		if (r > 0)
			break;
	}

	progress.stop();

	if (ferror(in)) {
		warn("fread");
		fclose(out);
		fclose(in);
		return (false);
	}

	if (ferror(out)) {
		warn("fwrite");
		fclose(out);
		fclose(in);
		return (false);
	}

	if (us.size > 0 && total < us.size) {
		warnx("truncated: %jd/%jd bytes",
		    (intmax_t)total, (intmax_t)us.size);
		fclose(out);
		fclose(in);
		return (false);
	}

	fclose(out);
	fclose(in);
	return (true);
}

static std::string
sha256_file(const std::string &path)
{
	std::string out;
	char *p;

	p = SHA256_File(path.c_str(), NULL);
	if (p == NULL) {
		warn("%s: could not hash", path.c_str());
		return ("");
	}

	out = p;
	free(p);
	return (out);
}

struct manifest_entry {
	std::string name;
	std::string filename;
	std::string sha256sum;
	unsigned long long nfiles;

	manifest_entry(const std::string &name, const std::string &filename,
	    const std::string &sha256sum, unsigned long long nfiles)
	    : name(name), filename(filename), sha256sum(sha256sum),
	    nfiles(nfiles)
	{
	}
};

static bool
parse_manifest(const std::string &path,
    std::vector<struct manifest_entry> &entries)
{
	size_t len, filepos, extpos, hashpos, nfilespos;
	std::string line, nfilesstr;
	unsigned long long nfiles;
	FILE *f;
	char *p;

	f = fopen(path.c_str(), "r");
	if (f == NULL) {
		warn("%s: could not open", path.c_str());
		return (false);
	}

	while ((p = fgetln(f, &len)) != NULL) {
		if (len > 0 && p[len - 1] == '\n')
			--len;
		line = std::string(p, len);
		filepos = line.find("\t");
		if (filepos == std::string::npos || filepos == 0) {
			warnx("%s: could not find name", path.c_str());
			fclose(f);
			return (false);
		}

		hashpos = line.find("\t", filepos + 1);
		if (hashpos == std::string::npos || hashpos == filepos + 1) {
			warnx("%s: could not find hash", path.c_str());
			fclose(f);
			return (false);
		}

		nfilespos = line.find("\t", hashpos + 1);
		if (nfilespos == std::string::npos ||
		    nfilespos == hashpos + 1) {
			warnx("%s: could not find file count", path.c_str());
			fclose(f);
			return (false);
		}

		nfilesstr = std::string(line, hashpos + 1,
		    nfilespos - hashpos - 1);
		errno = 0;
		nfiles = strtoull(nfilesstr.c_str(), &p, 10);
		if (*p != '\0' ||
		    (nfiles == ULLONG_MAX && errno == ERANGE)) {
			warnx("%s: bad file count: %s",
			    path.c_str(), nfilesstr.c_str());
			fclose(f);
			return (false);
		}

		extpos = std::string::npos;
		for (const auto &ext : {".txz", ".tzst"}) {
			extpos = line.rfind(ext, filepos - 1);
			if (extpos != std::string::npos &&
			    extpos + strlen(ext) == filepos)
				break;
			extpos = std::string::npos;
		}
		if (extpos == std::string::npos || extpos == 0) {
			warnx("%s: could not find basename: %s",
			    path.c_str(), line.substr(0, filepos).c_str());
			return (false);
		}

		entries.emplace_back(line.substr(0, extpos),
		    line.substr(0, filepos),
		    line.substr(filepos + 1, hashpos - filepos - 1),
		    nfiles);
	}

	if (ferror(f)) {
		warn("%s: could not read", path.c_str());
		fclose(f);
		return (false);
	}

	fclose(f);
	return (true);
}

static bool
download_dists(const std::string &url, const std::string &dir,
    std::vector<struct manifest_entry> &entries,
    std::unordered_set<std::string> &skip)
{
	std::string file, hash;

	file = dir + "/MANIFEST";
	if (!download_file(url + "MANIFEST", file))
		return (false);

	if (!parse_manifest(file, entries))
		return (false);

	for (auto it = entries.begin(); it != entries.end();) {
		if (skip.find(it->name) != skip.end())
			it = entries.erase(it);
		else
			++it;
	}

	for (const auto &entry : entries) {
		file = dir + "/" + entry.filename;
		if (!download_file(url + entry.filename, file))
			return (false);

		hash = sha256_file(file);
		if (hash.empty())
			return (false);

		if (hash != entry.sha256sum) {
			warnx("%s: hash mismatch: got %s, expected %s",
			    file.c_str(), hash.c_str(),
			    entry.sha256sum.c_str());
			return (false);
		}
	}

	return (true);
}

static bool
infer_dist_present(const std::string &dist, unsigned long long nfiles,
    bool &result)
{
	unsigned long long total, present;
	struct archive_entry *entry;
	struct archive *archive;
	progress_bar progress;
	std::string path;
	FILE *f;
	int ret;

	fprintf(stderr, "Scanning %s\n", dist.c_str());
	f = fopen(dist.c_str(), "r");
	if (f == NULL) {
		warn("could not open");
		return (false);
	}

	archive = archive_read_new();
	if (archive == NULL) {
		warnx("could not create archive reader: %s",
		    archive_error_string(NULL));
		fclose(f);
		return (false);
	}

	archive_read_support_format_all(archive);
	archive_read_support_filter_all(archive);
	ret = archive_read_open_FILE(archive, f);
	if (ret != 0) {
		warnx("could not open archive reader: %s",
		    archive_error_string(archive));
		archive_read_free(archive);
		fclose(f);
		return (false);
	}

	total = 0;
	present = 0;
	progress.start(stderr, 0);
	do {
		ret = archive_read_next_header(archive, &entry);
		if (ret == ARCHIVE_OK) {
			path = destdir + "/" + archive_entry_pathname(entry);
			if (exists(path, false))
				++present;
			++total;
			if (nfiles > 0)
				progress.update((total * 100) / nfiles);
			else
				progress.update(100);
		}
	} while (ret == ARCHIVE_OK);

	progress.stop();

	if (ret != ARCHIVE_EOF) {
		warnx("error: %s", archive_error_string(archive));
		archive_read_free(archive);
		fclose(f);
		return (false);
	}

	archive_read_free(archive);
	fclose(f);
	result = present >= (nfiles + 1) / 2;
	return (true);
}

static bool
extract_dist(const std::string &dist, unsigned long long nfiles,
    const std::string &dir)
{
	struct archive_entry *entry;
	unsigned long long total;
	struct archive *archive;
	progress_bar progress;
	scoped_chdir chdir;
	FILE *f;
	int ret;

	fprintf(stderr, "Extracting %s\n", dist.c_str());
	f = fopen(dist.c_str(), "r");
	if (f == NULL) {
		warn("could not open");
		return (false);
	}

	chdir.chdir(dir.c_str());

	archive = archive_read_new();
	if (archive == NULL) {
		warnx("could not create archive reader: %s",
		    archive_error_string(NULL));
		fclose(f);
		return (false);
	}

	archive_read_support_format_all(archive);
	archive_read_support_filter_all(archive);
	ret = archive_read_open_FILE(archive, f);
	if (ret != 0) {
		warnx("could not open archive reader: %s",
		    archive_error_string(archive));
		archive_read_free(archive);
		fclose(f);
		return (false);
	}

	total = 0;
	progress.start(stderr, 0);
	do {
		ret = archive_read_next_header(archive, &entry);
		if (ret == ARCHIVE_OK)
			ret = archive_read_extract(archive, entry,
			    ARCHIVE_EXTRACT_TIME | ARCHIVE_EXTRACT_OWNER |
			    ARCHIVE_EXTRACT_PERM | ARCHIVE_EXTRACT_ACL |
			    ARCHIVE_EXTRACT_XATTR | ARCHIVE_EXTRACT_FFLAGS);
		if (ret == ARCHIVE_OK) {
			++total;
			if (nfiles > 0)
				progress.update((total * 100) / nfiles);
			else
				progress.update(100);
		}
	} while (ret == ARCHIVE_OK);

	progress.stop();

	/* Skip ctime/mtime warnings like bsdinstall's distextract */
	if (ret != ARCHIVE_EOF && (ret != ARCHIVE_WARN ||
	    strcmp(archive_error_string(archive), "Can't restore time") != 0)) {
		warnx("error: %s", archive_error_string(archive));
		archive_read_free(archive);
		fclose(f);
		return (false);
	}

	archive_read_free(archive);
	fclose(f);
	return (true);
}

static bool
tar_from_dir(const std::string &file, const std::string &dir)
{
	struct archive_entry_linkresolver *resolver;
	struct archive_entry *entry, *sparse;
	struct archive *rarchive, *warchive;
	char block[4096], *p;
	scoped_chdir chdir;
	ssize_t r, w;
	int ret;
	FILE *f;

	fprintf(stderr, "Creating %s\n", file.c_str());
	f = fopen(file.c_str(), "w");
	if (f == NULL) {
		warn("could not open");
		return (false);
	}

	chdir.chdir(dir.c_str());

	rarchive = archive_read_disk_new();
	if (rarchive == NULL) {
		warnx("could not create archive reader: %s",
		    archive_error_string(NULL));
		fclose(f);
		return (false);
	}

	ret = archive_read_disk_open(rarchive, ".");
	if (ret != 0) {
		warnx("could not open archive reader: %s",
		    archive_error_string(rarchive));
		archive_read_free(rarchive);
		fclose(f);
		return (false);
	}

	warchive = archive_write_new();
	if (warchive == NULL) {
		warnx("could not create archive writer: %s",
		    archive_error_string(NULL));
		archive_read_free(rarchive);
		fclose(f);
		return (false);
	}

	ret = archive_write_set_format_pax_restricted(warchive);
	if (ret != 0) {
		warnx("could not set archive writer format: %s",
		    archive_error_string(warchive));
		archive_write_free(warchive);
		archive_read_free(rarchive);
		fclose(f);
		return (false);
	}

	ret = archive_write_open_FILE(warchive, f);
	if (ret != 0) {
		warnx("could not open archive writer: %s",
		    archive_error_string(warchive));
		archive_write_free(warchive);
		archive_read_free(rarchive);
		fclose(f);
		return (false);
	}

	resolver = archive_entry_linkresolver_new();
	if (resolver == NULL) {
		warnx("could not create link resolver: %s",
		    archive_error_string(NULL));
		archive_write_free(warchive);
		archive_read_free(rarchive);
		fclose(f);
		return (false);
	}

	archive_entry_linkresolver_set_strategy(resolver,
	    archive_format(warchive));

	archive_read_disk_set_symlink_physical(rarchive);
	archive_read_disk_set_standard_lookup(rarchive);

	do {
		ret = archive_read_next_header(rarchive, &entry);
		if (ret == ARCHIVE_OK) {
			archive_entry_linkify(resolver, &entry, &sparse);
			if (sparse != NULL) {
				warnx("error: unexpected deferred entry");
				archive_entry_linkresolver_free(resolver);
				archive_write_free(warchive);
				archive_read_free(rarchive);
				fclose(f);
				return (false);
			}

			ret = archive_read_disk_descend(rarchive);
		}
		if (ret == ARCHIVE_OK)
			ret = archive_write_header(warchive, entry);
		if (ret == ARCHIVE_OK) {
			/* Don't write data for hardlinks / non-regular files */
			if (archive_entry_size_is_set(entry) &&
			    archive_entry_size(entry) == 0)
				goto write_data_done;
		}
		while (ret == ARCHIVE_OK) {
			r = archive_read_data(rarchive, block, sizeof(block));
			if (r == 0)
				break;
			else if (r < 0)
				ret = r;

			for (p = block; r > 0; p += w, r -= w) {
				w = archive_write_data(warchive, p, r);
				if (w < 0) {
					ret = w;
					break;
				}
			}
		}

write_data_done:
		if (ret == ARCHIVE_OK)
			ret = archive_write_finish_entry(warchive);
	} while (ret == ARCHIVE_OK);

	if (ret != ARCHIVE_EOF) {
		if (archive_error_string(warchive) != NULL)
			warnx("error: %s", archive_error_string(warchive));
		else
			warnx("error: %s", archive_error_string(rarchive));
		archive_entry_linkresolver_free(resolver);
		archive_write_free(warchive);
		archive_read_free(rarchive);
		fclose(f);
		return (false);
	}

	entry = NULL;
	archive_entry_linkify(resolver, &entry, &sparse);
	if (entry != NULL || sparse != NULL) {
		warnx("error: unexpected deferred entry");
		archive_entry_linkresolver_free(resolver);
		archive_write_free(warchive);
		archive_read_free(rarchive);
		fclose(f);
		return (false);
	}

	archive_entry_linkresolver_free(resolver);
	archive_write_free(warchive);
	archive_read_free(rarchive);
	fclose(f);
	return (true);
}

static bool
extract_dists(const std::vector<struct manifest_entry> &entries,
    const std::string &distdir, const std::string &treedir)
{
	for (const auto &entry : entries) {
		if (!extract_dist(distdir + "/" + entry.filename, entry.nfiles,
		    treedir))
			return (false);
	}

	return (true);
}

static bool
filter_old_dists(std::vector<struct manifest_entry> &entries,
    const std::string &distdir, std::unordered_set<std::string> &skip)
{
	std::string path;
	bool present;
	int error;

	for (auto it = entries.begin(); it != entries.end();) {
		path = distdir + "/" + it->filename;
		if (!infer_dist_present(path, it->nfiles, present))
			return (false);

		if (!present) {
			fprintf(stderr, "Skipping %s\n", path.c_str());
			error = unlink(path.c_str());
			if (error != 0) {
				warn("could not delete %s", path.c_str());
				return (false);
			}
			skip.insert(it->name.c_str());
			it = entries.erase(it);
		} else
			++it;
	}

	return (true);
}

static bool
remove_files_in(const std::string &from, const std::string &in)
{
	char * const paths[2] = { __DECONST(char *, in.c_str()), NULL };
	std::string path;
	struct stat sb;
	const char *p;
	FTSENT *ftse;
	FTS *fts;
	bool ret;
	int err;

	fts = fts_open(paths, FTS_NOCHDIR | FTS_PHYSICAL, NULL);
	if (fts == NULL) {
		warn("cannot fts_open %s", in.c_str());
		goto err;
	}

	while ((ftse = fts_read(fts)) != NULL) {
		switch (ftse->fts_info) {
		case FTS_D:
		case FTS_DP:
			continue;
		case FTS_F:
		case FTS_DEFAULT:
		case FTS_SL:
		case FTS_SLNONE:
			break;
		case FTS_DC:
			warnx("cannot handle directory cycle: %s",
			    ftse->fts_path);
			goto err;
		case FTS_DNR:
		case FTS_ERR:
		case FTS_NS:
			warnc(ftse->fts_errno, "cannot read %s",
			    ftse->fts_path);
			goto err;
		case FTS_DOT:
		case FTS_NSOK:
		default:
			warnx("unexpected fts_info for %s: %d",
			    ftse->fts_path, ftse->fts_info);
			goto err;
		}

		p = path_without_prefix(ftse->fts_path, in.c_str());
		if (p == NULL) {
			warnx("%s does not have %s as a prefix",
			    ftse->fts_path, in.c_str());
			goto err;
		}

		if (*p == '\0' || from == "/")
			path = from + p;
		else
			path = from + "/" + p;

		if (!exists(path, false, &sb))
			continue;

		/* Ignore any errors here, we'll fail later if the flags matter */
		if (sb.st_flags != 0)
			chflags(path.c_str(), 0);

		err = unlink(path.c_str());

		if (err != 0) {
			warn("could not delete %s", path.c_str());
			goto err;
		}
	}

	ret = true;
	goto done;

err:
	ret = false;

done:
	if (fts != NULL && fts_close(fts) != 0) {
		warn("cannot fts_close %s", in.c_str());
		ret = false;
	}
	return (ret);
}

static bool
remove_files_glob(const std::string &from,
    std::initializer_list<std::string> pats)
{
	scoped_chdir chdir;
	size_t i;
	glob_t g;

	chdir.chdir(from.c_str());
	for (const auto &pat : pats) {
		if (glob(pat.c_str(), GLOB_NOCHECK | GLOB_ERR, NULL, &g) != 0) {
			warn("could not glob %s", pat.c_str());
			return (false);
		}

		for (i = 0; i < g.gl_matchc; i++) {
			if (unlink(g.gl_pathv[i]) != 0) {
				warn("could not delete %s/%s",
				    from.c_str(), g.gl_pathv[i]);
				return (false);
			}
		}
	}

	return (true);
}

static bool
prepare_tree(const std::string &url, const std::string &dir,
    bool new_tree, bool resume, std::unordered_set<std::string> &dists,
    std::unordered_set<std::string> &skip)
{
	std::vector<struct manifest_entry> entries;
	std::string tmpdir, tmptreedir;
	bool ret;
	int err;

	tmpdir = get_tmp_dir();
	tmptreedir = tmpdir + "/tree";

	if (dir_exists(dir)) {
		if (resume && !dir_exists(tmpdir))
			return (true);
		remove_dir_contents(dir);
	}

	if (!create_owned_dir(tmpdir, resume)) {
		remove_dir_contents(tmpdir);
		create_owned_dir(tmpdir);
	}

	if (!download_dists(url, tmpdir, entries, skip))
		goto err;

	if (!new_tree) {
		if (!filter_old_dists(entries, tmpdir, skip))
			goto err;
	}

	create_owned_dir(tmptreedir);
	if (!extract_dists(entries, tmpdir, tmptreedir))
		goto err;

	for (const auto &entry : entries)
		dists.insert(entry.name);

	if (new_tree) {
		if (!tar_from_dir(get_etc_tarball_path(),
		    tmptreedir + "/var/db/etcupdate/current"))
			goto err;
	}

	fprintf(stderr, "Cleaning etcupdate-managed files\n");

	if (!remove_files_in(tmptreedir,
	    tmptreedir + "/var/db/etcupdate/current"))
		goto err;

	remove_dir_contents(tmptreedir + "/var/db/etcupdate");

	/*
	 * Leave generated files alone and let etcupdate regenerate them
	 * (otherwise they will get replaced with pristine copies from the new
	 * tree until etcupdate is finally run to regenerate them).
	 * Keep this list in sync with etcupdate's.
	 */
	if (!remove_files_glob(tmptreedir,
	    {"etc/*.db", "etc/passwd", "var/db/services.db"}))
		goto err;

	sync();
	err = rename(tmptreedir.c_str(), dir.c_str());
	if (err != 0) {
		warn("could not rename %s to %s",
		    tmptreedir.c_str(), dir.c_str());
		goto err;
	}
	sync();
	ret = true;
	goto done;

err:
	ret = false;

done:
	remove_dir_contents(tmpdir);
	return (ret);
}

static int
step_init(status_entries &status __unused, bool resume)
{
	std::string workdir;

	workdir = get_work_dir();
	if (!create_owned_dir(workdir, resume)) {
		remove_dir_contents(workdir);
		create_owned_dir(workdir);
	}

	return (0);
}

static int
step_current(status_entries &status, bool resume)
{
	std::unordered_set<std::string> dists, skip;
	std::string from_url;

	if (!get_status_entry(status, "from_url", from_url))
		return (1);

	banner({"Generating reference tree for current version"});
	if (!prepare_tree(from_url, get_old_tree_dir(), false, resume,
	    dists, skip))
		return (1);

	add_status_entry(status, "current_dists", dists);
	add_status_entry(status, "skip_dists", skip);
	return (0);
}

static int
step_new(status_entries &status, bool resume)
{
	std::unordered_set<std::string> dists, skip;
	std::string to_url;

	if (!get_status_entry(status, "to_url", to_url))
		return (1);

	if (!get_status_entry(status, "skip_dists", skip))
		return (1);

	banner({"Generating reference tree for new version"});
	if (!prepare_tree(to_url, get_new_tree_dir(), true, resume,
	    dists, skip))
		return (1);

	add_status_entry(status, "new_dists", dists);
	return (0);
}

static int
step_confirm(status_entries &status, bool resume __unused)
{
	std::unordered_set<std::string> current_dists, new_dists, either_dists,
	    skip_dists, update_dists, add_dists, remove_dists;
	std::vector<std::pair<std::string, std::unordered_set<std::string>>>
	    categories;
	std::vector<std::string> sorted_dists;
	bool yes;
	int ret;

	if (!get_status_entry(status, "current_dists", current_dists))
		return (1);

	if (!get_status_entry(status, "new_dists", new_dists))
		return (1);

	if (!get_status_entry(status, "skip_dists", skip_dists))
		return (1);

	if (!get_status_entry(status, "yes", yes))
		return (1);

	banner({"Confirm update"});

	either_dists.insert(current_dists.begin(), current_dists.end());
	either_dists.insert(new_dists.begin(), new_dists.end());
	for (const auto &dist : either_dists) {
		bool in_cur = current_dists.find(dist) != current_dists.end();
		bool in_new = new_dists.find(dist) != new_dists.end();
		if (in_cur && in_new)
			update_dists.insert(dist);
		else if (in_cur)
			remove_dists.insert(dist);
		else
			add_dists.insert(dist);
	}

	categories.emplace_back("skipped", skip_dists);
	categories.emplace_back("updated", update_dists);
	categories.emplace_back("added", add_dists);
	categories.emplace_back("removed", remove_dists);
	for (const auto &cat : categories) {
		if (cat.second.empty())
			continue;

		sorted_dists = std::vector<std::string>(cat.second.begin(),
		    cat.second.end());
		std::sort(sorted_dists.begin(), sorted_dists.end());
		fprintf(stderr, "The following distribution sets will be %s:\n",
		    cat.first.c_str());
		for (const auto &dist : sorted_dists)
			fprintf(stderr, "    %s\n", dist.c_str());
		fprintf(stderr, "\n");
	}

	if (!yes) {
		ret = ask_yn(yes, true, "Proceed?");
		if (ret != 0) {
			warn("could not read from stdin");
			return (ret);
		}
	}

	if (!yes) {
		remove_dir_contents(get_work_dir());
		if (!delete_status())
			return (1);

		banner({"Abort finished"});
		return (1);
	}

	return (0);
}

template <typename F, typename ...Ts>
static bool
copy_tree(const std::string &from, const std::string &to, F callback,
    Ts &&...args)
{
	char * const paths[2] = { __DECONST(char *, from.c_str()), NULL };
	struct archive_entry_linkresolver *resolver;
	unsigned long fflags_set, fflags_clear;
	struct archive_entry *entry, *sparse;
	struct archive *rarchive, *warchive;
	bool ret, ro, done, reg, dir;
	std::string path, rpath;
	char block[4096];
	struct stat sb;
	const char *p;
	int aret, fd;
	ssize_t r, w;
	FTSENT *ftse;
	int pass;
	FTS *fts;

	rarchive = NULL;
	warchive = NULL;
	resolver = NULL;
	entry = NULL;
	fts = NULL;
	fd = -1;

	rarchive = archive_read_disk_new();
	if (rarchive == NULL) {
		warnx("could not create archive reader: %s",
		    archive_error_string(NULL));
		goto err;
	}

	warchive = archive_write_disk_new();
	if (warchive == NULL) {
		warnx("could not create archive writer: %s",
		    archive_error_string(NULL));
		goto err;
	}

	resolver = archive_entry_linkresolver_new();
	if (resolver == NULL) {
		warnx("could not create link resolver: %s",
		    archive_error_string(NULL));
		goto err;
	}

	entry = archive_entry_new();
	if (entry == NULL) {
		warn("cannot allocate entry for copy");
		goto err;
	}

	/*
	 * All tar formats give us hardlinks in the "obvious" manner, i.e. the
	 * first link to be seen writes the data and subsequent ones just link.
	 * Pick ARCHIVE_FORMAT_TAR_PAX_RESTRICTED specifically so it's exactly
	 * the same as in tar_from_dir.
	 */
	archive_entry_linkresolver_set_strategy(resolver,
	    ARCHIVE_FORMAT_TAR_PAX_RESTRICTED);

	archive_read_disk_set_symlink_physical(rarchive);
	archive_read_disk_set_standard_lookup(rarchive);
	archive_write_disk_set_options(warchive,
	    ARCHIVE_EXTRACT_TIME | ARCHIVE_EXTRACT_OWNER |
	    ARCHIVE_EXTRACT_PERM | ARCHIVE_EXTRACT_ACL |
	    ARCHIVE_EXTRACT_XATTR | ARCHIVE_EXTRACT_FFLAGS |
	    ARCHIVE_EXTRACT_SAFE_WRITES |
	    ARCHIVE_EXTRACT_SECURE_SYMLINKS |
	    ARCHIVE_EXTRACT_CLEAR_NOCHANGE_FFLAGS);

	for (pass = 0, done = false; !done; ++pass) {
		fts = fts_open(paths, FTS_NOCHDIR | FTS_PHYSICAL, NULL);
		if (fts == NULL) {
			warn("cannot fts_open %s for copy", path.c_str());
			goto err;
		}
		aret = ARCHIVE_OK;
		while (!done && aret == ARCHIVE_OK &&
		    (ftse = fts_read(fts)) != NULL) {
			switch (ftse->fts_info) {
			case FTS_DP:
				continue;
			case FTS_D:
			case FTS_F:
			case FTS_DEFAULT:
			case FTS_SL:
			case FTS_SLNONE:
				break;
			case FTS_DC:
				warnx("cannot handle directory cycle: %s",
				    ftse->fts_path);
				goto err;
			case FTS_DNR:
			case FTS_ERR:
			case FTS_NS:
				warnc(ftse->fts_errno, "cannot read %s",
				    ftse->fts_path);
				goto err;
			case FTS_DOT:
			case FTS_NSOK:
			default:
				warnx("unexpected fts_info for %s: %d",
				    ftse->fts_path, ftse->fts_info);
				goto err;
			}

			p = path_without_prefix(ftse->fts_path, from.c_str());
			if (p == NULL) {
				warnx("%s does not have %s as a prefixn",
				    ftse->fts_path, from.c_str());
				goto err;
			}

			rpath = std::string("/") + p;
			if (*p == '\0' || to == "/")
				path = to + p;
			else
				path = to + "/" + p;

			ro = false;
			switch (callback(pass, rpath, (const FTSENT *)ftse,
			    std::forward<Ts>(args)...)) {
			case CopyAct::COPY:
				break;
			case CopyAct::ABORT:
				goto err;
			case CopyAct::PRUNE:
				if (ftse->fts_level == FTS_ROOTLEVEL) {
					done = true;
					ftse = NULL;
				} else if (fts_set(fts, ftse, FTS_SKIP) != 0) {
					warn("cannot prune %s for fts",
					    ftse->fts_path);
					goto err;
				}
				continue;
			case CopyAct::READ:
				ro = true;
				break;
			case CopyAct::TRAVERSE:
				continue;
			}

			archive_entry_clear(entry);
			archive_entry_copy_sourcepath(entry, ftse->fts_accpath);
			archive_entry_copy_pathname(entry, path.c_str());
			aret = archive_read_disk_entry_from_file(rarchive, entry,
			    fd, ftse->fts_statp);
			if (aret == ARCHIVE_OK) {
				/*
				 * ZFS sets UF_ARCHIVE all by itself, so for
				 * directories that are themselves mount points
				 * (e.g. /dev) we'll try to create the
				 * directory with UF_ARCHIVE, which will fail.
				 * Just skip it like mv(1) does.
				 *
				 * This is all quite gross.
				 */
				archive_entry_fflags(entry, &fflags_set,
				    &fflags_clear);
				fflags_set &= ~UF_ARCHIVE;
				if (exists(path, false, &sb)) {
					reg = S_ISREG(sb.st_mode);
					dir = S_ISDIR(sb.st_mode);
					/*
					 * libarchive will only clear flag foo
					 * if nofoo is explicitly listed in the
					 * archive's flags representation, and
					 * archive_read_disk_entry_from_file
					 * will similarly regard any flags not
					 * set as flags to not set, not flags
					 * to clear, but we want to set the
					 * flags to exactly what's in the
					 * archive, so clear anything already
					 * present that's not requested (again
					 * ignoring UF_ARCHIVE).
					 */
					fflags_clear |= sb.st_flags &
					    ~(fflags_set | UF_ARCHIVE);
				} else {
					reg = false;
					dir = false;
				}

				archive_entry_set_fflags(entry, fflags_set,
				    fflags_clear);

				archive_entry_linkify(resolver, &entry,
				    &sparse);
				if (sparse != NULL) {
					warnx("error: unexpected deferred entry");
					goto err;
				}

				if (ro)
					continue;

				if (archive_entry_filetype(entry) == AE_IFDIR) {
					/* https://github.com/libarchive/libarchive/pull/2477 */
					if (reg && unlink(path.c_str()) != 0)
						warn("cannot unlink %s for new directory",
						    path.c_str());

					/*
					 * libarchive isn't diligent about
					 * clearing SF_IMMUTABLE when updating
					 * an existing directory, so clear it
					 * here and let libarchive restore it
					 * if still required.
					 */
					if (dir &&
					    (sb.st_flags & SF_IMMUTABLE) != 0 &&
					    chflags(path.c_str(), sb.st_flags &
					    ~SF_IMMUTABLE) != 0)
						warn("cannot chflags noschg %s "
						    "for existing directory",
						    path.c_str());
				}
				aret = archive_write_header(warchive, entry);
			}
			if (aret == ARCHIVE_OK) {
				/* Don't write data for hardlinks / non-regular files */
				if (archive_entry_size_is_set(entry) &&
				    archive_entry_size(entry) == 0)
					goto write_data_done;
			}

			fd = open(ftse->fts_accpath, O_RDONLY);
			if (fd < 0) {
				warn("cannot open %s for copy",
				    ftse->fts_accpath);
				goto err;
			}

			while (aret == ARCHIVE_OK) {
				r = read(fd, block, sizeof(block));
				if (r == 0)
					break;
				else if (r < 0) {
					warn("failed to read %s for copy",
					    ftse->fts_path);
					goto err;
				}

				for (p = block; r > 0; p += w, r -= w) {
					w = archive_write_data(warchive, p, r);
					if (w < 0) {
						aret = w;
						break;
					}
				}
			}

			close(fd);
			fd = -1;

write_data_done:
			if (aret == ARCHIVE_OK)
				aret = archive_write_finish_entry(warchive);
		}

		if (ftse != NULL) {
			if (archive_error_string(warchive) != NULL)
				warnx("cannot write %s: %s",
				    path.c_str(),
				    archive_error_string(warchive));
			else
				warnx("cannot read %s: %s",
				    ftse->fts_path,
				    archive_error_string(rarchive));
			goto err;
		}

		if (fts != NULL && fts_close(fts) != 0) {
			fts = NULL;
			warn("cannot fts_close %s for copy", from.c_str());
			goto err;
		}

		fts = NULL;
	}

	ret = true;
	goto done;

err:
	ret = false;

done:
	if (fd >= 0)
		close(fd);
	archive_entry_linkresolver_free(resolver);
	if (warchive != NULL && archive_write_close(warchive) != ARCHIVE_OK) {
		warnx("cannot close %s for copy: %s",
		    to.c_str(), archive_error_string(warchive));
		ret = false;
	}
	archive_write_free(warchive);
	archive_entry_free(entry);
	if (rarchive != NULL && archive_read_close(rarchive) != ARCHIVE_OK) {
		warnx("cannot close %s for copy: %s",
		    to.c_str(), archive_error_string(rarchive));
		ret = false;
	}
	archive_read_free(rarchive);
	if (fts != NULL && fts_close(fts) != 0) {
		warn("cannot fts_close %s for copy", from.c_str());
		ret = false;
	}
	return (ret);
}

static bool
copy_tree(const std::string &from, const std::string &to)
{
	return (copy_tree(from, to,
	    [](int pass, const std::string &, const FTSENT *) {
		return (pass == 0 ? CopyAct::COPY : CopyAct::PRUNE);
	    }));
}

static bool
is_jailed()
{
	size_t jailedlen;
	int jailed, err;

	jailedlen = sizeof(jailed);
	err = sysctlbyname("security.jail.jailed", &jailed, &jailedlen,
	    NULL, 0);
	if (err == 0)
		return (jailed != 0);

	warn("sysctl security.jail.jailed");
	return (false);
}

static int
get_kern_bootfile(std::string &path)
{
	char buf[MAXPATHLEN];
	int mib[2];
	size_t len;

	mib[0] = CTL_KERN;
	mib[1] = KERN_BOOTFILE;
	len = sizeof(buf);
	if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), buf, &len, NULL, 0)
	    == -1) {
		warn("sysctl kern.bootfile");
		return (1);
	}

	path = buf;
	return (0);
}

static int
set_kern_bootfile(const std::string &path)
{
	int mib[2];

	mib[0] = CTL_KERN;
	mib[1] = KERN_BOOTFILE;
	if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), NULL, 0, path.c_str(),
	    path.size() + 1) == -1) {
		warn("sysctl kern.bootfile");
		return (1);
	}

	return (0);
}

static bool
backup_kernel(const std::string &kerndir, const std::string &kernfile,
    const std::string &backupdir)
{
	std::string destdebugdir;
	int ret;

	fprintf(stderr, "Backing up %s to %s\n",
	    (destdir + kerndir).c_str(),
	    (destdir + backupdir).c_str());

	destdebugdir = destdir + get_debug_dir();

	if (exists(destdir + backupdir, false))
		remove_dir_contents(destdir + backupdir);

	if (exists(destdebugdir + backupdir, false))
		remove_dir_contents(destdebugdir + backupdir);

	if (!copy_tree(destdir + kerndir, destdir + backupdir))
		return (false);

	if (exists(destdebugdir + kerndir, false) &&
	    !copy_tree(destdebugdir + kerndir, destdebugdir + backupdir))
		return (false);

	if (!is_jailed()) {
		ret = set_kern_bootfile(destdir + backupdir + kernfile);
		if (ret != 0)
			return (false);
	}

	return (true);
}

static int
split_path(const std::string &path, std::string &dir, std::string &file)
{
	char *dirbuf, *filebuf;
	int ret;

	dirbuf = strdup(path.c_str());
	filebuf = strdup(path.c_str());
	if (dirbuf == NULL || filebuf == NULL) {
		warn("strdup");
		ret = 1;
	} else {
		dir = dirname(dirbuf);
		file = basename(filebuf);
		ret = 0;
	}

	free(dirbuf);
	free(filebuf);
	return (ret);
}

/*
 * Work around https://bugs.freebsd.org/bugzilla/show_bug.cgi?id=59739
 * by having a dummy prior stage for /. Hope/assume that /'s metadata doesn't
 * need to change across updates; if that turns out to be false then we can
 * handle it manually.
 *
 * Also skip /boot/efi since, if the ESP is mounted there, we won't be able to
 * set timestamps on it (and even if we could that would apply to the ESP not
 * the directory in /boot for the mountpoint). As with /, the metadata for this
 * should not be changing anyway.
 */
static const char * const * const copy_stage_skip[] = {
	(const char * const[]) {
		"=/",
		"=/boot/efi",
		NULL
	},
};

static const char * const * const copy_stage_boot[] = {
	(const char * const[]) {
		"=/",
		"+/boot",
		NULL
	},
};

static const char * const * const copy_stage_world[] = {
	(const char * const[]) {
		"=/",
		"=/libexec",
		"=/libexec/ld-elf*.so*",
		NULL
	},
	(const char * const[]) {
		"=/",
		"+/lib*",
		NULL
	},
	(const char * const[]) {
		"=/",
		"=/usr",
		"+/usr/lib*",
		"!+/usr/lib/debug",
		NULL
	},
	(const char * const[]) {
		"+/",
		NULL
	},
};

static bool
copy_stage_pass_match(const char * const *matches, const std::string &path)
{
	const char * const *p, *s;
	bool found, positive;
	int flags;

	found = false;
	for (p = matches; (s = *p) != NULL; ++p) {
		if (*s == '!') {
			positive = false;
			++s;
		} else
			positive = true;

		flags = FNM_PATHNAME;
		switch (*s) {
		case '=':
			break;
		case '+':
			flags |= FNM_LEADING_DIR;
			/* Special case; path won't be of the form //... */
			if (s[1] == '/' && s[2] == '\0') {
				if (path.rfind("/", 0) == 0)
					found = positive;
				continue;
			}
			break;
		default:
			errx(1, "bad match prefix: %s", s);
		}

		++s;

		if (fnmatch(s, path.c_str(), flags) == 0)
			found = positive;
	}

	return (found);
}

template <size_t N>
static CopyAct
filter_copy_stage_done(int pass, const std::string &path, const FTSENT *ftse,
    const char * const * const(&)[N])
{
	if (pass >= 0 && (size_t)pass >= N) {
		if (ftse->fts_level != FTS_ROOTLEVEL || pass != N) {
			warnx("saw unexpected pass %d for %s",
			    pass, path.c_str());
			return (CopyAct::ABORT);
		}
		return (CopyAct::PRUNE);
	}

	return (CopyAct::COPY);
}

template <size_t N>
static CopyAct
filter_copy_stage_match(int pass, const std::string &path, const FTSENT *,
    const char * const * const(&stage)[N], bool prior)
{
	size_t i;

	if (!prior && (size_t)pass >= N) {
		warnx("saw unexpected pass %d for %s",
		    pass, path.c_str());
		return (CopyAct::ABORT);
	}

	for (i = 0; i < N; ++i) {
		if (!prior && i > (size_t)pass)
			break;

		if (copy_stage_pass_match(stage[i], path)) {
			if (!prior && i == (size_t)pass)
				return (CopyAct::COPY);
			else if (pass == 0)
				return (CopyAct::READ);
			else
				return (CopyAct::TRAVERSE);
		}
	}

	return (CopyAct::PRUNE);
}

template <size_t N>
static CopyAct
filter_copy_stage_match(int pass, const std::string &path, const FTSENT *ftse,
    const char * const * const(&stage)[N])
{
	return (filter_copy_stage_match(pass, path, ftse, stage, false));
}

template <typename ...Ts, size_t N>
static typename std::enable_if<(sizeof...(Ts) > 0), CopyAct>::type
filter_copy_stage_match(int pass, const std::string &path, const FTSENT *ftse,
    const char * const * const(&prior)[N], const Ts &...stages)
{
	switch (filter_copy_stage_match(pass, path, ftse, prior, true)) {
	case CopyAct::COPY:
		warnx("saw prior COPY for %s", path.c_str());
		return (CopyAct::ABORT);
	case CopyAct::ABORT:
		return (CopyAct::ABORT);
	case CopyAct::PRUNE:
		break;
	case CopyAct::READ:
		return (CopyAct::READ);
	case CopyAct::TRAVERSE:
		return (CopyAct::TRAVERSE);
	}

	return (filter_copy_stage_match(pass, path, ftse, stages...));
}

template <typename ...Ts>
static typename std::enable_if<(sizeof...(Ts) > 0), CopyAct>::type
filter_copy_stage(int pass, const std::string &path, const FTSENT *ftse,
    const Ts &...stages)
{
	const auto &stage = std::get<sizeof...(stages) - 1>(
	    std::forward_as_tuple(std::forward<const Ts &>(stages)...));

	switch (filter_copy_stage_done(pass, path, ftse, stage)) {
	case CopyAct::COPY:
		break;
	case CopyAct::ABORT:
		return (CopyAct::ABORT);
	case CopyAct::PRUNE:
		return (CopyAct::PRUNE);
	case CopyAct::READ:
		warnx("saw READ checking done for %s", path.c_str());
		return (CopyAct::ABORT);
	case CopyAct::TRAVERSE:
		warnx("saw TRAVERSE checking done for %s", path.c_str());
		return (CopyAct::ABORT);
	}

	return (filter_copy_stage_match(pass, path, ftse,
	    std::forward<const Ts &>(stages)...));
}

static CopyAct
callback_boot(int pass, const std::string &path, const FTSENT *ftse,
    const std::string &bootfile, const std::string &bootdir,
    bool &update_esp)
{
	std::string destpath, oldkerndir;
	CopyAct act;

	act = filter_copy_stage(pass, path, ftse, copy_stage_skip,
	    copy_stage_boot);
	if (act != CopyAct::COPY)
		return (act);

	destpath = destdir + path;
	if (pass == 0 && destpath == bootdir && exists(destpath, false)) {
		oldkerndir = get_old_kernel_dir();
		if (!backup_kernel(path, bootfile, oldkerndir))
			return (CopyAct::ABORT);
	}

	if (path == "/boot/loader.efi")
		update_esp = true;

	return (CopyAct::COPY);
}

static bool
set_files_same(bool &res, const std::string &patha, const std::string &pathb)
{
	char ba[4096], bb[4096], *pa, *pb;
	size_t na, nb, n;
	FILE *fa, *fb;
	bool ret;

	fa = fb = NULL;

	fa = fopen(patha.c_str(), "r");
	if (fa == NULL) {
		warn("could not open %s", patha.c_str());
		goto err;
	}

	fb = fopen(pathb.c_str(), "r");
	if (fb == NULL) {
		warn("could not open %s", pathb.c_str());
		goto err;
	}

	for (na = nb = 0;; pa += n, pb += n, na -= n, nb -= n) {
		if (na == 0) {
			na = fread(ba, 1, sizeof(ba), fa);
			pa = ba;
		}

		if (nb == 0) {
			nb = fread(bb, 1, sizeof(bb), fb);
			pb = bb;
		}

		if (na == 0) {
			if (ferror(fa)) {
				warn("could not read %s", patha.c_str());
				goto err;
			} else if (!feof(fa)) {
				warnx("zero-byte read of %s", patha.c_str());
				goto err;
			}
		}

		if (nb == 0) {
			if (ferror(fb)) {
				warn("could not read %s", pathb.c_str());
				goto err;
			} else if (!feof(fb)) {
				warnx("zero-byte read of %s", pathb.c_str());
				goto err;
			}
		}

		if (na == 0 && nb == 0) {
			res = true;
			break;
		}

		n = std::min(na, nb);
		if (n == 0 || memcmp(pa, pb, n) != 0) {
			res = false;
			break;
		}
	}

	ret = true;
	goto done;

err:
	ret = false;

done:
	if (fb != NULL)
		fclose(fb);
	if (fa != NULL)
		fclose(fa);
	return (ret);
}

static bool
copy_loader_to_esp(const std::string &machine)
{
	std::string archbootname, spath, fpath, rpath;
	bool fcopy, rcopy;

	if (machine == "arm64")
		archbootname = "aa64";
	else if (machine == "amd64")
		archbootname = "x64";
	else if (machine == "riscv")
		archbootname = "riscv64";
	else {
		warnx("unsupported EFI architecture");
		return (false);
	}

	spath = destdir + "/boot/loader.efi";
	fpath = destdir + "/boot/efi/efi/freebsd/loader.efi";
	rpath = destdir + "/boot/efi/efi/boot/boot" + archbootname + ".efi";

	fcopy = exists(fpath);
	rcopy = exists(rpath);

	/*
	 * Always update FreeBSD path if it exists. Update the removable media
	 * path if the FreeBSD path doesn't exist or it has the same contents.
	 */
	if (fcopy && rcopy && !set_files_same(rcopy, fpath, rpath))
		return (false);

	/*
	 * NB: Update removable media path first, otherwise we won't copy it if
	 * interrupted and resumed.
	 */
	if (rcopy) {
		fprintf(stderr, "Updating %s\n", rpath.c_str());
		if (!copy_tree(spath, rpath))
			return (false);
	}

	if (fcopy) {
		fprintf(stderr, "Updating %s\n", fpath.c_str());
		if (!copy_tree(spath, fpath))
			return (false);
	}

	return (true);
}

static int
step_boot(status_entries &status, bool resume __unused)
{
	std::string bootfile, bootdir, machine;
	bool update_esp;
	char *buf;
	int ret;

	if (!get_status_entry(status, "machine", machine))
		return (1);

	banner({"Updating /boot"});

	ret = get_kern_bootfile(bootfile);
	if (ret != 0)
		return (ret);

	ret = split_path(bootfile, bootdir, bootfile);
	if (ret != 0)
		return (ret);

	buf = realpath(bootdir.c_str(), NULL);
	/* Ignore errors, expected inside a jail */
	if (buf != NULL) {
		bootdir = buf;
		free(buf);
	}

	update_esp = false;
	if (!copy_tree(get_new_tree_dir(), destdir.empty() ? "/" : destdir,
	    callback_boot, bootfile, bootdir, update_esp))
		return (1);

	if (update_esp && !copy_loader_to_esp(machine))
		return (1);

	return (0);
}

static CopyAct
callback_world(int pass, const std::string &path, const FTSENT *ftse)
{
	return (filter_copy_stage(pass, path, ftse, copy_stage_skip,
	    copy_stage_boot, copy_stage_world));
}

static bool
step_boot_needs_reboot(status_entries &status __unused)
{
	std::string path;
	char *buf;

	buf = realpath(destdir.empty() ? "/" : destdir.c_str(), NULL);
	if (buf != NULL) {
		path = buf;
		free(buf);
		if (path != "/")
			return (false);
	} else
		warn("realpath(%s)", destdir.c_str());

	if (is_jailed())
		return (false);

	return (true);
}

static int
step_world(status_entries &status __unused, bool resume __unused)
{
	banner({"Updating world"});

	if (!copy_tree(get_new_tree_dir(), destdir.empty() ? "/" : destdir,
	    callback_world))
		return (1);

	return (0);
}

static int
run_etcupdate(const char *cmd, const std::vector<const char *> &extra_args)
{
	std::vector<const char *> args;
	std::string etcupdate_path;
	int ret, child_status;
	pid_t pid;

	etcupdate_path = destdir + "/usr/sbin/etcupdate";

	args.push_back(etcupdate_path.c_str());
	if (cmd != NULL)
		args.push_back(cmd);
	args.push_back("-D");
	args.push_back(destdir.c_str());
	args.insert(args.end(), extra_args.begin(), extra_args.end());
	args.push_back(NULL);

	ret = posix_spawn(&pid, args[0], NULL, NULL,
	    (char * const *)(void *)args.data(), environ);
	if (ret != 0) {
		warnc(ret, "posix_spawn");
		return (1);
	}

	while ((ret = waitpid(pid, &child_status, 0)) == -1) {
		if (errno != EINTR) {
			warn("waitpid");
			return (1);
		}
	}

	if (!WIFEXITED(child_status) || WEXITSTATUS(child_status) != 0)
		return (1);

	return (0);
}

static int
step_etcupdate(status_entries &status __unused, bool resume __unused)
{
	std::vector<const char *> args;
	std::string etc_tarball_path;
	int ret;

	banner({"Running etcupdate"});

	etc_tarball_path = get_etc_tarball_path();

	args.push_back("-t");
	args.push_back(etc_tarball_path.c_str());
	ret = run_etcupdate(NULL, args);

	if (ret != 0) {
		banner({"etcupdate failed, please resolve then run:",
		    "    " + std::string(getprogname()) +
		    " [-D destdir] resume",
		    "to continue updating"});
		return (ret);
	}

	return (0);
}

static int
step_etcupdate_resolve(status_entries &status __unused, bool resume __unused)
{
	int ret;

	banner({"Running etcupdate resolve"});

	ret = run_etcupdate("resolve", {});

	if (ret != 0) {
		banner({"etcupdate resolve failed, please resolve then run:",
		    "    " + std::string(getprogname()) +
		    " [-D destdir] resume",
		    "to continue updating"});
		return (ret);
	}

	return (0);
}

static bool
remove_old_files(const std::string &from, const std::string &oldtree,
    const std::string &newtree)
{
	char * const paths[2] = { __DECONST(char *, oldtree.c_str()), NULL };
	std::string newpath, frompath;
	const char *p;
	FTSENT *ftse;
	FTS *fts;
	bool ret;
	int err;

	fts = fts_open(paths, FTS_NOCHDIR | FTS_PHYSICAL, NULL);
	if (fts == NULL) {
		warn("cannot fts_open %s", oldtree.c_str());
		goto err;
	}

	while ((ftse = fts_read(fts)) != NULL) {
		switch (ftse->fts_info) {
		case FTS_D:
			continue;
		case FTS_DP:
		case FTS_F:
		case FTS_DEFAULT:
		case FTS_SL:
		case FTS_SLNONE:
			break;
		case FTS_DC:
			warnx("cannot handle directory cycle: %s",
			    ftse->fts_path);
			goto err;
		case FTS_DNR:
		case FTS_ERR:
		case FTS_NS:
			warnc(ftse->fts_errno, "cannot read %s",
			    ftse->fts_path);
			goto err;
		case FTS_DOT:
		case FTS_NSOK:
		default:
			warnx("unexpected fts_info for %s: %d",
			    ftse->fts_path, ftse->fts_info);
			goto err;
		}

		p = path_without_prefix(ftse->fts_path, oldtree.c_str());
		if (p == NULL) {
			warnx("%s does not have %s as a prefix",
			    ftse->fts_path, oldtree.c_str());
			goto err;
		}

		if (*p == '\0' || newtree == "/")
			newpath = newtree + p;
		else
			newpath = newtree + "/" + p;

		if (exists(newpath, false))
			continue;

		if (*p == '\0' || from == "/")
			frompath = from + p;
		else
			frompath = from + "/" + p;

		/* Ignore any errors here, we'll fail later if the flags matter */
		chflags(frompath.c_str(), 0);

		if (S_ISDIR(ftse->fts_statp->st_mode))
			err = rmdir(frompath.c_str());
		else
			err = unlink(frompath.c_str());

		if (err != 0) {
			if (errno == ENOTEMPTY)
				fprintf(stderr, "%s not empty, keeping\n",
				    frompath.c_str());
			else if (errno != ENOENT) {
				warn("could not delete %s", frompath.c_str());
				goto err;
			}
		}
	}

	ret = true;
	goto done;

err:
	ret = false;

done:
	if (fts != NULL && fts_close(fts) != 0) {
		warn("cannot fts_close %s", oldtree.c_str());
		ret = false;
	}
	return (ret);
}

static int
step_remove_old(status_entries &status __unused, bool resume __unused)
{
	banner({"Removing old files"});

	if (!remove_old_files(destdir.empty() ? "/" : destdir,
	    get_old_tree_dir(), get_new_tree_dir()))
		return (1);

	return (0);
}

static int
step_cleanup(status_entries &status __unused, bool resume)
{
	std::string workdir;

	banner({"Cleaning up after update"});
	workdir = get_work_dir();
	if (resume && !dir_exists(workdir))
		return (0);

	remove_dir_contents(workdir);
	return (0);
}

static struct {
	const char *name;
	int (*func)(status_entries &, bool);
	bool clean_abort;
	bool (*needs_reboot)(status_entries &);
} steps[] = {
	{ "init",		step_init,		true,	NULL },
	{ "current",		step_current,		true,	NULL },
	{ "new",		step_new,		true,	NULL },
	{ "confirm",		step_confirm,		true,	NULL },
	{ "boot",		step_boot,		false,	step_boot_needs_reboot },
	{ "world",		step_world,		false,	NULL },
	{ "etcupdate",		step_etcupdate,		false,	NULL },
	{ "etcupdate_resolve",	step_etcupdate_resolve,	false,	NULL },
	{ "remove_old",		step_remove_old,	false,	NULL },
	{ "cleanup",		step_cleanup,		true,	NULL },
};

static int
run_steps(status_entries &status, bool resume)
{
	std::string state, start, stop;
	bool needs_reboot;
	int err;

	if (resume) {
		if (!get_status_entry(status, "state", state))
			return (1);
	}

	start = ":start";
	stop = ":stop";
	for (const auto &step : steps) {
		if (resume) {
			if (state == step.name + stop)
				goto stopped;
			if (state == step.name + start)
				goto started;
			continue;
		}

		add_status_entry(status, "state", step.name + start);
		if (!write_status(status))
			return (1);

started:
		err = step.func(status, resume);
		if (err != 0)
			return (err);

		needs_reboot = step.needs_reboot != NULL &&
		    step.needs_reboot(status);
		if (needs_reboot)
			banner({"Reboot required; please reboot then run:",
			    "    " + std::string(getprogname()) +
			    " [-D destdir] resume",
			    "to continue updating"});

		add_status_entry(status, "state", step.name + stop);
		if (!write_status(status))
			return (1);

		if (needs_reboot)
			return (0);

stopped:
		resume = false;
	}

	if (resume) {
		warnx("resume from unknown state %s", state.c_str());
		return (1);
	}

	if (!delete_status())
		return (1);

	banner({"Update finished; please upgrade any installed packages"});
	return (0);
}

static int
run_abort(status_entries &status, bool force)
{
	std::string state, start, stop, workdir;
	bool found, clean_abort;

	if (!get_status_entry(status, "state", state))
		return (1);

	workdir = get_work_dir();
	start = ":start";
	stop = ":stop";
	found = false;
	clean_abort = true;
	for (const auto &step : steps) {
		if (!step.clean_abort)
			clean_abort = false;

		if (state == step.name + stop ||
		    state == step.name + start) {
			found = true;
			break;
		}
	}

	if (!found || !clean_abort) {
		if (!found)
			warnx("abort from unknown state %s", state.c_str());
		else {
			fprintf(stderr,
			    "System changes have already been committed, "
			    "aborting may leave the system in an inconsistent "
			    "state.\n");
		}

		if (!force) {
			fprintf(stderr, "Not aborting (use -f to force).\n");
			return (1);
		}

		fprintf(stderr, "Enabled -f option, continuing anyway.\n");
	}

	if (dir_exists(workdir))
		remove_dir_contents(workdir);

	if (!delete_status())
		return (1);

	banner({"Abort finished"});
	return (0);
}

static int
run_dump_status(const status_entries &status)
{
	std::string val;

	for (const auto &entry : status) {
		if (!status_entry_to_string(val, entry.second))
			return (1);

		fprintf(stderr, "%s = %s\n", entry.first.c_str(), val.c_str());
	}

	return (0);
}

static int
command_update(int argc, char **argv)
{
	std::string machine, machine_arch;
	std::string from_version, to_version;
	std::string from_url, to_url;
	status_entries status;
	file_lock lock;
	bool yes;
	int ch;

	machine = get_machine();
	machine_arch = get_machine_arch();

	yes = false;
	while ((ch = getopt(argc, argv, "a:hy")) != -1) {
		switch (ch) {
		case 'a':
			split_arch(optarg, machine, machine_arch);
			break;

		case 'h':
			usage();
			return (0);

		case 'y':
			yes = true;
			break;

		case '?':
		default:
			usage();
			return (1);
		}
	}
	argc -= optind;
	argv += optind;

	if (argc < 1) {
		warnx("missing current version");
		usage();
		return (1);
	}
	from_version = argv[0];
	from_url = version_to_url(from_version, machine, machine_arch);

	if (argc < 2) {
		warnx("missing new version");
		usage();
		return (1);
	}
	to_version = argv[1];
	to_url = version_to_url(to_version, machine, machine_arch);

	if (argc > 2) {
		warnx("too many arguments");
		usage();
		return (1);
	}

	ensure_db_dir();
	if (!lock.acquire(get_lock_path())) {
		print_lock_acquire_error();
		return (1);
	}

	if (file_exists(get_status_path())) {
		fprintf(stderr,
		    "An update is currently in progress.\n"
		    "Use 'resume' command to resume, "
		    "or 'abort' command to abort.\n");
		return (1);
	}

	add_status_entry(status, "machine", machine);
	add_status_entry(status, "machine_arch", machine_arch);
	add_status_entry(status, "from_url", from_url);
	add_status_entry(status, "to_url", to_url);
	add_status_entry(status, "yes", yes);
	return (run_steps(status, false));
}

static int
command_resume(int argc, char **argv)
{
	status_entries status;
	file_lock lock;
	int ch;

	while ((ch = getopt(argc, argv, "h")) != -1) {
		switch (ch) {
		case 'h':
			usage();
			return (0);

		case '?':
		default:
			usage();
			return (1);
		}
	}
	argc -= optind;
	argv += optind;

	if (argc > 0) {
		warnx("too many arguments");
		usage();
		return (1);
	}

	ensure_db_dir();
	if (!lock.acquire(get_lock_path())) {
		print_lock_acquire_error();
		return (1);
	}

	if (!file_exists(get_status_path())) {
		fprintf(stderr,
		    "No update is currently in progress.\n"
		    "Use 'update' command to start.\n");
		return (1);
	}

	if (!read_status(status))
		return (1);

	return (run_steps(status, true));
}

static int
command_abort(int argc, char **argv)
{
	status_entries status;
	file_lock lock;
	bool force;
	int ch;

	force = false;
	while ((ch = getopt(argc, argv, "fh")) != -1) {
		switch (ch) {
		case 'f':
			force = true;
			break;

		case 'h':
			usage();
			return (0);

		case '?':
		default:
			usage();
			return (1);
		}
	}
	argc -= optind;
	argv += optind;

	if (argc > 0) {
		warnx("too many arguments");
		usage();
		return (1);
	}

	ensure_db_dir();
	if (!lock.acquire(get_lock_path())) {
		print_lock_acquire_error();
		return (1);
	}

	if (!file_exists(get_status_path())) {
		fprintf(stderr, "No update is currently in progress.\n");
		return (1);
	}

	if (!read_status(status))
		return (1);

	return (run_abort(status, force));
}

static int
command_dump_status(int argc, char **argv)
{
	status_entries status;
	std::string path;
	file_lock lock;
	int ch;

	while ((ch = getopt(argc, argv, "h")) != -1) {
		switch (ch) {
		case 'h':
			usage();
			return (0);

		case '?':
		default:
			usage();
			return (1);
		}
	}
	argc -= optind;
	argv += optind;

	if (argc > 1) {
		warnx("too many arguments");
		usage();
		return (1);
	}

	if (argc == 0) {
		if (!lock.acquire(get_lock_path())) {
			print_lock_acquire_error();
			return (1);
		}

		path = get_status_path();
		if (!file_exists(path)) {
			fprintf(stderr,
			    "No update is currently in progress.\n");
			return (1);
		}
	} else
		path = argv[0];

	if (!read_status(status, path))
		return (1);

	return (run_dump_status(status));
}

static struct {
	const char *name;
	int (*func)(int, char **);
} commands[] = {
	{ "update",		command_update },
	{ "resume",		command_resume },
	{ "abort",		command_abort },
	{ "dump-status",	command_dump_status },
};

static std::string
get_machine()
{
	int mib[2];
	size_t len;
	char buf[1024];

	mib[0] = CTL_HW;
	mib[1] = HW_MACHINE;
	len = sizeof(buf);
	if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), buf, &len, NULL, 0)
	    == -1)
		err(1, "sysctl hw.machine");

	return (buf);
}

static std::string
get_machine_arch()
{
	int mib[2];
	size_t len;
	char buf[1024];

	mib[0] = CTL_HW;
	mib[1] = HW_MACHINE_ARCH;
	len = sizeof(buf);
	if (sysctl(mib, sizeof(mib) / sizeof(mib[0]), buf, &len, NULL, 0)
	    == -1)
		err(1, "sysctl hw.machine_arch");

	return (buf);
}

int
main(int argc, char **argv)
{
	size_t len;
	int ch;

	destdir = "";
	while ((ch = getopt(argc, argv, "D:h")) != -1) {
		switch (ch) {
		case 'D':
			destdir = optarg;
			for (len = destdir.size(); len > 0; --len)
				if (destdir[len - 1] != '/')
					break;
			destdir = destdir.substr(0, len);
			break;

		case 'h':
			usage();
			return (0);

		case '?':
		default:
			usage();
			return (1);
		}
	}
	argc -= optind;
	argv += optind;
	optreset = 1;
	optind = 1;

	if (argc == 0) {
		warnx("no command given");
		usage();
		return (1);
	}

	for (const auto &command : commands)
		if (strcmp(argv[0], command.name) == 0)
			return (command.func(argc, argv));

	warnx("unknown command %s", argv[0]);
	usage();
	return (1);
}
