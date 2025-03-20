/*-
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2024-2025 Jessica Clarke
 */

#include <err.h>
#include <unistd.h>

#include <cassert>
#include <cstdlib>
#include <string>

class scoped_chdir {
	const char *cwd = NULL;

public:
	scoped_chdir()
	{
	}

	~scoped_chdir()
	{
		if (cwd != NULL)
			restore();
	}

	scoped_chdir(const scoped_chdir &) = delete;

	scoped_chdir(scoped_chdir &&other)
	    : cwd(other.cwd)
	{
		other.cwd = NULL;
	}

	scoped_chdir &
	operator=(const scoped_chdir &) = delete;

	scoped_chdir &
	operator=(scoped_chdir &&other)
	{
		cwd = other.cwd;
		other.cwd = NULL;
		return (*this);
	}

	bool
	chdir(const std::string &path)
	{
		if (cwd == NULL) {
			cwd = getcwd(NULL, 0);
			if (cwd == NULL)
				return (false);
		}

		return (::chdir(path.c_str()) != 0);
	}

	void
	restore()
	{
		assert(cwd != NULL);
		if (chdir(cwd) != 0)
			err(1, "scoped_chdir restore");
		free((void *)cwd);
		cwd = NULL;
	}
};
