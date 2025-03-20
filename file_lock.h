/*-
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2024-2025 Jessica Clarke
 */

#include <sys/stat.h>

#include <fcntl.h>
#include <unistd.h>

#include <cassert>
#include <string>

class file_lock {
	int fd = -1;

public:
	file_lock()
	{
	}

	~file_lock()
	{
		if (fd != -1)
			release();
	}

	file_lock(const file_lock &) = delete;

	file_lock(file_lock &&other)
	    : fd(other.fd)
	{
		other.fd = -1;
	}

	file_lock &
	operator=(const file_lock &) = delete;

	file_lock &
	operator=(file_lock &&other)
	{
		fd = other.fd;
		other.fd = -1;
		return (*this);
	}

	bool
	acquire(const std::string &path)
	{
		assert(fd == -1);
		fd = open(path.c_str(),
		    O_RDWR | O_CREAT | O_NONBLOCK | O_EXLOCK,
		    S_IRUSR | S_IWUSR);
		return (fd != -1);
	}

	void
	release()
	{
		assert(fd != -1);
		close(fd);
		fd = -1;
	}
};
