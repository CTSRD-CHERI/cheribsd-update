/*-
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2024-2025 Jessica Clarke
 */

#include <err.h>

#include <cassert>
#include <cstdio>
#include <cstdlib>

class progress_bar {
	enum { SEGMENTS = 20, PERCENT_PER_SEGMENT = 100 / SEGMENTS };
	static_assert(SEGMENTS * PERCENT_PER_SEGMENT == 100,
	    "Cannot have fractional PERCENT_PER_SEGMENT");

	FILE *file;
	int percent;

	char *
	progress_bar_str()
	{
		char bar[SEGMENTS + 1], *str;
		int i, ret;

		assert(file != nullptr);
		bar[SEGMENTS] = 0;
		for (i = 0; i < SEGMENTS; ++i) {
			if (percent >= (i + 1) * PERCENT_PER_SEGMENT)
				bar[i] = '=';
			else if (percent >= i * PERCENT_PER_SEGMENT)
				bar[i] = '>';
			else
				bar[i] = ' ';
		}

		str = NULL;
		if (percent == -1) {
			bar[SEGMENTS / 2 - 1] = bar[SEGMENTS / 2] = '?';
			ret = asprintf(&str, "[%s] ??%%", bar);
		} else
			ret = asprintf(&str, "[%s] %d%%", bar, percent);

		if (ret < 0)
			err(1, "asprintf");

		return (str);
	}

	void
	print(bool initial)
	{
		char *str;

		str = progress_bar_str();
		fprintf(file, "%s%s", initial ? "" : "\r", str);
		free(str);
	}

public:
	progress_bar() : file(nullptr) {}

	~progress_bar()
	{
		if (file != nullptr)
			stop();
	}

	void
	start(FILE *f, int pc)
	{
		assert(file == nullptr);
		file = f;
		percent = pc;
		print(true);
	}

	void
	update(int pc)
	{
		if (pc == percent)
			return;

		percent = pc;
		print(false);
	}

	void
	stop()
	{
		char *str, *p;

		str = progress_bar_str();
		for (p = str; *p != '\0'; ++p)
			*p = ' ';

		fprintf(file, "\r%s\r", str);
		free(str);
		file = nullptr;
	}
};
