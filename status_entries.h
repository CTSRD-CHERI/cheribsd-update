/*-
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright (c) 2024-2025 Jessica Clarke
 */

#include <err.h>

#include <cinttypes>
#include <cstdio>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#define	STATUS_VERSION	1

typedef std::vector<uint8_t> status_entry_encval;
typedef std::unordered_map<std::string, status_entry_encval> status_entries;

enum class EncodedType : uint8_t {
	Signed		= 0,
	Unsigned	= 1,
	Bool		= 2,
	String		= 3,
	List		= 4,
	Set		= 5,
	Tuple		= 6,
	Map		= 7,
};

static inline void
append_wrapped_status_entry(status_entry_encval &outer,
    const status_entry_encval &inner)
{
	uint64_t lelen;

	lelen = htole64(inner.size());
	outer.insert(outer.end(), (char *)&lelen, (char *)(&lelen + 1));
	outer.insert(outer.end(), inner.begin(), inner.end());
}

static inline void
append_status_entry_type(status_entry_encval &encval, EncodedType type)
{
	encval.push_back((uint8_t)type);
}

static inline status_entry_encval encode_status_entry(const std::string &val,
    EncodedType type = EncodedType::String);
static inline status_entry_encval encode_status_entry(const int64_t &val,
    EncodedType type = EncodedType::Signed);
static inline status_entry_encval encode_status_entry(const uint64_t &val,
    EncodedType type = EncodedType::Unsigned);
static inline status_entry_encval encode_status_entry(const bool &val,
    EncodedType type = EncodedType::Bool);
template <typename T> static inline status_entry_encval
encode_status_entry(const std::vector<T> &vals,
    EncodedType type = EncodedType::List);
template <typename T> static inline status_entry_encval
encode_status_entry(const std::unordered_set<T> &vals,
    EncodedType type = EncodedType::Set);
template <typename ...Ts> static inline status_entry_encval
encode_status_entry(const std::tuple<Ts...> &vals,
    EncodedType type = EncodedType::Tuple);
template <typename T1, typename T2> static inline status_entry_encval
encode_status_entry(const std::pair<T1, T2> &vals,
    EncodedType type = EncodedType::Tuple);
template <typename K, typename V> static inline status_entry_encval
encode_status_entry(const std::unordered_map<K, V> &vals,
    EncodedType type = EncodedType::Map);

static inline status_entry_encval
encode_status_entry(const std::string &val, EncodedType type)
{
	status_entry_encval encval;

	append_status_entry_type(encval, type);
	encval.insert(encval.end(), val.begin(), val.end());
	return (encval);
}

static inline status_entry_encval
encode_status_entry(const int64_t &val, EncodedType type)
{
	status_entry_encval encval;
	uint64_t leval;

	leval = htole64(val);
	append_status_entry_type(encval, type);
	encval.insert(encval.end(), (char *)&leval, (char *)(&leval + 1));
	return (encval);
}

static inline status_entry_encval
encode_status_entry(const uint64_t &val, EncodedType type)
{
	status_entry_encval encval;
	uint64_t leval;

	leval = htole64(val);
	append_status_entry_type(encval, type);
	encval.insert(encval.end(), (char *)&leval, (char *)(&leval + 1));
	return (encval);
}

static inline status_entry_encval
encode_status_entry(const bool &val, EncodedType type)
{
	return (encode_status_entry((uint64_t)val, type));
}

template <typename T>
static inline status_entry_encval
encode_status_entry(const std::vector<T> &vals, EncodedType type)
{
	std::vector<status_entry_encval> encvals;
	status_entry_encval encval;

	for (const auto &val : vals)
		encvals.push_back(encode_status_entry(val));

	append_status_entry_type(encval, type);
	for (const auto &enc : encvals)
		append_wrapped_status_entry(encval, enc);

	return (encval);
}

template <typename T>
static inline status_entry_encval
encode_status_entry(const std::unordered_set<T> &vals, EncodedType type)
{
	std::vector<T> vec;

	vec = std::vector<T>(vals.begin(), vals.end());
	return (encode_status_entry(vec, type));
}

template <size_t I, typename ...Ts>
static inline typename std::enable_if<I == sizeof...(Ts), void>::type
encode_append_status_tuple_field(
    std::vector<status_entry_encval> &encvals __unused,
    const std::tuple<Ts...> &vals __unused)
{
}

template <size_t I, typename ...Ts>
static inline typename std::enable_if<I < sizeof...(Ts), void>::type
encode_append_status_tuple_field(std::vector<status_entry_encval> &encvals,
    const std::tuple<Ts...> &vals)
{
	encvals.push_back(encode_status_entry(std::get<I>(vals)));
	encode_append_status_tuple_field<I + 1>(encvals, vals);
}

template <typename ...Ts>
static inline void
encode_append_status_tuple_field(std::vector<status_entry_encval> &encvals,
    const std::tuple<Ts...> &vals)
{
	encode_append_status_tuple_field<0>(encvals, vals);
}

template <typename ...Ts>
static inline status_entry_encval
encode_status_entry(const std::tuple<Ts...> &vals, EncodedType type)
{
	std::vector<status_entry_encval> encvals;
	status_entry_encval encval;

	encode_append_status_tuple_field(encvals, vals);

	append_status_entry_type(encval, type);
	for (const auto &enc : encvals)
		append_wrapped_status_entry(encval, enc);

	return (encval);
}

template <typename T1, typename T2>
static inline status_entry_encval
encode_status_entry(const std::pair<T1, T2> &vals, EncodedType type)
{
	std::tuple<T1, T2> tuple;

	tuple = std::tuple<T1, T2>(vals.first, vals.second);
	return (encode_status_entry(tuple, type));
}

template <typename K, typename V>
static inline status_entry_encval
encode_status_entry(const std::unordered_map<K, V> &vals, EncodedType type)
{
	std::vector<std::pair<K, V>> pairs;

	pairs = std::vector<std::pair<K, V>>(vals.begin(), vals.end());
	return (encode_status_entry(pairs, type));
}

static inline bool
check_status_entry_type(const status_entry_encval &encval, EncodedType type)
{
	if (encval.empty()) {
		warnx("missing type for status entry; expected %d",
		    (uint8_t)type);
		return (false);
	}

	if (encval.front() != (uint8_t)type) {
		warnx("bad type for status entry; expected %d, got %d",
		    (uint8_t)type, encval.front());
		return (false);
	}

	return (true);
}

static inline bool decode_status_entry(const status_entry_encval &encval,
    std::string &val, EncodedType type = EncodedType::String);
static inline bool decode_status_entry(const status_entry_encval &encval,
    uint64_t &val, EncodedType type = EncodedType::Unsigned);
static inline bool decode_status_entry(const status_entry_encval &encval,
    int64_t &val, EncodedType type = EncodedType::Signed);
static inline bool decode_status_entry(const status_entry_encval &encval,
    bool &val, EncodedType type = EncodedType::Bool);
template <typename T> static inline bool
decode_status_entry(const status_entry_encval &encval,
    std::vector<T> &vals, EncodedType type = EncodedType::List);
template <typename T> static inline bool
decode_status_entry(const status_entry_encval &encval,
    std::unordered_set<T> &vals, EncodedType type = EncodedType::Set);
template <typename ...Ts> static inline bool
decode_status_entry(const status_entry_encval &encval,
    std::tuple<Ts...> &vals, EncodedType type = EncodedType::Tuple);
template <typename T1, typename T2> static inline bool
decode_status_entry(const status_entry_encval &encval,
    std::pair<T1, T2> &vals, EncodedType type = EncodedType::Tuple);
template <typename K, typename V> static inline bool
decode_status_entry(const status_entry_encval &encval,
    std::unordered_map<K, V> &vals, EncodedType type = EncodedType::Map);

static inline bool
decode_status_entry(const status_entry_encval &encval, std::string &val,
    EncodedType type)
{
	if (!check_status_entry_type(encval, type))
		return (false);

	val = std::string(encval.begin() + 1, encval.end());
	return (true);
}

static inline bool
decode_status_entry(const status_entry_encval &encval, uint64_t &val,
    EncodedType type)
{
	uint64_t leval;

	if (!check_status_entry_type(encval, type))
		return (false);

	if (encval.size() != sizeof(leval) + 1) {
		warnx("bad length for unsigned status entry; "
		    "expected %zu, got %zu",
		    sizeof(leval) + 1, encval.size());
		return (false);
	}

	memcpy(&leval, encval.data() + 1, sizeof(leval));
	val = le64toh(leval);
	return (true);
}

static inline bool
decode_status_entry(const status_entry_encval &encval, int64_t &val,
    EncodedType type)
{
	uint64_t leval;

	if (!check_status_entry_type(encval, type))
		return (false);

	if (encval.size() != sizeof(leval) + 1) {
		warnx("bad length for signed status entry; "
		    "expected %zu, got %zu",
		    sizeof(leval) + 1, encval.size());
		return (false);
	}

	memcpy(&leval, encval.data() + 1, sizeof(leval));
	val = le64toh(leval);
	return (true);
}

static inline bool
decode_status_entry(const status_entry_encval &encval, bool &val,
    EncodedType type)
{
	uint64_t intval;

	if (!decode_status_entry(encval, intval, type))
		return (false);

	if (intval > 1) {
		warnx("could not decode out-of-range bool %" PRIu64, intval);
		return (false);
	}

	val = intval;
	return (true);
}

static inline bool
split_aggregate_encval(const status_entry_encval &encval,
    std::vector<status_entry_encval> &encvals)
{
	const uint8_t *b, *e, *p;
	uint64_t len;

	for (b = encval.data(), e = b + encval.size(), p = b + 1; p < e;
	    p += len) {
		if (size_t(e - p) < sizeof(len)) {
			warnx("missing value size in list");
			return (false);
		}
		memcpy(&len, p, sizeof(len));
		len = le64toh(len);
		p += sizeof(len);
		if (uint64_t(e - p) < len) {
			warnx("short value in list; "
			    "needed %" PRIu64 " bytes, have %td",
			    len, e - p);
			return (false);
		}
		encvals.emplace_back(p, p + len);
	}

	return (true);
}

template <typename T>
static inline bool
decode_status_entry(const status_entry_encval &encval,
    std::vector<T> &vals, EncodedType type)
{
	std::vector<status_entry_encval> encvals;
	T val;

	if (!check_status_entry_type(encval, type))
		return (false);

	if (!split_aggregate_encval(encval, encvals))
		return (false);

	for (const auto &enc : encvals) {
		if (!decode_status_entry(enc, val))
			return (false);
		vals.push_back(val);
	}

	return (true);
}

template <typename T>
static inline bool
decode_status_entry(const status_entry_encval &encval,
    std::unordered_set<T> &vals, EncodedType type)
{
	std::vector<T> vec;

	if (!decode_status_entry(encval, vec, type))
		return (false);

	vals = std::unordered_set<T>(vec.begin(), vec.end());
	return (true);
}

template <typename ...Ts, typename ...Vs>
static inline typename std::enable_if<sizeof...(Vs) == sizeof...(Ts), bool>::type
decode_append_status_tuple_field(
    const std::vector<status_entry_encval> &encvals __unused,
    std::tuple<Ts...> &vals, const Vs &...vs)
{
	vals = std::tuple<Ts...>(vs...);
	return (true);
}

template <typename ...Ts, typename ...Vs>
static inline typename std::enable_if<sizeof...(Vs) < sizeof...(Ts), bool>::type
decode_append_status_tuple_field(
    const std::vector<status_entry_encval> &encvals, std::tuple<Ts...> &vals,
    const Vs &...vs)
{
	typename std::tuple_element<sizeof...(Vs), std::tuple<Ts...>>::type v;

	if (!decode_status_entry(encvals[sizeof...(Vs)], v))
		return (false);

	return (decode_append_status_tuple_field(encvals, vals, vs..., v));
}

template <typename ...Ts>
static inline bool
decode_status_entry(const status_entry_encval &encval,
    std::tuple<Ts...> &vals, EncodedType type)
{
	std::vector<status_entry_encval> encvals;

	if (!check_status_entry_type(encval, type))
		return (false);

	if (!split_aggregate_encval(encval, encvals))
		return (false);

	if (encvals.size() != sizeof...(Ts)) {
		warnx("wrong number of tuple elements; expected %zu, got %zu",
		    sizeof...(Ts), encvals.size());
		return (false);
	}

	if (!decode_append_status_tuple_field(encvals, vals))
		return (false);

	return (true);
}

template <typename T1, typename T2>
static inline bool
decode_status_entry(const status_entry_encval &encval,
    std::pair<T1, T2> &vals, EncodedType type)
{
	std::tuple<T1, T2> tuple;

	if (!decode_status_entry(encval, tuple, type))
		return (false);

	vals = std::pair<T1, T2>(std::get<0>(tuple), std::get<1>(tuple));
	return (true);
}

template <typename K, typename V>
static inline bool
decode_status_entry(const status_entry_encval &encval,
    std::unordered_map<K, V> &vals, EncodedType type)
{
	std::vector<std::pair<K, V>> pairs;

	if (!decode_status_entry(encval, pairs, type))
		return (false);

	vals = std::unordered_map<K, V>(pairs.begin(), pairs.end());
	return (true);
}

template <typename T>
static inline void
add_status_entry(status_entries &entries, const std::string &key,
    const T &val)
{
	status_entry_encval encval;

	encval = encode_status_entry(val);
	entries[key] = encval;
}

static inline bool
get_status_entry_raw(status_entries &entries, const std::string &key,
    status_entry_encval &val)
{
	if (entries.find(key) == entries.end()) {
		warnx("missing %s in status", key.c_str());
		return (false);
	}

	val = entries[key];
	return (true);
}

template <typename T>
static inline bool
get_status_entry(status_entries &entries, const std::string &key,
    T &val)
{
	status_entry_encval encval;

	if (!get_status_entry_raw(entries, key, encval))
		return (false);

	if (!decode_status_entry(encval, val))
		return (false);

	return (true);
}

static inline bool
append_status_entry_to_string(std::string &result,
    const status_entry_encval &encval)
{
	std::vector<status_entry_encval> encvals, kv;
	char listb, liste;
	const char *sep;
	std::string s;
	uint64_t u64;
	int64_t i64;
	char *buf;
	int ret;
	bool b;

	if (encval.size() == 0) {
		warnx("missing type for status entry");
		return (false);
	}

	switch (encval.front()) {
	case (uint8_t)EncodedType::Signed:
		if (!decode_status_entry(encval, i64))
			return (false);
		buf = NULL;
		ret = asprintf(&buf, "%" PRId64, i64);
		goto common_asprintf;
	case (uint8_t)EncodedType::Unsigned:
		if (!decode_status_entry(encval, u64))
			return (false);
		buf = NULL;
		ret = asprintf(&buf, "%" PRIu64, u64);
		goto common_asprintf;
	case (uint8_t)EncodedType::Bool:
		if (!decode_status_entry(encval, b))
			return (false);
		result += b ? "true" : "false";
		break;
	case (uint8_t)EncodedType::String:
		if (!decode_status_entry(encval, s))
			return (false);
		result += "\"" + s + "\"";
		break;
	case (uint8_t)EncodedType::List:
		listb = '[';
		liste = ']';
		goto common_list;
	case (uint8_t)EncodedType::Set:
		listb = '{';
		liste = '}';
		goto common_list;
	case (uint8_t)EncodedType::Tuple:
		listb = '(';
		liste = ')';
		goto common_list;
	case (uint8_t)EncodedType::Map:
		if (!split_aggregate_encval(encval, encvals))
			return (false);
		result += "{";
		sep = "";
		for (const auto &entry : encvals) {
			result += sep;
			if (!check_status_entry_type(entry, EncodedType::Tuple))
				return (false);
			kv.clear();
			if (!split_aggregate_encval(entry, kv))
				return (false);
			if (kv.size() != 2) {
				warnx("wrong number of tuple elements for map; "
				    "expected 2, got %zu", kv.size());
				return (false);
			}
			if (!append_status_entry_to_string(result, kv[0]))
				return (false);
			result += ": ";
			if (!append_status_entry_to_string(result, kv[1]))
				return (false);
			sep = ", ";
		}
		result += "}";
		break;
	default:
		warnx("unknown type for status entry: %d", encval.front());
		return (false);

	common_list:
		if (!split_aggregate_encval(encval, encvals))
			return (false);
		result += listb;
		sep = "";
		for (const auto &entry : encvals) {
			result += sep;
			if (!append_status_entry_to_string(result, entry))
				return (false);
			sep = ", ";
		}
		result += liste;
		break;

	common_asprintf:
		if (ret < 0) {
			warn("asprintf");
			return (false);
		}
		result += buf;
		free(buf);
		break;
	}

	return (true);
}

static inline bool
status_entry_to_string(std::string &result, const status_entry_encval &encval)
{
	result = "";
	return (append_status_entry_to_string(result, encval));
}
