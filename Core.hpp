#ifndef CORE_HPP
#define CORE_HPP

#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

#define PANIC(format, ...) \
fprintf(stderr, format "\n", ##__VA_ARGS__); \
fprintf(stderr, "in function: %s\nat: %s %d", __func__, __FILE__, __LINE__); \
fflush(stderr); \
exit(-1)

#define TODO(format, ...) PANIC(format, ##__VA_ARGS__)

#define REQUIRE(condition, format, ...) \
do { \
if (!(condition)) { \
PANIC("condition failed: %s" format, #condition, ##__VA_ARGS__); \
} \
} while (false)

#define ASSERT(condition, format, ...) REQUIRE(condition, format, ##__VA_ARGS__)

#define BOOL_TO_STRING(val) val ? "true" : "false"

#define PRINT(format, ...) \
fprintf(stdout, format "\n", ##__VA_ARGS__); \
fflush(stdout)

#define PRINT_ERR(format, ...) \
fprintf(stderr, format "\n", ##__VA_ARGS__); \
fflush(stderr)

#ifndef NDEBUG
#define LOG(format, ...) \
PRINT(format, ##__VA_ARGS__)
#else
#define LOG(format, ...) do {} while(false)
#endif

#endif //CORE_HPP
