TARGET_EXEC:=interpreter
UNAME_S := $(shell uname -s)

ifeq ($(UNAME_S),Linux)
    CC=gcc
else ifeq ($(UNAME_S),Darwin)
    CC=clang
    ARCH = -arch x86_64
endif

BUILD_DIR:=build
SRC_DIRS:=main/src
EXCLUDES:=
SRCS:=main/src/main.c
OBJS:=$(SRCS:%=$(BUILD_DIR)/%.o)
DEPS:=$(OBJS:.o=.d)
# INC_DIRS:=include lib
# INC_DIRS += $(shell find $(INC_DIRS) -type d)
LIBS:=:runtime.a
INC_FLAGS:=#$(addprefix -I, $(INC_DIRS))
CPP_FLAGS:=$(INC_FLAGS) -MMD -MP
LDFLAGS:=$(addprefix -l, $(LIBS)) -L main/src/runtime
CFLAGS:=-Wall -Wextra -std=c11 -pedantic

debug: CXXFLAGS += -O0 -DDEBUG -g3
debug: LDFLAGS += -g
debug: CCFLAGS += -O0 -DDEBUG -g3
debug: $(BUILD_DIR)/$(TARGET_EXEC)

release: CXXFLAGS += -O3 -DNDEBUG
release: CCFLAGS += -O3 -DNDEBUG
release: $(BUILD_DIR)/$(TARGET_EXEC)

asan: CXXFLAGS += -fsanitize=address
asan: CCFLAGS += -fsanitize=address
asan: LDFLAGS += -fsanitize=address
asan: debug

ubsan: CXXFLAGS += -fsanitize=undefined
ubsan: CCFLAGS += -fsanitize=undefined
ubsan: LDFLAGS += -fsanitize=undefined
ubsan: debug

tsan: CXXFLAGS += -fsanitize=thread
tsan: CCFLAGS += -fsanitize=thread
tsan: LDFLAGS += -fsanitize=thread
tsan: debug

clangd: clean
	bear -- make

$(BUILD_DIR)/$(TARGET_EXEC): main/src/runtime $(OBJS)
	$(CC) $(OBJS) -o $@ $(LDFLAGS)

$(BUILD_DIR)/%.c.o: %.c
	mkdir -p $(dir $@)
	$(CC) $(CPP_FLAGS) $(CFLAGS) -c $< -o $@

clean:
	-rm -r $(BUILD_DIR)
-include $(DEPS)

.PHONY: clean
