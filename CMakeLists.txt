#
# This file is a part of the Sharemind framework.
# Copyright (C) Cybernetica AS
#
# All rights are reserved. Reproduction in whole or part is prohibited
# without the written consent of the copyright owner. The usage of this
# code is subject to the appropriate license agreement.
#

CMAKE_MINIMUM_REQUIRED(VERSION "2.8.12")
PROJECT("SHAREMIND_SBDUMP" "C")

INCLUDE("${CMAKE_CURRENT_SOURCE_DIR}/config.local" OPTIONAL)
INCLUDE("${CMAKE_CURRENT_BINARY_DIR}/config.local" OPTIONAL)

FIND_PACKAGE(SharemindLibexecutable REQUIRED)
FIND_PACKAGE(SharemindLibvmi REQUIRED)
FIND_PACKAGE(SharemindVmGlobals REQUIRED)

INCLUDE_DIRECTORIES(
    ${SharemindLibexecutable_INCLUDE_DIRS}
    ${SharemindLibvmi_INCLUDE_DIRS}
    ${SharemindVmGlobals_INCLUDE_DIRS}
)

ADD_COMPILE_OPTIONS(
    "-std=c99" "-O2" "-fwrapv" "-Wall" "-Wextra" "-Wunused" "-Wabi"
    "-Wstrict-aliasing=1" "-Wbad-function-cast" "-Wformat" "-Wswitch-default"
    "-Wfloat-equal" "-Wshadow" "-Wpointer-arith" "-Wcast-qual"
    "-Wstrict-prototypes" "-Wconversion" "-Wsign-conversion" "-Wunused-macros"
    "$<$<NOT:$<STREQUAL:$<CONFIGURATION>,Release>>:-fno-omit-frame-pointer>"
    "$<$<STREQUAL:$<CONFIGURATION>,Release>:-DNDEBUG>"
    "$<$<STREQUAL:$<CONFIGURATION>,Release>:-fomit-frame-pointer>"
)

INCLUDE(CheckCCompilerFlag)
FUNCTION(CHECK_ADD_COMPILER_FLAG flag)
    STRING(SUBSTRING "${flag}" 1 -1 FlagName)
    CHECK_C_COMPILER_FLAG("${flag}" C_COMPILER_HAS_${FlagName}_FLAG)
    IF(C_COMPILER_HAS_${FlagName}_FLAG)
        ADD_COMPILE_OPTIONS("${flag}")
    ENDIF()
ENDFUNCTION()
CHECK_ADD_COMPILER_FLAG("-Weverything")
CHECK_ADD_COMPILER_FLAG("-Wlogical-op")

ADD_DEFINITIONS(
    ${SharemindLibexecutable_DEFINITIONS}
    ${SharemindLibvmi_DEFINITIONS}
    ${SharemindVmGlobals_DEFINITIONS}
    "-D__STDC_LIMIT_MACROS" "-D_XOPEN_SOURCE=700"
)

################################################################################
# sbdump
################################################################################

FILE(GLOB_RECURSE SHAREMIND_SBDUMP_SOURCES
     "${CMAKE_CURRENT_SOURCE_DIR}/src/*.c")
FILE(GLOB_RECURSE SHAREMIND_SBDUMP_HEADERS
     "${CMAKE_CURRENT_SOURCE_DIR}/src/*.h")
ADD_CUSTOM_TARGET("include_sbdump_headers_in_IDE"
                  SOURCES ${SHAREMIND_SBDUMP_HEADERS})

ADD_EXECUTABLE("sbdump" ${SHAREMIND_SBDUMP_SOURCES})
TARGET_LINK_LIBRARIES("sbdump"
                      ${SharemindLibexecutable_LIBRARIES}
                      ${SharemindLibvmi_LIBRARIES})

INSTALL(TARGETS "sbdump"
        RUNTIME DESTINATION "bin")


################################################################################
# scripts
################################################################################

INSTALL(FILES "${CMAKE_CURRENT_SOURCE_DIR}/scripts/SyscallAtBlock.awk"
        DESTINATION "bin")
