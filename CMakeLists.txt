#
# Copyright (C) 2015 Cybernetica
#
# Research/Commercial License Usage
# Licensees holding a valid Research License or Commercial License
# for the Software may use this file according to the written
# agreement between you and Cybernetica.
#
# GNU Lesser General Public License Usage
# Alternatively, this file may be used under the terms of the GNU Lesser
# General Public License version 3 as published by the Free Software
# Foundation and appearing in the file LICENSE.LGPLv3 included in the
# packaging of this file.  Please review the following information to
# ensure the GNU Lesser General Public License version 3 requirements
# will be met: http://www.gnu.org/licenses/lgpl-3.0.html.
#
# For further information, please contact us at sharemind@cyber.ee.
#

CMAKE_MINIMUM_REQUIRED(VERSION 3.0)
PROJECT(SharemindSbDump VERSION 1.3.0 LANGUAGES "CXX")

INCLUDE("${CMAKE_CURRENT_SOURCE_DIR}/config.local" OPTIONAL)
INCLUDE("${CMAKE_CURRENT_BINARY_DIR}/config.local" OPTIONAL)

FIND_PACKAGE(SharemindCMakeHelpers 1.6 REQUIRED)


FIND_PACKAGE(LogHard 0.5.0 REQUIRED)
FIND_PACKAGE(SharemindCHeaders 1.3.0 REQUIRED)
FIND_PACKAGE(SharemindCxxHeaders 0.8.0 REQUIRED)
FIND_PACKAGE(SharemindLibExecutable 0.4.0 REQUIRED)
FIND_PACKAGE(SharemindLibVmi 0.4.0 REQUIRED)


# SbDump:
SharemindSetCxx14CompileOptions()
FILE(GLOB_RECURSE SharemindSbDump_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
FILE(GLOB_RECURSE SharemindSbDump_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/src/*.h")
SharemindAddExecutable(SbDump
    OUTPUT_NAME "sbdump"
    SOURCES
        ${SharemindSbDump_SOURCES}
        ${SharemindSbDump_HEADERS}
)
TARGET_COMPILE_DEFINITIONS(SbDump PRIVATE "_XOPEN_SOURCE=700")
TARGET_LINK_LIBRARIES(SbDump
    PRIVATE
        LogHard::LogHard
        Sharemind::CHeaders
        Sharemind::CxxHeaders
        Sharemind::LibExecutable
        Sharemind::LibVmi
    )


# SyscallAtBlock.awk:
INSTALL(FILES "${CMAKE_CURRENT_SOURCE_DIR}/scripts/SyscallAtBlock.awk"
        DESTINATION "bin"
        COMPONENT "bin")


# Packaging:
SharemindSetupPackaging()
SharemindAddComponentPackage("bin"
    NAME "sbdump"
    DESCRIPTION "Sharemind bytecode dumper"
    DEB_SECTION "net"
    DEB_DEPENDS
        "libloghard (>= 0.5.0)"
        "libsharemind-executable (>= 0.4.0)"
        "libsharemind-vmi (>= 0.4.0)"
        "libstdc++6 (>= 4.8.0)"
        "libc6 (>= 2.19)"
)
SharemindAddComponentPackage(debug
    NAME "sbdump-dbg"
    DESCRIPTION "Sharemind bytecode dumper debug symbols"
    DEB_SECTION "debug"
    DEB_DEPENDS "sbdump (= ${SharemindSbDump_DEB_bin_PACKAGE_VERSION})")
SharemindPackagingFinalize()
