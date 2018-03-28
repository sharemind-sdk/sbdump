/*
 * Copyright (C) 2015 Cybernetica
 *
 * Research/Commercial License Usage
 * Licensees holding a valid Research License or Commercial License
 * for the Software may use this file according to the written 
 * agreement between you and Cybernetica.
 *
 * GNU Lesser General Public License Usage
 * Alternatively, this file may be used under the terms of the GNU Lesser
 * General Public License version 3 as published by the Free Software
 * Foundation and appearing in the file LICENSE.LGPLv3 included in the
 * packaging of this file.  Please review the following information to
 * ensure the GNU Lesser General Public License version 3 requirements
 * will be met: http://www.gnu.org/licenses/lgpl-3.0.html.
 *
 * For further information, please contact us at sharemind@cyber.ee.
 */

#include <algorithm>
#include <fcntl.h>
#include <cassert>
#include <cinttypes>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <LogHard/Backend.h>
#include <LogHard/Logger.h>
#include <LogHard/CFileAppender.h>
#include <limits>
#include <memory>
#include <sharemind/Concat.h>
#include <sharemind/Exception.h>
#include <sharemind/ExceptionMacros.h>
#include <sharemind/FileDescriptor.h>
#include <sharemind/codeblock.h>
#include <sharemind/IntegralComparisons.h>
#include <sharemind/likely.h>
#include <sharemind/libexecutable/libexecutable.h>
#include <sharemind/libexecutable/libexecutable_0x0.h>
#include <sharemind/libvmi/instr.h>
#include <sharemind/PotentiallyVoidTypeInfo.h>
#include <sharemind/ScopeExit.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <type_traits>
#include <unistd.h>


namespace {

bool fullNames = false;

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused"
#pragma GCC diagnostic ignored "-Wunused-function"
#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-member-function"
#endif
SHAREMIND_DECLARE_EXCEPTION_NOINLINE(sharemind::Exception, Exception);
SHAREMIND_DEFINE_EXCEPTION_NOINLINE(sharemind::Exception,, Exception);
#define DEFINE_EXCEPTION(name, ...) \
    SHAREMIND_DECLARE_EXCEPTION_CONST_MSG_NOINLINE(Exception, \
                                                   name ## Exception); \
    SHAREMIND_DEFINE_EXCEPTION_CONST_MSG_NOINLINE(Exception,, \
                                                  name ## Exception, \
                                                  __VA_ARGS__)

SHAREMIND_DECLARE_EXCEPTION_CONST_STDSTRING_NOINLINE(Exception,
                                                     ParseErrorException);
SHAREMIND_DEFINE_EXCEPTION_CONST_STDSTRING_NOINLINE(Exception,,
                                                    ParseErrorException);
DEFINE_EXCEPTION(InvalidInputFile, "Invalid input file!")
DEFINE_EXCEPTION(NoCodeSection, "No code section!")
DEFINE_EXCEPTION(InvalidHeader, "Invalid header!")
DEFINE_EXCEPTION(InvalidInstruction, "Invalid instruction!")
DEFINE_EXCEPTION(InvalidArguments, "Invalid arguments!")
DEFINE_EXCEPTION(DuplicatePdBind, "Duplicate protection domain binding!")
#ifdef __clang__
#pragma clang diagnostic pop
#endif
#pragma GCC diagnostic pop

constexpr std::size_t extraPadding[8] = { 0u, 7u, 6u, 5u, 4u, 3u, 2u, 1u };

void printSpacedHex(void const * data, std::size_t size) {
    if (size <= 0u)
        return;
    auto * c = static_cast<char const *>(data);
    std::printf("%02x", static_cast<unsigned>(*c));
    while (--size)
        std::printf(" %02x", static_cast<unsigned>(*++c));
}

void printNormalHex(void const * data, std::size_t size) {
    for (auto * c = static_cast<unsigned char const *>(data); size; ++c, --size)
        std::printf("%02x", static_cast<unsigned>(*c));
}

void printHex(void const * data,
              void const * pos,
              std::size_t size,
              std::size_t const ui,
              std::size_t const si)
{
    auto * p = static_cast<unsigned char const *>(pos);
    std::size_t offset = 0u;
    auto realOffset =
            static_cast<std::size_t>(
                p - static_cast<unsigned char const *>(data));
    std::printf("  %08zx U%zxS%zx+%08zx  ", realOffset, ui, si, offset);
    while (size-- > 0u) {
        std::printf("%02x ", static_cast<unsigned>(*p++));
        offset++;
        realOffset++;
        if ((offset % 16u) == 0u) {
            std::printf("\n  %08zx U%zxS%zx+%08zx  ", realOffset, ui, si, offset);
        } else if ((offset % 8u) == 0u) {
            std::putc(' ', stdout);
        }
    }
}

void addCodeSection(void const * data,
                    void const * pos,
                    std::size_t const size,
                    std::size_t const ui,
                    std::size_t const si)
{
    assert(data <= pos);
    auto realOffset = static_cast<std::size_t>(sharemind::ptrDist(data, pos));

    auto * c = static_cast<SharemindCodeBlock const *>(pos);

    /* Initialize instructions hashmap: */
    for (std::size_t i = 0u; i < size; realOffset += sizeof(SharemindCodeBlock))
    {
        std::printf("  %08zx U%zxS%zx+%08zx  ", realOffset, ui, si, i);

        auto const & cm = sharemind::instructionCodeMap();
        auto const instrIt = cm.find(c[i].uint64[0]);
        if (instrIt == cm.end()) {
            std::puts("<invalid instruction>\n");
            throw InvalidInstructionException();
        }
        auto const & instr = instrIt->second;
        if (fullNames) {
            std::fputs(instr.fullName, stdout);
            std::putc(' ', stdout);
        } else {
            // Only strip first component:
            auto const end = instr.fullName + instr.fullNameSize;
            auto name = std::find(instr.fullName, end, '.');
            assert(name != end);
            ++name;
            assert(*name);
            std::fputs(name, stdout);
            std::putc(' ', stdout);
        }

        i++;
        for (std::size_t j = 0u; j < instr.numArgs; j++, i++) {
            std::putc(' ', stdout);
            if (i >= size) {
                std::printf(" <too few arguments (need %zx)>\n", instr.numArgs);
                throw InvalidArgumentsException();
            }
            printNormalHex(&c[i].uint64[0], 8u);
        }
        std::putc('\n', stdout);
    }
    std::putc('\n', stdout);
}

#define RP_RETURN_ERR(e,p) \
    do { \
        ParseErrorException locationException( \
            sharemind::concat("Parse error at offset ", \
                              sharemind::ptrDist(data, (p)))); \
        try { \
            throw e ## Exception(); \
        } catch (...) { \
            std::throw_with_nested(std::move(locationException)); \
        } \
    } while (false)

bool readProgram(void const * const data, std::size_t const dataSize) {
    assert(data);

    if (dataSize < sizeof(SharemindExecutableCommonHeader))
        RP_RETURN_ERR(InvalidHeader, data);

    SharemindExecutableCommonHeader ch;
    if (SharemindExecutableCommonHeader_read(data, &ch)
        != SHAREMIND_EXECUTABLE_READ_OK)
        RP_RETURN_ERR(InvalidHeader, data);

    if (ch.fileFormatVersion > 0u)
        /** \todo new error code? */
        RP_RETURN_ERR(InvalidHeader, data);

    void const * pos =
            sharemind::ptrAdd(data, sizeof(SharemindExecutableCommonHeader));

    SharemindExecutableHeader0x0 h;
    if (SharemindExecutableHeader0x0_read(pos, &h)
        != SHAREMIND_EXECUTABLE_READ_OK)
        RP_RETURN_ERR(InvalidHeader, pos);

    pos = sharemind::ptrAdd(pos, sizeof(SharemindExecutableHeader0x0));

    static char const LU_NAME[33] = "Linking Unit";
    char unitTypeRaw[33];
    unitTypeRaw[32] = '\0';
    for (std::size_t ui = 0; ui <= h.numberOfUnitsMinusOne; ui++) {
        SharemindExecutableUnitHeader0x0 uh;
        if (SharemindExecutableUnitHeader0x0_read(pos, &uh)
            != SHAREMIND_EXECUTABLE_READ_OK)
            RP_RETURN_ERR(InvalidHeader, pos);

        std::memcpy(unitTypeRaw, uh.type, 32u);
        std::printf("Start of unit %zx (", ui);
        if (std::memcmp(LU_NAME, unitTypeRaw, 32u) == 0u) {
            std::printf("%s):\n\n", unitTypeRaw);
        } else {
            printSpacedHex(unitTypeRaw, 32u);
            std::puts("):\n");
        }

        char sectionTypeRaw[33];
        sectionTypeRaw[32] = '\0';
        pos = sharemind::ptrAdd(pos, sizeof(SharemindExecutableUnitHeader0x0));
        for (std::size_t si = 0u; si <= uh.sectionsMinusOne; si++) {
            SharemindExecutableSectionHeader0x0 sh;
            if (SharemindExecutableSectionHeader0x0_read(pos, &sh)
                != SHAREMIND_EXECUTABLE_READ_OK)
                RP_RETURN_ERR(InvalidHeader, pos);

            std::memcpy(sectionTypeRaw, sh.type, 32u);
            pos = sharemind::ptrAdd(pos,
                                    sizeof(SharemindExecutableSectionHeader0x0));

            SHAREMIND_EXECUTABLE_SECTION_TYPE sectionType =
                    SharemindExecutableSectionHeader0x0_type(&sh);

            static_assert(std::numeric_limits<decltype(sh.length)>::max()
                          <= std::numeric_limits<std::size_t>::max(), "");

#define PRINT_SECTION_HEADER \
    do { \
        std::printf("Start of section %zx (", si); \
        if (sectionType != SHAREMIND_EXECUTABLE_SECTION_TYPE_INVALID) { \
            std::fputs(sectionTypeRaw, stdout); \
        } else { \
            printSpacedHex(sectionTypeRaw, 32u); \
        } \
        std::printf(") of size %" PRIu32 ":\n", sh.length); \
    } while(false)

#define PRINT_DATASECTION \
    do { \
        PRINT_SECTION_HEADER; \
        printHex(data, pos, sh.length, ui, si); \
        std::puts("\n"); \
        pos = sharemind::ptrAdd(pos, sh.length + extraPadding[sh.length % 8]); \
    } while(false)
#define PRINT_BINDSECTION_CASE(utype) \
    case SHAREMIND_EXECUTABLE_SECTION_TYPE_ ## utype: { \
        PRINT_SECTION_HEADER; \
        if (sh.length <= 0) \
            break; \
        auto * endPos = sharemind::ptrAdd(pos, sh.length); \
        /* Check for 0-termination: */ \
        if (unlikely(*static_cast<char const *>(sharemind::ptrSub(endPos, 1))))\
            RP_RETURN_ERR(InvalidInputFile, pos); \
        std::size_t bi = 0u; \
        do { \
            if (static_cast<char const *>(pos)[0u] == '\0') \
                RP_RETURN_ERR(InvalidInputFile, pos); \
            std::printf("  %zx: %s\n", bi, static_cast<char const *>(pos)); \
            auto const len(std::strlen(static_cast<char const *>(pos))); \
            pos = sharemind::ptrAdd(pos, len + 1); \
            bi++; \
        } while (pos != endPos); \
        pos = sharemind::ptrAdd(pos, extraPadding[sh.length % 8]); \
        std::putc('\n', stdout); \
    } break;

            using U = std::underlying_type<decltype(sectionType)>::type;
            switch (static_cast<U>(sectionType)) {

                case SHAREMIND_EXECUTABLE_SECTION_TYPE_TEXT: {
                    PRINT_SECTION_HEADER;
                    addCodeSection(data, pos, sh.length, ui, si);

                    pos = sharemind::ptrAdd(pos,
                                            sh.length
                                            * sizeof(SharemindCodeBlock));
                } break;

                case SHAREMIND_EXECUTABLE_SECTION_TYPE_BSS: {
                    PRINT_SECTION_HEADER;
                    printf("BSS Section virtual size: %zx\n\n",
                           static_cast<std::size_t>(sh.length));
                } break;

                PRINT_BINDSECTION_CASE(BIND)
                PRINT_BINDSECTION_CASE(PDBIND)

                case SHAREMIND_EXECUTABLE_SECTION_TYPE_RODATA:
                case SHAREMIND_EXECUTABLE_SECTION_TYPE_DATA:
                default:
                    PRINT_DATASECTION;
                    break;
            }
        }
    }

    return true;
}

} // anonymous namespace

int main(int argc, char * argv[]) {
    LogHard::Logger const logger([]() {
        auto logBackend(std::make_shared<LogHard::Backend>());
        logBackend->addAppender(
                    std::make_shared<LogHard::CFileAppender>(stderr));
        return logBackend;
    }());

    try {
        /* Parse arguments */
        char const * inName = nullptr;
        for (int i = 1; i < argc; ++i) {
            if (argv[i][0] == '-') {
                if (argv[i][1] == 'f' && argv[i][2] == '\0') {
                    fullNames = true;
                } else {
                    logger.fatal() << "Invalid argument: " << argv[i];
                    return EXIT_FAILURE;
                }
            } else {
                if (inName) {
                    logger.fatal() << "Multiple input files specified!";
                    return EXIT_FAILURE;
                } else {
                    inName = argv[i];
                }
            }
        }
        if (!inName) {
            logger.fatal() << "No input files specified!";
            return EXIT_FAILURE;
        }

        /* Open input file: */
        sharemind::FileDescriptor inFileD(::open(inName, O_RDONLY));
        if (!inFileD.valid()) {
            logger.fatal() << "Error opening file \"" << inName
                           << "\" for reading!";
            return EXIT_FAILURE;
        }

        /* Determine input file size: */
        struct ::stat inFileStat;
        if (::fstat(inFileD.nativeHandle(), &inFileStat) != 0) {
            logger.fatal() << "Failed to fstat input file \"" << inName
                           << "\"!";
            return EXIT_FAILURE;
        }

        /* Memory map input file: */
        if (sharemind::integralGreater(inFileStat.st_size,
                                       std::numeric_limits<std::size_t>::max()))
        {
            logger.fatal() << "Input file \"" << inName << "\" too large!";
            return EXIT_FAILURE;
        }
        if (sharemind::integralNonPositive(inFileStat.st_size)) {
            logger.fatal() << "Input file \"" << inName
                           << "\" is empty!";
            return EXIT_FAILURE;
        }
        static_assert(std::numeric_limits<decltype(inFileStat.st_size)>::max()
                      < std::numeric_limits<std::size_t>::max(), "");
        auto const fileSize = static_cast<std::size_t>(inFileStat.st_size);

        auto * const map = ::mmap(nullptr,
                                  fileSize,
                                  PROT_READ,
                                  MAP_SHARED,
                                  inFileD.nativeHandle(),
                                  static_cast<::off_t>(0));
        if (map == MAP_FAILED) {
            logger.fatal() << "Failed to mmap the file \"" << inName << "\"!";
            return EXIT_FAILURE;
        }

        try {
            #ifdef __linux__
            /* Advise the OS that we plan to read the file sequentially: */
            (void) ::madvise(map, fileSize, MADV_SEQUENTIAL);
            #endif

            std::printf("Disassembly of Sharemind Executable \"%s\"\n\n", inName);

            auto const returnStatus = readProgram(map, fileSize);

            if (::munmap(map, fileSize) != 0)
                logger.error() << "Failed to munmap input file!";

            return returnStatus ? EXIT_SUCCESS : EXIT_FAILURE;
        } catch (...) {
            if (::munmap(map, fileSize) != 0)
                logger.error() << "Failed to munmap input file!";
            throw;
        }
    } catch (...) {
        logger.printCurrentException<LogHard::Priority::Fatal>();
        return EXIT_FAILURE;
    }
}
