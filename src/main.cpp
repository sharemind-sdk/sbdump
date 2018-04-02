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
#include <sharemind/EndianMacros.h>
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
        } else {
            // Only strip first component:
            auto const end = instr.fullName + instr.fullNameSize;
            auto name = std::find(instr.fullName, end, '.');
            assert(name != end);
            ++name;
            assert(*name);
            std::fputs(name, stdout);
        }

        i++;
        auto argPrefix = " 0x";
        for (std::size_t j = 0u; j < instr.numArgs; j++, i++) {
            std::fputs(argPrefix, stdout);
            argPrefix = ", 0x";
            if (i >= size) {
                std::printf(" <too few arguments (need %zx)>\n", instr.numArgs);
                throw InvalidArgumentsException();
            }
            auto const toPrint = sharemind::littleEndianToHost(c[i].uint64[0]);
            if (toPrint <= 0xff) {
                std::printf("%02" PRIx64, toPrint);
            } else if (toPrint <= 0xffff) {
                std::printf("%04" PRIx64, toPrint);
            } else if (toPrint <= 0xffffffff) {
                std::printf("%08" PRIx64, toPrint);
            } else {
                std::printf("%016" PRIx64, toPrint);
            }
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

    if (dataSize < sizeof(sharemind::ExecutableCommonHeader))
        RP_RETURN_ERR(InvalidHeader, data);

    sharemind::ExecutableCommonHeader ch;
    if (!ch.deserializeFrom(data))
        RP_RETURN_ERR(InvalidHeader, data);

    if (ch.fileFormatVersion() > 0u)
        /** \todo new error code? */
        RP_RETURN_ERR(InvalidHeader, data);

    void const * pos =
            sharemind::ptrAdd(data, sizeof(sharemind::ExecutableCommonHeader));

    sharemind::ExecutableHeader0x0 h;
    if (!h.deserializeFrom(pos))
        RP_RETURN_ERR(InvalidHeader, pos);

    pos = sharemind::ptrAdd(pos, sizeof(sharemind::ExecutableHeader0x0));

    for (std::size_t ui = 0; ui <= h.numberOfLinkingUnitsMinusOne(); ui++) {
        sharemind::ExecutableLinkingUnitHeader0x0 uh;
        if (!uh.deserializeFrom(pos))
            RP_RETURN_ERR(InvalidHeader, pos);

        std::printf("Start of unit %zx:\n\n", ui);

        pos = sharemind::ptrAdd(pos, sizeof(uh));
        for (std::size_t si = 0u; si <= uh.numberOfSectionsMinusOne(); si++) {
            sharemind::ExecutableSectionHeader0x0 sh;
            if (!sh.deserializeFrom(pos))
                RP_RETURN_ERR(InvalidHeader, pos);

            pos = sharemind::ptrAdd(pos, sizeof(sh));

            auto const sectionType = sh.type();
            auto const sectionSize = sh.size();

            static_assert(std::numeric_limits<decltype(sh)::SizeType>::max()
                          <= std::numeric_limits<std::size_t>::max(), "");

            using ST = decltype(sh.type());
            static auto const sectionTypeToString =
                    [](ST const sectionType_) noexcept {
                        switch (sectionType_) {
                        case ST::Bind: return "BIND";
                        case ST::Bss: return "BSS";
                        case ST::Data: return "DATA";
                        case ST::Debug: return "DEBUG";
                        case ST::PdBind: return "PDBIND";
                        case ST::RoData: return "RODATA";
                        case ST::Text: return "TEXT";
                        default: return "<INVALID>";
                        }
                    };
            auto const printSectionHeader =
                    [&si, &sectionType, &sectionSize]() noexcept {
                        static_assert(
                                std::is_same<decltype(sectionSize),
                                             std::uint32_t const>::value, "");
                        std::printf("Start of section %zx (%s) of size %" PRIu32
                                    ":\n",
                                    si,
                                    sectionTypeToString(sectionType),
                                    sectionSize);
                    };
#define PRINT_BINDSECTION_CASE(utype) \
    case ST::utype: { \
        printSectionHeader(); \
        if (sectionSize <= 0) \
            break; \
        auto * endPos = sharemind::ptrAdd(pos, sectionSize); \
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
        pos = sharemind::ptrAdd(pos, extraPadding[sectionSize % 8]); \
        std::putc('\n', stdout); \
    } break;

            switch (sectionType) {

                case ST::Text: {
                    printSectionHeader();
                    addCodeSection(data, pos, sh.size(), ui, si);

                    pos = sharemind::ptrAdd(pos,
                                            sh.size()
                                            * sizeof(SharemindCodeBlock));
                } break;

            case ST::Bss: {
                    printSectionHeader();
                    printf("BSS Section virtual size: %zx\n\n",
                           static_cast<std::size_t>(sh.size()));
                } break;

                PRINT_BINDSECTION_CASE(Bind)
                PRINT_BINDSECTION_CASE(PdBind)

            default:
                printSectionHeader();
                printHex(data, pos, sectionSize, ui, si);
                std::puts("\n");
                pos = sharemind::ptrAdd(pos,
                                        sectionSize
                                        + extraPadding[sectionSize % 8]);
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
