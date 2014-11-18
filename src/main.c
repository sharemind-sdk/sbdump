/*
 * This file is a part of the Sharemind framework.
 * Copyright (C) Cybernetica AS
 *
 * All rights are reserved. Reproduction in whole or part is prohibited
 * without the written consent of the copyright owner. The usage of this
 * code is subject to the appropriate license agreement.
 */

#include <assert.h>
#include <fcntl.h>
#include <inttypes.h>
#include <sharemind/codeblock.h>
#include <sharemind/likely.h>
#include <sharemind/libexecutable/libexecutable.h>
#include <sharemind/libexecutable/libexecutable_0x0.h>
#include <sharemind/libvmi/instr.h>
#include <sharemind/static_assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>


SHAREMIND_STATIC_ASSERT(sizeof(off_t) <= sizeof(size_t));

extern bool fullNames;
bool fullNames = false;

#define PARSE_ERROR_ENUM \
    ((PARSE_OK, = 0)) \
    ((PARSE_ERROR_OUT_OF_MEMORY,)) \
    ((PARSE_ERROR_INVALID_INPUT_FILE,)) \
    ((PARSE_ERROR_NO_CODE_SECTION,)) \
    ((PARSE_ERROR_INVALID_HEADER,)) \
    ((PARSE_ERROR_INVALID_INSTRUCTION,)) \
    ((PARSE_ERROR_INVALID_ARGUMENTS,)) \
    ((PARSE_ERROR_DUPLICATE_PDBIND,))
SHAREMIND_ENUM_CUSTOM_DEFINE(ParseError, PARSE_ERROR_ENUM);
SHAREMIND_ENUM_DECLARE_TOSTRING(ParseError);
SHAREMIND_ENUM_CUSTOM_DEFINE_TOSTRING(ParseError, PARSE_ERROR_ENUM)

static const size_t extraPadding[8] = { 0u, 7u, 6u, 5u, 4u, 3u, 2u, 1u };

void printSpacedHex(const void * data, const size_t size);
void printSpacedHex(const void * data, const size_t size) {
    if (size <= 0u)
        return;
    const char * c = (const char *) data;
    printf("%02x", c[0u]);
    for (size_t i = 1u; i < size; i++)
        printf(" %02x", c[i]);
}

void printNormalHex(const void * data, const size_t size);
void printNormalHex(const void * data, const size_t size) {
    const char * c = (const char *) data;
    for (size_t i = 0u; i < size; i++)
        printf("%02x", c[i]);
}

void printHex(const void * data,
              const void * pos,
              size_t size,
              const size_t ui,
              const size_t si);
void printHex(const void * data,
              const void * pos,
              size_t size,
              const size_t ui,
              const size_t si)
{
    const char * p = ((const char *) pos);
    size_t offset = 0u;
    size_t realOffset = (size_t) (p - ((const char *) data));
    printf("  %08zx U%zxS%zx+%08zx  ", realOffset, ui, si, offset);
    while (size-- > 0u) {
        printf("%02x ", (unsigned) *p++);
        offset++;
        realOffset++;
        if ((offset % 16u) == 0u) {
            printf("\n  %08zx U%zxS%zx+%08zx  ", realOffset, ui, si, offset);
        } else if ((offset % 8u) == 0u) {
            printf(" ");
        }
    }
}

ParseError addCodeSection(const void * data,
                          const void * pos,
                          const size_t size,
                          const size_t ui,
                          const size_t si);
ParseError addCodeSection(const void * data,
                          const void * pos,
                          const size_t size,
                          const size_t ui,
                          const size_t si)
{
    size_t realOffset = (size_t) (((const char *) pos) - ((const char *) data));

    const SharemindCodeBlock * c = (const SharemindCodeBlock *) pos;

    /* Initialize instructions hashmap: */
    for (size_t i = 0u; i < size; realOffset += sizeof(SharemindCodeBlock)) {
        printf("  %08zx U%zxS%zx+%08zx  ", realOffset, ui, si, i);

        const SharemindVmInstruction * const instr =
                sharemind_vm_instruction_from_code(c[i].uint64[0]);
        if (!instr) {
            printf("<invalid instruction>\n");
            return PARSE_ERROR_INVALID_INSTRUCTION;
        }
        printf("%s ", fullNames
                      ? instr->fullName
                      : sharemind_vm_instruction_fullname_to_name(
                                instr->fullName));

        i++;
        for (size_t j = 0u; j < instr->numArgs; j++, i++) {
            printf(" ");
            if (i + j >= size) {
                printf(" <invalid arguments (need %zx)>\n", instr->numArgs);
                return PARSE_ERROR_INVALID_ARGUMENTS;
            }
            printNormalHex(&c[i].uint64[0], 8u);
        }
        printf("\n");
    }
    return PARSE_OK;
}

#define RPRETURN(e,p) \
    do { \
        if ((e) == PARSE_OK) \
            return true; \
        fprintf(stderr, "Parse error %s at offset %tx\n", \
                ParseError_toString((e)), \
                ((const char *)((p))) - ((const char *)(data))); \
        return false; \
    } while (false)

bool readProgram(const void * const data, const size_t dataSize);
bool readProgram(const void * const data, const size_t dataSize) {
    assert(data);

    if (dataSize < sizeof(SharemindExecutableCommonHeader))
        RPRETURN(PARSE_ERROR_INVALID_HEADER, data);

    SharemindExecutableCommonHeader ch;
    if (SharemindExecutableCommonHeader_read(data, &ch)
        != SHAREMIND_EXECUTABLE_READ_OK)
        RPRETURN(PARSE_ERROR_INVALID_HEADER, data);

    if (ch.fileFormatVersion > 0u)
        RPRETURN(PARSE_ERROR_INVALID_HEADER, data); /** \todo new error code? */


    const void * pos =
            ((const uint8_t *) data) + sizeof(SharemindExecutableCommonHeader);

    SharemindExecutableHeader0x0 h;
    if (SharemindExecutableHeader0x0_read(pos, &h)
        != SHAREMIND_EXECUTABLE_READ_OK)
        RPRETURN(PARSE_ERROR_INVALID_HEADER, pos);

    pos = ((const uint8_t *) pos) + sizeof(SharemindExecutableHeader0x0);

    static const char LU_NAME[33] = "Linking Unit";
    char unitTypeRaw[33];
    unitTypeRaw[32] = '\0';
    for (size_t ui = 0; ui <= h.numberOfUnitsMinusOne; ui++) {
        SharemindExecutableUnitHeader0x0 uh;
        if (SharemindExecutableUnitHeader0x0_read(pos, &uh)
            != SHAREMIND_EXECUTABLE_READ_OK)
            RPRETURN(PARSE_ERROR_INVALID_HEADER, pos);

        memcpy(unitTypeRaw, uh.type, 32u);
        printf("Start of unit %zx (", ui);
        if (memcmp(LU_NAME, unitTypeRaw, 32u) == 0u) {
            printf("%s):\n\n", unitTypeRaw);
        } else {
            printSpacedHex(unitTypeRaw, 32u);
            printf("):\n\n");
        }

        char sectionTypeRaw[33];
        sectionTypeRaw[32] = '\0';
        pos = ((const uint8_t *) pos)
              + sizeof(SharemindExecutableUnitHeader0x0);
        for (size_t si = 0u; si <= uh.sectionsMinusOne; si++) {
            SharemindExecutableSectionHeader0x0 sh;
            if (SharemindExecutableSectionHeader0x0_read(pos, &sh)
                != SHAREMIND_EXECUTABLE_READ_OK)
                RPRETURN(PARSE_ERROR_INVALID_HEADER, pos);

            memcpy(sectionTypeRaw, sh.type, 32u);
            pos = ((const uint8_t *) pos)
                  + sizeof(SharemindExecutableSectionHeader0x0);

            SHAREMIND_EXECUTABLE_SECTION_TYPE sectionType =
                    SharemindExecutableSectionHeader0x0_type(&sh);

#if SIZE_MAX < UINT32_MAX
            if (unlikely(sh.length > SIZE_MAX))
                RPRETURN(PARSE_ERROR_OUT_OF_MEMORY, pos);
#endif

#define PRINT_SECTION_HEADER \
    do { \
        printf("Start of section %zx (", si); \
        if (sectionType != SHAREMIND_EXECUTABLE_SECTION_TYPE_INVALID) { \
            printf("%s", sectionTypeRaw); \
        } else { \
            printSpacedHex(sectionTypeRaw, 32u); \
        } \
        printf(") of size %" PRIu32 ":\n", sh.length); \
    } while(false)

#define PRINT_DATASECTION \
    do { \
        PRINT_SECTION_HEADER; \
        printHex(data, pos, sh.length, ui, si); \
        printf("\n\n"); \
        pos = ((const uint8_t *) pos) \
              + sh.length \
              + extraPadding[sh.length % 8]; \
    } while(false)
#define PRINT_BINDSECTION_CASE(utype) \
    case SHAREMIND_EXECUTABLE_SECTION_TYPE_ ## utype: { \
        PRINT_SECTION_HEADER; \
        if (sh.length <= 0) \
            break; \
        const char * endPos = ((const char *) pos) + sh.length; \
        /* Check for 0-termination: */ \
        if (unlikely(*(endPos - 1))) \
            RPRETURN(PARSE_ERROR_INVALID_INPUT_FILE, pos); \
        size_t bi = 0u; \
        do { \
            if (((const char *) pos)[0u] == '\0') \
                RPRETURN(PARSE_ERROR_INVALID_INPUT_FILE, pos); \
            printf("  %zx: %s\n", bi, (const char *) pos); \
            pos = ((const char *) pos) + strlen((const char *) pos) + 1; \
            bi++; \
        } while (pos != endPos); \
        pos = ((const char *) pos) + extraPadding[sh.length % 8]; \
        printf("\n"); \
    } break;

            SHAREMIND_STATIC_ASSERT(sizeof(sectionType) <= sizeof(int));
            switch ((int) sectionType) {

                case SHAREMIND_EXECUTABLE_SECTION_TYPE_TEXT: {
                    PRINT_SECTION_HEADER;
                    const ParseError r =
                            addCodeSection(data, pos, sh.length, ui, si);
                    if (r != PARSE_OK)
                        RPRETURN(r, pos);

                    pos = ((const uint8_t *) pos)
                          + sh.length * sizeof(SharemindCodeBlock);
                } break;

                case SHAREMIND_EXECUTABLE_SECTION_TYPE_BSS: {
                    PRINT_SECTION_HEADER;
                    printf("BSS Section virtual size: %zx\n\n",
                           (size_t) sh.length);
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

    return PARSE_OK;
}

int main(int argc, char * argv[]) {
    const char * inName = NULL;
    /*const char * outName = NULL;*/
    char activeOpt = '\0';
    int inFileD;
    struct stat inFileStat;
    size_t fileSize;
    void * map;
    int returnStatus;

    /* Parse arguments */
    for (int i = 1; i < argc; i++) {
        switch (activeOpt) {
            case '\0':
                if (argv[i][0] == '-') {
                    if (argv[i][1] == 'f' && argv[i][2] == '\0') {
                        fullNames = true;
                    } else {
                        fprintf(stderr,
                                "Error: Invalid argument: %s\n",
                                argv[i]);
                        returnStatus = EXIT_FAILURE;
                        goto main_fail_1;
                    }
                } else {
                    if (inName != NULL) {
                        fprintf(stderr,
                                "Error: Multiple input files specified!\n");
                        returnStatus = EXIT_FAILURE;
                        goto main_fail_1;
                    } else {
                        inName = argv[i];
                    }
                }
                break;
            default:
                abort();
        }
    }
    if (activeOpt != '\0') {
        fprintf(stderr, "Error: Argument expected!\n");
        returnStatus = EXIT_FAILURE;
        goto main_fail_1;
    }
    if (inName == NULL) {
        fprintf(stderr, "Error: No input files specified!\n");
        returnStatus = EXIT_FAILURE;
        goto main_fail_1;
    }

    /* Open input file: */
    inFileD = open(inName, O_RDONLY);
    if (inFileD == -1) {
        fprintf(stderr, "Error opening file \"%s\" for reading!\n", inName);
        returnStatus = EXIT_FAILURE;
        goto main_fail_1;
    }

    /* Determine input file size: */
    if (fstat(inFileD, &inFileStat) != 0) {
        fprintf(stderr, "Error: Failed to fstat input file \"%s\"!\n", inName);
        returnStatus = EXIT_FAILURE;
        goto main_fail_2;
    }

    /* Memory map input file: */
    if (((uintmax_t) inFileStat.st_size) > SIZE_MAX) {
        fprintf(stderr, "Error: Input file \"%s\" too large!\n", inName);
        returnStatus = EXIT_FAILURE;
        goto main_fail_2;
    }
    if (((uintmax_t) inFileStat.st_size) <= 0u) {
        fprintf(stderr, "Error: Input file \"%s\" is empty!\n", inName);
        returnStatus = EXIT_FAILURE;
        goto main_fail_2;
    }
    fileSize = (size_t) inFileStat.st_size;

    map = mmap(0, fileSize, PROT_READ, MAP_SHARED, inFileD, 0);
    if (map == MAP_FAILED) {
        fprintf(stderr, "Error: Failed to mmap the file \"%s\"!\n", inName);
        returnStatus = EXIT_FAILURE;
        goto main_fail_2;
    }

#ifdef __USE_BSD
    /* Advise the OS that we plan to read the file sequentially: */
    (void) madvise(map, fileSize, MADV_SEQUENTIAL);
#endif

    printf("Disassembly of Sharemind Executable \"%s\"\n\n", inName);

    returnStatus = readProgram(map, fileSize) ? EXIT_SUCCESS : EXIT_FAILURE;

    if (munmap(map, fileSize) != 0)
        fprintf(stderr, "Error: Failed to munmap input file!\n");

main_fail_2:

    if (close(inFileD))
        fprintf(stderr, "Error: Failed to close input file!\n");

main_fail_1:

    return returnStatus;
}
