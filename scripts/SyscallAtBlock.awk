#!/usr/bin/gawk

# Use this on the disassembler output to find a syscall. It takes a single
# argument "block" on the command line:
#
# Example:
#
#    smdis ~/program.sb | gawk -f SyscallAtBlock.awk -v block=374
#

function syscallArgParse(a) {
  return strtonum(substr(a, 15, 2) substr(a, 13, 2) substr(a, 11, 2) substr(a, 9, 2) substr(a, 7, 2) substr(a, 5, 2) substr(a, 3, 2) substr(a, 1, 2));
}

BEGIN {
  fail=0;
  haveSection=0;
  if (length(block)<=0) {
    print "Please provide variable \"block\"";
    fail=1;
  }
}

{
  if (haveSection==1) {
    if ($0!~/^  [[:xdigit:]]{8} U[[:xdigit:]]+S[[:xdigit:]]+\+[[:xdigit:]]{8}  /) {
      haveSection=0;
    } else if ($0~/syscall/) {
      split($2, o, "+");
      syscallArgs[strtonum("0x" o[2])]=syscallArgParse($4);
    }
  } else if (haveSection==2) {
    if ($0!~/^  [[:xdigit:]]+: /) {
      haveSection=0;
    } else {
      split($1, i, ":");
      binds[strtonum(i[1])]=$2;
    }
  }
  if (haveSection==0) {
    if ($0~/^Start of section .* \(TEXT\):/) {
      haveSection=1;
    } else if ($0~/^Start of section .* \(BIND\):/) {
      haveSection=2;
    }
  }
}

END {
  if (fail!=0)
    exit 1;

  if (length(syscallArgs[strtonum(block)])<=0) {
    print "No system call at block " block "!!!";
    exit 1;
  } else {
    print "System call at block " block " is bound to " binds[syscallArgs[strtonum(block)]];
  }
}
