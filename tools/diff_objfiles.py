#! /usr/bin/env python3

from pathlib import Path
import subprocess
import glob
import itertools
import sys

def shell_exec(command):
    return subprocess.run(command.split(), stdout=subprocess.PIPE).stdout.decode('utf-8')

def same_section(content1, content2, secname):
    if secname in content1 and secname in content2 and content1[secname] == content2[secname]:
        return True
    if secname in content1 and secname not in content2 and len(content1[secname]) == 0:
        return True
    if secname in content2 and secname not in content1 and len(content2[secname]) == 0:
        return True
    if secname not in content1 and secname not in content2:
        return True
    return False

def main():
    if len(sys.argv) != 2:
        print("Diff objfiles (version)")
        sys.exit(1)

    version = sys.argv[1]

    if version == "5.3":
        programs = ("cfe", "cc", "ugen")
        libs = ()
    elif version == "7.1":
        programs = ("as1", "cfe", "cc", "ugen")
        libs = ("libp", "mld")
    else:
        print("Version unrecognized")
        sys.exit(1)

    objfiles = [f.relative_to('build/src') for p in programs for f in (Path('build/src').glob(f'{version}/{p}/*.o'))]
    lib_objfiles = [f.relative_to('build/src') for p in libs for f in (Path('build/src').glob(f'{version}/{p}/*.o'))]
    sections = (".text", ".data", ".rodata")

    for name in objfiles:
        # object file names
        objfile_c = f"build/src/{name}"
        objfile_asm = f"build/asm/{name}"

        # object file sections
        readelf_c = shell_exec(f"mips-linux-gnu-readelf -S {objfile_c}")
        readelf_asm = shell_exec(f"mips-linux-gnu-readelf -S {objfile_asm}")

        #get sections content
        content_c = {}
        content_asm = {}
        for section in sections:
            for line in readelf_c.splitlines():
                if " " + section in line:
                    splitted_line = line[line.find(section):].split()
                    offset = int(splitted_line[3], 16)
                    size = int(splitted_line[4], 16)
                    content_c[section] = Path(objfile_c).read_bytes()[offset: offset + size]

            for line in readelf_asm.splitlines():
                if " " + section in line:
                    splitted_line = line[line.find(section):].split()
                    offset = int(splitted_line[3], 16)
                    size = int(splitted_line[4], 16)
                    content_asm[section] = Path(objfile_asm).read_bytes()[offset: offset + size]

            if not same_section(content_c, content_asm, section):
                print(f"[--] {name} {section} : compare build/src/{name}{section}.c.bin and build/src/{name}{section}.asm.bin")
                if section in content_c:
                    Path(f"build/src/{name}{section}.c.bin").write_bytes(content_c[section])
                if section in content_asm:
                    Path(f"build/src/{name}{section}.asm.bin").write_bytes(content_asm[section])

    for libname in lib_objfiles:
        #remove version from libname
        libname_mod = libname.relative_to(libname.parents[-2])

        # object file names
        objfile_c = f"build/src/{libname}"
        objfile_asm_list = [f"build/asm/{version}/{p}/{libname_mod}" for p in programs]
        objfile_asm_list = [o for o in objfile_asm_list if Path(o).exists()]

        for objfile_asm in objfile_asm_list:
            # object file sections
            readelf_c = shell_exec(f"mips-linux-gnu-readelf -S {objfile_c}")
            readelf_asm = shell_exec(f"mips-linux-gnu-readelf -S {objfile_asm}")

            #get sections content
            content_c = {}
            content_asm = {}
            for section in sections:
                for line in readelf_c.splitlines():
                    if " " + section in line:
                        splitted_line = line[line.find(section):].split()
                        offset = int(splitted_line[3], 16)
                        size = int(splitted_line[4], 16)
                        content_c[section] = Path(objfile_c).read_bytes()[offset: offset + size]

                for line in readelf_asm.splitlines():
                    if " " + section in line:
                        splitted_line = line[line.find(section):].split()
                        offset = int(splitted_line[3], 16)
                        size = int(splitted_line[4], 16)
                        content_asm[section] = Path(objfile_asm).read_bytes()[offset: offset + size]

                if not same_section(content_c, content_asm, section):
                    print(f"[--] {objfile_asm} {section} : compare build/src/{libname}{section}.c.bin and build/src/{libname}{section}.asm.bin")
                    if section in content_c:
                        Path(f"build/src/{libname}{section}.c.bin").write_bytes(content_c[section])
                    if section in content_asm:
                        Path(f"build/src/{libname}{section}.asm.bin").write_bytes(content_asm[section])



if __name__ == "__main__":
    main()
