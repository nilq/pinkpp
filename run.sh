#! /bin/sh
cargo run -- src/test.pnk --print-mir --print-asm -o test.s || exit
gcc test.s -o test || exit
rm test.s
./test
echo $?
