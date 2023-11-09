#!/bin/sh
make && \
bin/parser ~/hello-world/target/debug/deps/hello_world*.ll 9 15
