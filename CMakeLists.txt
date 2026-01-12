cmake_minimum_required(VERSION 3.26)
project(aatree_concurrent C)

set(CMAKE_C_STANDARD 11)

find_package(Threads REQUIRED)

add_executable(aatree_concurrent main.c aatree.c)
target_link_libraries(aatree_concurrent PRIVATE Threads::Threads)
