cmake_minimum_required(VERSION 2.8)
project(hess_mt)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${PROJECT_SOURCE_DIR}/bin)
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${PROJECT_SOURCE_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${PROJECT_SOURCE_DIR}/lib)

set(CMAKE_C_FLAGS "-std=c11 -O3 -fPIC -Wno-int-conversion -Wno-incompatible-pointer-types -D LOG")

add_executable(hess_mt hess_mt.c tinycthread.c)