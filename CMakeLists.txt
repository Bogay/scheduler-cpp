cmake_minimum_required(VERSION 3.0)
project(scheduler)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_STANDARD 99)
set(CMAKE_C_EXTENSIONS OFF)

include(FetchContent)

FetchContent_Declare(z3
        GIT_REPOSITORY https://github.com/Z3Prover/z3
        GIT_TAG        z3-4.12.1
)
FetchContent_MakeAvailable(z3)

include_directories( ${z3_SOURCE_DIR}/src/api )
add_executable(sched src/main.c)
target_include_directories(sched PRIVATE ${Z3_C_INCLUDE_DIRS})
target_link_libraries(sched libz3)

add_executable(sim src/sim.c)
target_link_libraries(sim m)
