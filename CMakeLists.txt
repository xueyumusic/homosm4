
cmake_minimum_required(VERSION 3.5 FATAL_ERROR)

# Use -std=c++14 as default.
set(CMAKE_CXX_STANDARD 14)
# Disable C++ extensions
set(CMAKE_CXX_EXTENSIONS OFF)
# Require full C++ standard
set(CMAKE_CXX_STANDARD_REQUIRED ON)

project(homosm4 LANGUAGES CXX)

 find_package(helib 1.0.0 REQUIRED)
# find_package(helib 1.0.2 REQUIRED)

add_executable(homosm4 homo_sm4_decrypt.cpp originsm4.cpp)

target_link_libraries(homosm4 helib)
