llvm_map_components_to_libnames(llvm_libs bitwriter core ipo irreader instcombine instrumentation target linker analysis scalaropts support )
# file (GLOB SOURCES
#    *.cpp
# )
set (SRC_FILES
  main.cpp
)
add_executable(parser ${SRC_FILES})

target_link_libraries(parser ${SVF_LIB} ${llvm_libs})
target_link_libraries(parser ${Z3_LIBRARIES})
set_target_properties( parser PROPERTIES
                       RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
