#!/usr/bin/env python3

# https://tree-sitter.github.io/tree-sitter/playground
from tree_sitter import Language, Parser
from pathlib import Path
import os
import sys

class CodeQuery:
    _captures = []
    _i = 0
    _parsed = []
    _src = bytes("", 'utf-8')
    _parser = Parser()
    _tree = None
    _filename = ""
    _LANGUAGES_PATH = Path(os.path.abspath(os.path.dirname(__file__)), 'build/my-languages.so').as_posix()


    def _build_languages(self):
        Language.build_library(
            self._LANGUAGES_PATH,
            [
                Path(os.path.abspath(os.path.dirname(__file__)), 'tree-sitter-rust').as_posix(),
            ]
        )
    
    # Given a tree-sitter node, find its code text from the source file
    def _get_code_text(self, node):
        return str(self._src[node.start_byte:node.end_byte], 'utf-8')
        
    def set_file(self, filename):
        with open(filename) as f: self._src = bytes(f.read(), 'utf-8')
        self._tree = self._parser.parse(self._src)
        self._filename = filename

class RustCodeQuery(CodeQuery):
    def __init__(self, filename):
        self._build_languages()
        self.__RS_LANG = Language(self._LANGUAGES_PATH, 'rust')
        self._parser.set_language(self.__RS_LANG)
        self.set_file(filename)
        
    def _capture_unsafes(self):
        query = self.__RS_LANG.query("""
        (unsafe_block) @unsafe
        (function_item
            (function_modifiers)? @function-mods
        ) @function
        """)
        self._captures = query.captures(self._tree.root_node)

    def _parse_captures(self):
        self._i = 0
        self._parsed = []
        last_function = None
        for cap in self._captures:
            if cap[1] == 'unsafe':
                self._parsed.append(cap[0])
            elif cap[1] == 'function':
                last_function = cap[0]
            elif cap[1] == 'function-mods':
                if 'unsafe' in self._get_code_text(cap[0]):
                    self._parsed.append(last_function)
        
    def _offset_to_linum(self, offset):
        with open(self._filename, 'r') as f:
            s = f.read(offset)
            l = s.count('\n') + 1
        return l
        
    # Get all function signatures from given source code file
    def get_unsafe_locations(self):
        locations = []
        self._capture_unsafes()
        self._parse_captures()
        for par in self._parsed:
            locations.append((self._offset_to_linum(par.start_byte),
                              self._offset_to_linum(par.end_byte)))
            # print(self._get_code_text(par))
            # print(locations[-1])
        return locations

def get_rust_file_paths(root):
    return [path.as_posix() for path in Path(root).rglob('*.rs')]
            
if __name__ == '__main__':
    assert(len(sys.argv) >= 2)
    code_root = sys.argv[1]
    for code in get_rust_file_paths(code_root):
        queryer = RustCodeQuery(code)
        locations = queryer.get_unsafe_locations()
        if len(locations) > 0:
            print(code)
            for loc in locations:
                print(loc)
