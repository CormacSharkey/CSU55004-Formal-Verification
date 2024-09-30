import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: module_

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def isPrefix(pre, str):
        res: bool = False
        if (len(pre)) <= (len(str)):
            d_0_str__slice_: _dafny.Seq
            d_0_str__slice_ = _dafny.SeqWithoutIsStrInference((str)[0:len(pre):])
            if (pre) == (d_0_str__slice_):
                res = True
                res = res
                return res
        res = False
        res = res
        return res
        return res

    @staticmethod
    def isSubstring(sub, str):
        res: bool = False
        if (len(sub)) <= (len(str)):
            d_0_dif_: int
            d_0_dif_ = ((len(str)) - (len(sub))) + (1)
            d_1_i_: int
            d_1_i_ = 0
            while (d_1_i_) < (d_0_dif_):
                out0_: bool
                out0_ = default__.isPrefix(sub, _dafny.SeqWithoutIsStrInference((str)[d_1_i_::]))
                res = out0_
                d_1_i_ = (d_1_i_) + (1)
                if (res) == (True):
                    res = res
                    return res
        res = False
        res = res
        return res
        return res

    @staticmethod
    def haveCommonKSubstring(k, str1, str2):
        found: bool = False
        if (((k) <= (len(str1))) and ((k) <= (len(str2)))) and ((k) >= (1)):
            d_0_i_: int
            d_0_i_ = 0
            while (d_0_i_) < (((len(str1)) - (k)) + (1)):
                out0_: bool
                out0_ = default__.isSubstring(_dafny.SeqWithoutIsStrInference((str1)[d_0_i_:((d_0_i_) + (k)) - (1):]), str2)
                found = out0_
                if (found) == (True):
                    found = found
                    return found
                d_0_i_ = (d_0_i_) + (1)
        found = False
        found = found
        return found
        return found

    @staticmethod
    def maxCommonSubstringLength(str1, str2):
        len: int = int(0)
        d_0_flag_: bool
        d_0_flag_ = True
        d_1_size_: int
        d_1_size_ = len(str1)
        while (d_1_size_) >= (0):
            out0_: bool
            out0_ = default__.haveCommonKSubstring(d_1_size_, str1, str2)
            d_0_flag_ = out0_
            if (d_0_flag_) == (True):
                len = d_1_size_
                return len
            d_1_size_ = (d_1_size_) - (1)
        len = 0
        return len
        return len

