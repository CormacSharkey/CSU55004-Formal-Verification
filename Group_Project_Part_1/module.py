
def isPrefix(pre, str):
    if (len(pre) <= len(str)):
        str_slice = str[0:len(pre)]

        if (pre == str_slice):
            return True
    return False