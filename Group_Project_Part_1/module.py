
def isPrefix(pre, str):
    if (len(pre) <= len(str)):
        str_slice = str[0:len(pre)]

        if (pre == str_slice):
            return True
    return False

def isSubstring(sub, str):
    if (len(sub) <= len(str)):
        diff = (len(str)-len(sub)) + 1
        i = 0

        while (i<diff):
            result = isPrefix(sub, str[i:])
            if (result):
                return True
    return False

