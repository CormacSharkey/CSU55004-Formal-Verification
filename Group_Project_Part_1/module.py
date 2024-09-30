
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

def haveCommonKSubstring(k, str1, str2):
    if (k <= len(str1) and k <= len(str2) and k>= 1):
        i = 0

        while (i < len(str1) -k + 1):
            found = isSubstring(str1[i:i+k-1])

            if (found):
                return True
            i += 1
    return False

def maxCommonSubstringLength(str1, str2):
    flag = True
    size = len(str1)

    while (size >= 0):
        flag = haveCommonKSubstring(size, str1, str2)

        if (flag):
            return size
        size -= 1
    return 0


print(isPrefix("str", "string"))
print(isPrefix("string", "str"))
print(isPrefix(" ", " "))