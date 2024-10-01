
def isPrefix(pre, str):
    if (len(pre) <= len(str) and len(pre) >= 1 and len(str) >= 1):
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
            i += 1
    return False

def haveCommonKSubstring(k, str1, str2):
    if (k <= len(str1) and k <= len(str2) and k>= 1):
        i = 0

        while (i < len(str1) -k + 1):
            found = isSubstring(str1[i:i+k-1], str2)

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
print(isPrefix("", ""))
print("\n")


print(isSubstring("str", "string"))
print(isSubstring("str", "substring"))
print(isSubstring("substring", "string"))
print(isSubstring("", ""))
print("\n")

print(haveCommonKSubstring(3, "str", "string"))
print(haveCommonKSubstring(5, "str", "string"))
print(haveCommonKSubstring(5, "string", "substring"))
print(haveCommonKSubstring(2, "", ""))
print(haveCommonKSubstring(5, "substring", "string"))
print(haveCommonKSubstring(3, "string", "str"))
print("\n")

print(maxCommonSubstringLength("string", "str"))
print(maxCommonSubstringLength("substring", "string"))
print(maxCommonSubstringLength("banana", "bananagun"))
print(maxCommonSubstringLength("banana", "bananagun"))
print(maxCommonSubstringLength("", ""))

