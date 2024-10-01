method isPrefix( pre:string, str:string) returns (res:bool)
{
    // check if the prefix is smaller than string, if so, continue
    if(|pre| <= |str| && |pre| >= 1 && |str| >= 1)
    {
        // store the prefix length slice of string
        var str_slice := str[0..|pre|];

        // if the prefix matches the slice of string, return true
        if(pre == str_slice)
        {
            res := true;
            return res;
        }
    }
    // else, return false
    res := false;
    return res;
}

method isSubstring(sub: string, str: string) returns (res:bool)
{
    // check if the substring is smaller than string, if so, continue
    if (|sub| <= |str|)
    {    
        // store the difference of the lengths of substring and string, plus 1 (no. of iterations)
        var diff := (|str| - |sub|) + 1;
        
        // counter variable
        var i := 0;

        // while the counter is less than the diff
        // store the result of isPrefix with substring and a slice of string
        // each iteration, the front of string is sliced off
        while i < diff
        {
            res := isPrefix(sub, str[i..]);

            // increment counter
            i := i + 1;

            // if the result of isPrefix is true, return true
            if (res == true) 
            {
                return;
            }
        }
        
    }
    // else, return false
    res := false;
    return;
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
{
    // if the length of string1 and string 2 is less than k and k is greater than 0, continue
    if (k <= |str1|) && ( k <= |str2|) && (k >= 1)
    {
        // counter variable
        var i := 0;

        // while the counter is less than the length of string1
        // store the result of isSubtring using a slice of string1 and string2
        // iterate through slices of string1, with each sixe equal to k
        while i < (|str1| - k + 1)
        {
            found := isSubstring(str1[i..i+k-1], str2);

            // if the result is true, return true
            if (found == true)
            {
                return;
            }

            // increment the counter
            i := i + 1;
        } 
    }
    // else, return false
    found := false;
    return;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
{
    // flag and size of string1 vars
    var flag := true;
    var size := |str1|;

    // while the size is greater than -1
    while (size >= 0)
    {
        // set flag as the result of haveCommonKSubstring call with size parameter
        flag := haveCommonKSubstring(size,str1, str2);

        // if flag is true, return true
        if (flag == true) {
            len := size;
            return;
        }
        //decrement the size
        size := size - 1;
    }
    // else, return 0 (no common string)
    len := 0;
    return;

}