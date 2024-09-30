method isPrefix( pre:string, str:string) returns (res:bool)
{
    // check if the prefix is smaller than string, if so, continue
    if(|pre| <= |str|)
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
                return res;
            }
        }
        
    }
    // else, return false
    res := false;
    return res;
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    // ensures k <= |str1|
    // ensures k <= |str2|
{
    if (k <= |str1|) && ( k <= |str2|) && (k >= 1)
    {
        var i := 0;
        while i < (|str1| - k + 1)
        {
            found := isSubstring(str1[i..i+k-1], str2);
            if (found == true)
            {
                return found;
            }
            i := i + 1;
            // check the slice of str1 (sub) is in str2
            // if it is, return true
            // if not, check the next slice of str1  

        } 
    }
    found := false;
    return found;
    // is K > the|n l2|
    // is K > then len of str1 and 2  of str1 and 2 
    // then break
    //
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
{

    // get size of str
    // make a while loop and iterate till 0 or when have common k string returns a false
    //keep recording the size 
    //when it breaks return size as len
    var flag := true;
    var size := |str1|;


    while (size >=0 )
    {
        flag := haveCommonKSubstring(size,str1, str2);
        if (flag == true) {
            return size;
        }
        size:= size -1;
    }
    return 0; // size will therefor be 0 so nothing was in common

}