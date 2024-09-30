method isPrefix( pre:string, str:string) returns (res:bool)
{
    if(|pre| <= |str|) // if pre is smaller then str cont
    {
        // for the length of the pre string do: 
        // compare each slice to  see if they match

        // if they match continue 
        //else return false
        var str_slice := str[0..|pre|];
        if(pre == str_slice) // if the letters
        {
            res := true;
            return;
        }
    }
    res := false;
    return;
}

method isSubstring(sub: string, str: string) returns (res:bool)
{
    // var lenA := |sub|;
    // var lenB := |str|;

    if (|sub| <= |str|) // if sub is smaller than str cont 
    {    
        // get the difference of the two strings + 1 to determine the no. of iterations
        var dif := (|str| - |sub|) + 1;
        
        var i := 0;
        while i < dif
        {
            res := isPrefix(sub, str[i..]);
            i := i + 1;
            if res == true 
            {
                return;
            }
        }
        
    }
    res := false;
    return;
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
                return;
            }
            i := i + 1;
            // check the slice of str1 (sub) is in str2
            // if it is, return true
            // if not, check the next slice of str1  

        } 
    }
    found := false;
    return;
    // is K > the|n l2|
    // is K > then len of str1 and 2  of str1 and 2 
    // then break
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
{

    // get size of str
    // make a while loop and iterate till 0 or when have common k string returns a false
    //keep recording the size 
    //when it breaks return size as len
    var flag := false;
    var size := |str1|;


    while (size >=0 )
    {
        flag := haveCommonKSubstring(size, str1, str2);
        if (flag == true) {
            len := size;
            return;
        }
        size := size - 1;
    }
    len := 0;
    return; // size will therefor be 0 so nothing was in common
}

method Main() {
    
    var str1 := "hello world";
    var str2 := "world";
    var str3 := "earth";

    
}