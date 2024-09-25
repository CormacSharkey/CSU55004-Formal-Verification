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
            return res;
        }
    }
    res := false;
    return res;
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
                return res;
            }
        }
        
    }
    res := false;
    return res;
}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    // ensures k <= |str1|
    // ensures k <= |str2|
{
    if (k <= |str1|) && ( k <= |str2|)
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