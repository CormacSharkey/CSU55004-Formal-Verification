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
