method isPrefix( pre:string, str:string) returns (res:bool)
{
    if(|pre| <= |str|) // if pre is smaller then str cont
    {
        // for the lengeth of the pre string do: 
        // compare each slice to  see if they match

        // if they dmatch continue 
        //else return false
        var str_slice := str[0..|pre|];
        if(pre == str_slice) // if the letters
        {
            return res:= 1;
        } 
    }
}