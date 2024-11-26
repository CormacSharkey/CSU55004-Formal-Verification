predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && 
	pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	(|pre| > |str|) || 
	pre != str[..|pre|]
}

lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

method isPrefix(pre: string, str: string) returns (res:bool)
	ensures !res <==> isNotPrefixPred(pre,str)
	ensures  res <==> isPrefixPred(pre,str)
{
	// assert (|pre| <= |str| && |pre| >= 1 && |str| >= 1 && pre == str[..|pre|]) ==> (isPrefixPred(pre, str) && !isNotPrefixPred(pre, str)) 
    // && (!(|pre| <= |str| && |pre| >= 1 && |str| >= 1 && pre == str[..|pre|]) ==> (!isPrefixPred(pre, str) && isNotPrefixPred(pre, str)));

	assert (( |pre| <= |str| && pre == str[..|pre|])==>(!true <==> isNotPrefixPred(pre,str)) && (true <==> isPrefixPred(pre,str))) &&
	 (!(|pre| <= |str| && pre == str[..|pre|]) ==> !((!true <==> isNotPrefixPred(pre,str)) && (true <==> isPrefixPred(pre,str)))) ;
	res:= false;
	// check if the prefix is smaller than string, if so, continue
	assert ((|pre| <= |str|  && pre == str[..|pre|])==>(!true <==> isNotPrefixPred(pre,str)) && (true <==> isPrefixPred(pre,str))) 
	&& (!(|pre| <= |str| && pre == str[..|pre|]) ==> (!res <==> isNotPrefixPred(pre,str)) && (res <==> isPrefixPred(pre,str))) ;

	if(|pre| <= |str| && pre == str[..|pre|])
    {
        // store the prefix length slice of string
		assert (!true <==> isNotPrefixPred(pre,str)) && (true <==> isPrefixPred(pre,str)) ;
        res := true;
		assert (!res <==> isNotPrefixPred(pre,str)) && (res <==> isPrefixPred(pre,str)) ;

	}
	else {
		assert (!res <==> isNotPrefixPred(pre,str)) && (res <==> isPrefixPred(pre,str)) ;
		res := res;
		assert (!res <==> isNotPrefixPred(pre,str)) && (res <==> isPrefixPred(pre,str)) ;

	}
	assert (!res <==> isNotPrefixPred(pre,str)) && (res <==> isPrefixPred(pre,str)) ;
	return res;
}
predicate isSubstringPred(sub:string, str:string)
{
	(exists i :: 0 <= i < |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i < |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	// ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	res := false;
	var i := 0;
	var yes := false;

	// assert

	while i < |str|
	invariant i <= |str|
	invariant ((res==false) ==> isNotSubstringPred(sub, str))
	{

		yes := isPrefix(sub, str[i..]);
		// assert ((yes == true) ==> (i+1 <= |str|)) && ((yes == false) ==> ((i+1 <= |str|) && ((res == true) ==> isSubstringPred(sub, str))));
		if (yes == true) 
		{
			// assert (i+1 <= |str|);
			// assert ((i+1 <= |str|) && (true));
			// assert ((i+1 <= |str|) && ((true == false) ==> isNotSubstringPred(sub, str)));
			res := true;
			// assert ((i+1 <= |str|) && ((res == false) ==> isNotSubstringPred(sub, str)));
		}

		else {
			// assert ((i+1 <= |str|) && ((res == false) ==> isNotSubstringPred(sub, str)));
			res := res;
			// assert ((i+1 <= |str|) && ((res == false) ==> isNotSubstringPred(sub, str)));
		}
		// assert ((i+1 <= |str|) && ((res == false) ==> isNotSubstringPred(sub, str)));
		i := i + 1;
		// assert ((i <= |str|) && ((res == false) ==> isNotSubstringPred(sub, str)));
	}
	// assert ((i <= |str|) && ((res == false) ==> isNotSubstringPred(sub, str)) && !(i < |str|));
	// assert ((res == false) ==> isNotSubstringPred(sub, str)) && (i == |str|);
    return res;
}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	exists i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2)
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	forall i1, j1 :: 0 <= i1 <= |str1|- k && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2)
}

lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}

method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
	ensures found  <==>  haveCommonKSubstringPred(k,str1,str2)
	//ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
// if the length of string1 and string 2 is less than k and k is greater than 0, continue
    if (k <= |str1|) && ( k <= |str2|) && (k >= 1)
    {
        // counter variable
        var i := 0;

        // while the counter is less than the length of string1
        // store the result of isSubtring using a slice of string1 and string2
        // iterate through slices of string1, with each slice equal to k
        while i < (|str1| - k + 1)
        {
            // -1 might need to be added back - ask the Professor
            found := isSubstring(str1[i..i+k], str2);

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

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
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


