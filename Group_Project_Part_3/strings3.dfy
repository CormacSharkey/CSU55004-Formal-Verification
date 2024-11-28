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

	assert (( |pre| <= |str| && pre == str[..|pre|])==>(!true <==> isNotPrefixPred(pre,str)) && (true <==> isPrefixPred(pre,str))) &&
	 (!(|pre| <= |str| && pre == str[..|pre|]) ==> !((!true <==> isNotPrefixPred(pre,str)) && (true <==> isPrefixPred(pre,str)))) ;

	res:= false;
	
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
	(exists i :: 0 <= i <= |str| &&  isPrefixPred(sub, str[i..]))
}

predicate isNotSubstringPred(sub:string, str:string)
{
	(forall i :: 0 <= i <= |str| ==> isNotPrefixPred(sub,str[i..]))
}

lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}

method isSubstring(sub: string, str: string) returns (res:bool)
	ensures  res <==> isSubstringPred(sub, str)
	ensures !res <==> isNotSubstringPred(sub, str) // This postcondition follows from the above lemma.
{
	res := false;
	var i := 0;

	while i <= |str|
	invariant 0 <= i <= |str| + 1
	invariant res <==> (exists j :: 0 <= j < i <= |str|+1 && isPrefixPred(sub, str[j..]))
	invariant !res <==> (forall j :: 0 <= j < i <= |str|+1 ==> isNotPrefixPred(sub, str[j..]))
	{

		var yes := isPrefix(sub, str[i..]);
		if (yes == true) 
		{
			res := true;
		}

		else {
			res := res;
		}
		i := i + 1;
	}
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
	ensures !found <==> haveNotCommonKSubstringPred(k,str1,str2) // This postcondition follows from the above lemma.
{
	found := false;

    if (k <= |str1|) && ( k <= |str2|) && (k >= 0)
    {
        var i := 0;

        while i <= (|str1| - k)
		invariant 0 <= i <= |str1| - k + 1
		invariant found <==> (exists i1, j1 :: 0 <= i1 < i <= |str1|- k+1 && j1 == i1 + k && isSubstringPred(str1[i1..j1],str2))
		invariant !found <==> (forall i1, j1 :: 0 <= i1 < i <= |str1|- k+1  && j1 == i1 + k ==>  isNotSubstringPred(str1[i1..j1],str2))
        {
            var yes := isSubstring(str1[i..i+k], str2);

            if (yes == true)
            {
                found := true;
            }else{
				found := found;
			}
            i := i + 1;
        } 
    }
    return found;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
	requires (|str1| <= |str2|)
	ensures (forall k :: len < k <= |str1| ==> !haveCommonKSubstringPred(k,str1,str2))
	ensures haveCommonKSubstringPred(len,str1,str2)
{
    var size := |str1|;
	len := 0;

    while (size >= 0)
	invariant -1 <= size <= |str1|
    {
        var flag := haveCommonKSubstring(size,str1, str2);

        if (flag == true) {
            len := size;
        }
		else {
			len := len;
		}
        size := size - 1;
    }
	return len;
}
