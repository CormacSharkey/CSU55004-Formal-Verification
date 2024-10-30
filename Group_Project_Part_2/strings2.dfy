predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	!(|pre| <= |str|) || !(pre == str[..|pre|])
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}


predicate isSubstringPred(sub:string, str:string)
{
    exists i :: (|sub|<= |str| ) &&	0<= i < ((|str|-|sub|)+1) && isPrefixPred(sub,str[i..])
}

predicate isNotSubstringPred(sub:string, str:string)
{
    forall i :: !((|sub|<= |str| ) &&	0<= i < ((|str| - |sub|)+1) && isPrefixPred(sub,str[i..]))
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    exists i :: ((0 <= i < |str1| - k + 1) && ((k <= |str1|) && (k <= |str2|) && (k >= 1)) && isSubstringPred(str1[i..i+k], str2))
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    forall i :: !((0 <= i < |str1| - k + 1) && ((k <= |str1|) && (k <= |str2|) && (k >= 1)) && isSubstringPred(str1[i..i+k], str2))
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}
