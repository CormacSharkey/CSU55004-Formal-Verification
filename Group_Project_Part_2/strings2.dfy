// Predicate to check if pre is a prefix of str
predicate isPrefixPred(pre:string, str:string)
{
	(|pre| <= |str|) && (pre == str[..|pre|])
}

// Predicate to check if pre is not a prefix of str
predicate isNotPrefixPred(pre:string, str:string)
{
	!(|pre| <= |str|) || !(pre == str[..|pre|])
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}

// Predicate to check if sub is a substring of str
predicate isSubstringPred(sub:string, str:string)
{
    exists i :: ((|sub| <= |str|) && (0 <= i < ((|str| - |sub|)+1)) && (isPrefixPred(sub,str[i..])))
}

// Predicate to check if sub is not a substring of str
predicate isNotSubstringPred(sub:string, str:string)
{
    forall i :: !((|sub| <= |str| ) && (0 <= i < ((|str| - |sub|)+1)) && (isPrefixPred(sub,str[i..])))
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


// Hey Oisin, I think I've narrowed down the issue to being the str1[i..i+k]. Because it includes k, which is an outside variable and is not bounded, it means it isn't a trigger anymore.
// To fix it, we have to figure out a way to add a trigger or turn str1[i..i+k] into a trigger
// Might also have to ask the Professor about this

// // Predicate to check if str1 and str2 have a common substring of length k
// predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
// {
//     exists i :: ((0 <= i < |str1| - k + 1) && ((1 <= k <= |str1|) && (1 <= k <= |str2|)) && (isSubstringPred(str1[i..i+k], str2)))
// }

// // Predicate to check if str1 and str2 do not have a common substring of length k
// predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
// {
//     forall i :: !((0 <= i < |str1| - k + 1) && ((1 <= k <= |str1|) && (1 <= k <= |str2|)) && (isSubstringPred(str1[i..i+k], str2)))
// }

// Predicate to check if str1 and str2 have a common substring of length k
predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    exists i, j :: (((1 <= k <= |str1|) && (1 <= k <= |str2|)) && (0 <= i  < |str1| - k + 1)  && (j == i+k) && (isSubstringPred(str1[i..j], str2)))
}

// Predicate to check if str1 and str2 do not have a common substring of length k
predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
    forall i, j :: !(((1 <= k <= |str1|) && (1 <= k <= |str2|)) && (0 <= i < |str1| - k + 1) && (j == i+k) && (isSubstringPred(str1[i..j], str2)))
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==>  haveNotCommonKSubstringPred(k,str1,str2)
{}
