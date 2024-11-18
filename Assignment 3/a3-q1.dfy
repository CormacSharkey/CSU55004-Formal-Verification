//predicate all numbers in s are unique
predicate Unique(s: seq<int>) {
	forall i, j :: (0 <= i < j < |s|) ==> (s[i] != s[j])
}
// all numbers in s1 appear at least twice in s2
predicate AtLeastTwice(s1: seq<int>, s2: seq<int>) {
	forall i :: 0 <= i < |s1| ==> exists j :: 0 <= j < |s2| && exists k  :: j < k < |s2| && s1[i] == s2[j] == s2[k]
}
// all numbers in s1 appear at most twice in s2
predicate AtMostTwice(s1: seq<int>, s2: seq<int>) {
	forall i :: 0 <= i < |s1| ==> !(exists j :: 0 <= j < |s2| && exists k  :: j < k < |s2| && exists l  :: k < l < |s2| && s1[i] == s2[j] == s2[k] == s2[l])
}
// all numbers in s1 appear exactly twice in s2
predicate ExactlyTwice(s1: seq<int>, s2: seq<int>) {
	AtLeastTwice(s1, s2) && AtMostTwice(s1, s2)
}
// all numbers in s1, if they do not appear in s2, then they also do not appear in s3
predicate Complex(s1: seq<int>, s2: seq<int>, s3: seq<int>) {
	forall i :: 0 <= i < |s1| && s1[i] !in s2 ==> s1[i] !in s3
}

method VerifyUnique() {
	var s0 :seq<int> := [];
	var s1 := [1];
	var s21 := [1, 2];
	assert s21[0] != s21[1];
	var s22 := [1, 1];
	assert s22[0] == s22[1];
	var s31 := [1, 2, 3];
	assert s31[0] != s31[1] && s31[1] != s31[2];
	var s32 := [1, 2, 1];
	assert s32[1] != s32[0] == s32[2];
	var s33 := [1, 1, 2];
	assert s33[1] == s33[0] != s33[2];
	var s34 := [1, 1, 1];
	assert s34[0] == s34[1] == s34[2];

	assert Unique(s0);
	assert Unique(s1);
	assert Unique(s21);
	assert !Unique(s22);
	assert Unique(s31);
	assert !Unique(s32);
	assert !Unique(s33);
	assert !Unique(s34);
}

method VerifyAtLeastTwice() {
	var s0 :seq<int> := [];
	var s1 := [1];
	var s21 := [1, 2];
	assert s21[0] != s21[1];
	var s22 := [1, 1];
	assert s22[0] == s22[1];
	var s31 := [1, 2, 3];
	assert s31[0] != s31[1] && s31[1] != s31[2];
	var s32 := [1, 2, 1];
	assert s32[1] != s32[0] == s32[2];
	var s33 := [1, 1, 2];
	assert s33[1] == s33[0] != s33[2];
	var s34 := [1, 1, 1];
	assert s34[0] == s34[1] == s34[2];

	assert AtLeastTwice(s0, s0); assert AtLeastTwice(s0, s1); 
	assert !AtLeastTwice(s1, s0); assert !AtLeastTwice(s1, s1); assert !AtLeastTwice(s1, s21); assert AtLeastTwice(s1, s22);
	assert !AtLeastTwice(s1, s31); assert AtLeastTwice(s1, s32); assert AtLeastTwice(s1, s33); assert AtLeastTwice(s1, s34);
	assert !AtLeastTwice(s21, s31); assert !AtLeastTwice(s21, s32); assert !AtLeastTwice(s21, s33); assert !AtLeastTwice(s21, s34);
	assert !AtLeastTwice(s22, s31); assert AtLeastTwice(s22, s32); assert AtLeastTwice(s22, s33); assert AtLeastTwice(s22, s34);
}

method VerifyAtMostTwice() {
	var s0 :seq<int> := [];
	var s1 := [1];
	var s21 := [1, 2];
	assert s21[0] != s21[1];
	var s22 := [1, 1];
	assert s22[0] == s22[1];
	var s31 := [1, 2, 3];
	assert s31[0] != s31[1] && s31[1] != s31[2];
	var s32 := [1, 2, 1];
	assert s32[1] != s32[0] == s32[2];
	var s33 := [1, 1, 2];
	assert s33[1] == s33[0] != s33[2];
	var s34 := [1, 1, 1];
	assert s34[0] == s34[1] == s34[2];

	assert AtMostTwice(s0, s0); assert AtMostTwice(s0, s1); assert AtMostTwice(s0, s21); 
	assert AtMostTwice(s1, s0); assert AtMostTwice(s1, s1); assert AtMostTwice(s1, s21); assert AtMostTwice(s1, s22);
	assert AtMostTwice(s1, s33); assert !AtMostTwice(s1, s34);
	assert AtMostTwice(s21, s0); assert AtMostTwice(s21, s1); assert AtMostTwice(s21, s21); assert AtMostTwice(s21, s22);
	assert AtMostTwice(s21, s33); assert !AtMostTwice(s21, s34);
	assert AtMostTwice(s22, s0); assert AtMostTwice(s22, s1); assert AtMostTwice(s22, s21); assert AtMostTwice(s22, s22);
	assert AtMostTwice(s22, s33); assert !AtMostTwice(s22, s34);
}

method VerifyExactlyTwice() {
	var s0 :seq<int> := [];
	var s1 := [1];
	var s21 := [1, 2];
	assert s21[0] != s21[1];
	var s22 := [1, 1];
	assert s22[0] == s22[1];
	var s31 := [1, 2, 3];
	assert s31[0] != s31[1] && s31[1] != s31[2];
	var s32 := [1, 2, 1];
	assert s32[1] != s32[0] == s32[2];
	var s33 := [1, 1, 2];
	assert s33[1] == s33[0] != s33[2];
	var s34 := [1, 1, 1];
	assert s34[0] == s34[1] == s34[2];

	assert ExactlyTwice(s0, s0); assert ExactlyTwice(s0, s1); assert ExactlyTwice(s0, s21); assert ExactlyTwice(s0, s32);
	assert !ExactlyTwice(s1, s0); assert !ExactlyTwice(s1, s1); assert !ExactlyTwice(s1, s21); assert ExactlyTwice(s1, s22);
	assert !ExactlyTwice(s1, s31); assert ExactlyTwice(s1, s32); assert !ExactlyTwice(s1, s34);
}	

method VerifyComplex() {
	var s0 :seq<int> := [];
	var s1 := [1];
	var s21 := [1, 2];
	var s22 := [1, 1];
	assert s22[0] == s22[1];
	var s23 := [2, 2];
	assert s23[0] == s23[1];
	var s31 := [1, 2, 3];
	var s32 := [2, 2, 3];
	var s33 := [3, 4, 5];

	assert Complex(s0, s0, s0); assert Complex(s0, s1, s0); assert Complex(s0, s21, s31);
	assert s21[0] == s1[0]; assert Complex(s1, s21, s1); assert Complex(s1, s21, s32);
	assert Complex(s22, s21, s32); assert Complex(s21, s22, s33);
	assert s21[1] == s31[1]; assert !Complex(s21, s22, s31);
	assert Complex(s21, s22, s33);
	assert s1[0] == s31[0]; assert s1[0] != s23[0]; assert !Complex(s1, s23, s31);

}