
// PART I)
// S = [1,2,3]
// x = 2
// Flag | I |  
//   F | 0 |  
//   T | 1 |  
//   T | 2 |  
// ITER2
// x = 4
// Flag | I |  
//    F | 0 |  
//    F | 1 |  
//    F | 2 | 
// Above we see two possible iterations of this code. what the code is doing is if x is contained 
// inside the arry s, it will return true. if it is not it will return false

// PART II)
predicate Pfalse(s: seq<int>,x:int,i:int){
forall j::0 <= j< i <= |s|  ==>  s[j] != x
}

// PART III)
// The invarients for this while loop is:
// i <= |s| && (flag == false) ==> Pfalse(s,x,i)
// to get the final post condition we add the negation of the while loop 
// (i <= |s|) && ((flag == false) ==> Pfalse(s, x, i)) && !(i < |s|)
// this can be simplified to as if i <= |s| and i cannot be < |s| therefore i == |s| (bounds): 
// (flag ==false) ==>Pfalse(s,x,|s|);

// PART IV)
method Ccode(s:seq<int>, x:int)returns (flag:bool)
{
    assert(0 <= |s|)&&((false == false) ==> Pfalse(s, x, 0) );
    flag := false;
    assert(0 <= |s|)&&((flag == false) ==> Pfalse(s, x, 0) );
    var i:=0;
    assert(i <= |s|)&&((flag == false) ==> Pfalse(s, x, i) );
    while (i < |s|)
    invariant (i <= |s|)
    invariant (!flag ==> Pfalse(s,x,i))
    {
        assert( (i <= |s|)&&((flag == false) ==> Pfalse(s, x, i)) && (i<|s|));
        assert(((i+1)<= |s|) && ((flag == false) ==> Pfalse(s, x, i)));
        assert(((i+1)<= |s|)
        &&  ((x !=s[i]) ==> ((flag == false) ==> (Pfalse(s, x, i)&&(x !=s[i])))));
        assert(((i+1)<= |s|)
        &&  ((x !=s[i]) ==> ((flag == false) ==> Pfalse(s, x, i+1))));
        assert(((i+1)<= |s|)
        &&  ((x !=s[i]) ==> (i+1 <=|s|) && ((flag == false) ==> Pfalse(s, x, i+1))));
        assert (((x == s[i]) ==> ((i+1)<= |s|))
        && ((x !=s[i]) ==> (i+1 <=|s|) && ((flag == false) ==> Pfalse(s, x, i+1))));
        assert (((x == s[i]) ==> ((i+1)<= |s|))
        && (!(x ==s[i]) ==> (i+1 <=|s|) && ((flag == false) ==> Pfalse(s, x, i+1))));
        if (x==s[i])
        {
        assert (i+1 <= |s|);
        assert (i+1 <= |s|)&&(true);
        assert (i+1 <= |s|)&&( false ==> Pfalse(s, x, i+1));
        assert (i+1 <= |s|)&&((true == false) ==> Pfalse(s, x, i+1));
            flag := true;
        } else 
        {
        assert (i+1 <= |s|)&&((flag == false) ==> Pfalse(s, x, i+1));
            flag := flag;
        assert (i+1 <= |s|)&&((flag == false) ==> Pfalse(s, x, i+1));
        }
        assert (i+1 <= |s|)&&((flag == false) ==> Pfalse(s, x, i+1));
        i := i +1;
      assert (i <= |s|)&&((flag == false) ==> Pfalse(s, x, i));
    }
assert (i <= |s|) && ((flag == false) ==> Pfalse(s, x, i)) && !(i < |s|); // postcondition of loop
assert (flag ==false) ==>Pfalse(s,x,|s|);
}