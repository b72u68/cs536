method findFirstGreater (a: seq<int>, x: int) returns (i : int)
ensures (0 <= i < |a| ==> a[i] > x && forall j :: 0 <= j < i ==> a[j] <= x) && 
(i == |a| ==> forall j :: 0 <= j < |a| ==> a[j] <= x)
{
    i := 0;
    while (i < |a| && a[i] <= x)
    invariant (i <= |a| && forall j :: 0 <= j < i ==> a[j] <= x)
    {
        i := i + 1;
    }
}