function sum(n){
  assume(n > 0);
  var r = 0;
  var i = n;
  while (0 < i) {
    invariant(0 < n);
    invariant(0 <= i);
    invariant(r + i == n);
    r = r + 1;
    i = i - 1;
  }
  assert (i == 0);
  assert (n == r);
  assert (0 <  r);
}
