procedure test (a: int) returns (r:int)
{
	r := if a!=3 then 0 else 3;
	assert r != 3;
}