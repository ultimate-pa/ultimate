/*
working example:

	terminating [ ] | nonterminating [+] | correct [+]
		String fileContent = "[](a)\n"
				+ "a: x = 1";
				
	terminating [ ] | nonterminating [+] | correct [+]
		String fileContent = "[](a)\n"
			+ "a: x > 1";
			
	terminating [+] | nonterminating [ ] | correct [+]
			String fileContent = "<>(a)\n"
				+ "a: x > 1";
				
	terminating [+] | nonterminating [ ] | correct [+]
		String fileContent = "<>[](a)\n"
			+ "a: x > 1";
*/


procedure ULTIMATE.start() returns()
{
	var x:int;
	havoc x;
    while(true){
		x := x +1;
  }
}