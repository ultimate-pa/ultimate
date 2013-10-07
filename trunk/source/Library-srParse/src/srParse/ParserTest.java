package srParse;

import java.io.StringReader;

import java_cup.runtime.Symbol;

public class ParserTest {
	static String scopes[] = {
		"Globally", "After a", "Before a", "Between a and b",
		"After a until b"
	};
	
	static String patterns[] = {
		"it is never the case that p holds",
		"it is always the case that p holds",
		"it is always the case that if p holds and is succeeded by q then r eventually holds after s",
		"it is always the case that if p holds then q holds as well",
		"transitions to states in which p holds occur at most twice",
		"P eventually holds"
		//"it is always the case that if p holds, then q.x previously held and was preceded by r.x"
	};
	
	static String test1 = "Globally, it is always the case that if p holds, then q.x previously held and was preceded by r.x.\n";
	
	public void testNewParser(String input) throws Exception {
		StringReader sr = new StringReader(input);
		ReqLexer lexer = new ReqLexer(sr);
		ReqParser parser = new ReqParser(lexer);
		
		Symbol goal = parser.parse();
		srParsePattern[] patterns = (srParsePattern[]) goal.value;
		
		for (srParsePattern pat : patterns) {
			System.out.println(pat);
		}
	}
	
	
	public static void main(String[] param) throws Exception {
		ParserTest test = new ParserTest();
		for (String s: scopes) { 
			for (String p: patterns) {
				test.testNewParser(s+", "+p+".\n");
			}
		}
	}
}	
