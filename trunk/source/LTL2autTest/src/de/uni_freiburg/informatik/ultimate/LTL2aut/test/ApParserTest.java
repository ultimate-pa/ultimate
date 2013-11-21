package de.uni_freiburg.informatik.ultimate.LTL2aut.test;

import java.io.InputStreamReader;




import junit.framework.TestCase;

import org.apache.commons.io.IOUtils;

import de.uni_freiburg.informatik.ultimate.LTL2aut.Lexer;
import de.uni_freiburg.informatik.ultimate.LTL2aut.LexerAP;
import de.uni_freiburg.informatik.ultimate.LTL2aut.parser;
import de.uni_freiburg.informatik.ultimate.LTL2aut.parserAP;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;

public class ApParserTest extends TestCase {
	
	public void testApParserMin() throws Exception
	{
	
		String code = "a : true";
		InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(code));		
	
		LexerAP lexer = new LexerAP(file);
		parserAP p = new parserAP(lexer);
		AstNode n = (AstNode)p.parse().value;
	
		assertEquals(code.replaceAll("\\s", "")
				, n.toString().replaceAll("\\s", ""));
	}

	public void testApParser() throws Exception
	{
	
		String code = "a : a *4 + -2 > y";
		InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(code));		
	
		LexerAP lexer = new LexerAP(file);
		parserAP p = new parserAP(lexer);
		AstNode n = (AstNode)p.parse().value;
	
		assertEquals("a:((a*4)+ -2)>y".replaceAll("\\s", "")
				, n.toString().replaceAll("\\s", ""));
	}
	
	@SuppressWarnings("static-access")
	public void testErrorCases() throws Exception{
		
		String[] errorStrings = new String[]{
				"a: tempIn >= 0 \n",
				"b: error = true",
		};
			
		for (String s: errorStrings)
		{
			InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(s));		
		
			LexerAP lexer = new LexerAP(file);
			parserAP p = new parserAP(lexer);
			AstNode n = (AstNode)p.parse().value;
		
			// just looking for parser errors with big input
			assertTrue(true);
		}	
	}
	
}
