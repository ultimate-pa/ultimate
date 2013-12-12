package de.uni_freiburg.informatik.ultimate.LTL2aut.test;

import java.io.InputStreamReader;

import junit.framework.TestCase;

import org.apache.commons.io.IOUtils;

import de.uni_freiburg.informatik.ultimate.LTL2aut.*;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.*;


public class ParserTest extends TestCase {
	
		//@TODO kommentare im code
	
		/*
		 * simple piece of code to catch basic grammar errors
		 */
		public void testBasicGrammarWithoutAlgebr() throws Exception
		{
			String code = 
						"never \n"
					+ 	"	{\n"
					+ 	"	Node_1:\n"
					+ 	"		if\n"
					+ 	"		::  (((a && (!b) && c) || ((!b) && c && d) || (!f))) ->  goto bla\n"
					+	 "		:: 	(d) ->  goto blubber\n"
					+ 	"		fi;\n"
					+ 	"	bla:\n"
					+ 	"		skip\n"
					+ 	"}\n";
			InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(code));		
	
			Lexer lexer = new Lexer(file);
			Parser p = new Parser(lexer);
			AstNode n = (AstNode)p.parse().value;
			
			System.out.println(n.toString());
	
			assertEquals(code.replaceAll("\\s", "")
					, n.toString().replaceAll("\\s", ""));
			
		}
		
		/*
		 * test bigger chunk of code without any logical formulas
		 */
		public void testBasicGrammarApOnly() throws Exception
		{
			String code = 
						"never \n"
					+ 	"	{\n"
					+ 	"	Node_1:\n"
					+ 	"		if\n"
					+ 	"		::	(a) -> goto marfnode\n"
					+ 	"		::  (d) -> goto bla\n"
					+ 	"		fi;\n"
					+ 	"	bla:\n"
					+ 	"		skip\n"
					+ 	"}\n";
			InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(code));		
	
			Lexer lexer = new Lexer(file);
			Parser p = new Parser(lexer);
			AstNode n = (AstNode)p.parse().value;
	
			assertEquals(code.replaceAll("\\s", "")
					, n.toString().replaceAll("\\s", ""));
			
		}
		
		/*
		 * test wheather the smallest possible piece of code returns the 
		 * correct parsetree
		 */
		public void testBasicNeverNodeParse() throws Exception
		{
			String code = 
					"never { \n"
				+ 	"	testlabel:\n"
				+ 	"	skip\n"
				+ 	"}";
		InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(code));		
	
		Lexer lexer = new Lexer(file);
		Parser p = new Parser(lexer);
		AstNode n = (AstNode)p.parse().value;
	
		assertEquals(code.replaceAll("\\s", "")
				, n.toString().replaceAll("\\s", ""));

	}

		/*
		 * Semicolons belong to if fi; not to the labeled block
		 * coments
		 */
		public void testCommentIgnoring() throws Exception
		{
			String code = "never {  /*  [] a  */ "
							+"accept_init: "
							+	"if "
							+	":: (a) -> goto accept_init "
							+	"fi; "
							+ "}";
		InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(code));		
	
		Lexer lexer = new Lexer(file);
		Parser p = new Parser(lexer);
		AstNode n = (AstNode)p.parse().value;
	
		//comments are not parsed!
		assertEquals(code.replace("/*  [] a  */", "").replaceAll("\\s", "")
				, n.toString().replaceAll("\\s", ""));

	}
		
		@SuppressWarnings("static-access")
		public void testErrorCases() throws Exception{
		
		String[] errorStrings = new String[]{
			"never { accept_init:	if	:: (!a) || (r) -> goto accept_init	:: (!p) || (!r && s) -> goto accept_S2	:: (!r) -> goto T0_S3	:: (!r && s) || (!p) -> goto T1_S4	:: (!r) -> goto T0_S5	fi;T0_S3:	if	:: (!r) -> goto T0_S3	:: (!r) -> goto T0_S10	:: (!r && s) -> goto accept_S2	:: (!r && s) -> goto T1_S11	fi;T0_S10:	if	:: (!r) -> goto T0_S10	:: (!r && s) -> goto T1_S11	fi;T1_S11:	if	:: (!p) || (!r && s) -> goto T1_S11	:: (!r) -> goto T1_S10	:: (r && !p) -> goto accept_S2	fi;T1_S10:	if	:: (!r) -> goto T1_S10	:: (!r && s) -> goto T1_S11	fi;accept_S2:	if	:: (!p) || (!r && s) -> goto accept_S2	:: (!p) || (!r && s) -> goto T1_S11	:: (!r) -> goto T0_S3	:: (!r) -> goto T0_S10	fi;T0_S5:	if	:: (!r) -> goto T0_S5	:: (!r && s) -> goto T1_S4	fi;T1_S4:	if	:: (!p) || (!r && s) -> goto T1_S4	:: (!r) -> goto T1_S5	:: (r) -> goto accept_init	fi;T1_S5:	if	:: (!r) -> goto T1_S5	:: (!r && s) -> goto T1_S4	fi;}",
			"never { /* !( <> b  ) */accept_init:	if	:: (!b) -> goto accept_init	fi;}",
			"never { /* !( []( !a -> <>[] b ) ) */T0_init:	if	:: (1) -> goto T1_S1	:: (!a) -> goto T0_S3	fi;T1_S1:	if	:: (1) -> goto T1_S1	:: (!a) -> goto accept_S3	fi;accept_S3:	if	:: (1) -> goto T0_S3	:: (!b) -> goto accept_S3	fi;T0_S3:	if	:: (1) -> goto T0_S3	:: (!b) -> goto accept_S3	fi;}"

		};
			
		for (String s: errorStrings)
		{
			InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(s));		
		
			Lexer lexer = new Lexer(file);
			Parser p = new Parser(lexer);
			AstNode n = (AstNode)p.parse().value;
		
			// just looking for Parser errors with big input
			assertTrue(true);
		}		

	}
		
}
