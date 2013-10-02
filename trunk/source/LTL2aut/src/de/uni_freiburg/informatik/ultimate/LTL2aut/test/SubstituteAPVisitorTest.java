package de.uni_freiburg.informatik.ultimate.LTL2aut.test;

import java.io.InputStreamReader;
import java.util.HashMap;
import java.util.Map;

import org.apache.commons.io.IOUtils;

import de.uni_freiburg.informatik.ultimate.LTL2aut.Lexer;
import de.uni_freiburg.informatik.ultimate.LTL2aut.LexerAP;
import de.uni_freiburg.informatik.ultimate.LTL2aut.SubstituteAPVisitor;
import de.uni_freiburg.informatik.ultimate.LTL2aut.parser;
import de.uni_freiburg.informatik.ultimate.LTL2aut.parserAP;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AtomicProposition;
import junit.framework.TestCase;

public class SubstituteAPVisitorTest extends TestCase {

	
	public void  testAstSubstitution() throws Exception
	{
		String code = 
				"never \n"
			+ 	"	{\n"
			+ 	"	Node_1:\n"
			+ 	"		if\n"
			+ 	"		::  (a && (!b) && c) ->  goto bla\n"
			+	 "		:: 	(d && x) ->  goto blubber\n"
			+	 "		:: 	(1) ->  goto blubber\n"
			+	 "		:: 	(a) ->  goto glibber\n"
			+ 	"		fi;\n"
			+ 	"	bla:\n"
			+ 	"		skip\n"
			+ 	"}\n";
		InputStreamReader file = new InputStreamReader(IOUtils.toInputStream(code));		
	
		Lexer lexer = new Lexer(file);
		parser p = new parser(lexer);
		AstNode ast = (AstNode)p.parse().value;
		
		// pasrse aps
		String[] aps = {"a : x *4 + 2 >= y", "b : x > 2", "c : 1 = 1", "d : ding+dong = derp" };
		Map apmap= new HashMap<String,AstNode>();
		
		for (String ap: aps)
		{
			file = new InputStreamReader(IOUtils.toInputStream(ap));		
		
			LexerAP lexerAP = new LexerAP(file);
			parserAP pAP = new parserAP(lexerAP);
			AstNode nodea = (AstNode)pAP.parse().value;

			if (nodea instanceof AtomicProposition) 
				apmap.put(((AtomicProposition) nodea).getIdent(), nodea.getOutgoingNodes().get(0));	
		}
		
		SubstituteAPVisitor vis = new SubstituteAPVisitor(apmap, ast);
		
		String result = "never {"
				+ "Node_1:"
				+ "if"
				+ ":: (( (!x>2) && ( ( x * 4 ) + 2 )>=y && 1=1 ))-> goto bla"
				+ ":: ((x &&( ding + dong )=derp))-> goto blubber"
				+ ":: (true) -> goto blubber"
				+":: (( ( x * 4 ) + 2 )>=y) ->  goto glibber\n"
				+ "fi;"
				+ "bla:"
				+ "skip"
				+ "}";

		assertEquals(result.replaceAll("\\s", ""),ast.toString().replaceAll("\\s", ""));
	}
}
