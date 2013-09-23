package de.uni_freiburg.informatik.ultimate.LTL2aut.test;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.LTL2aut.WrapLTL2Never;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import junit.framework.TestCase;

public class PluginTest extends TestCase {
	
	public void testInvokeAutomatonBuilder() throws IOException, InterruptedException
	{
		WrapLTL2Never wrap = new WrapLTL2Never();
		String result = wrap.execLTLXBA("[] a");
		
		assertNotSame("", result);
	}
	
	
	public void testForumulaToAst()
	{
		WrapLTL2Never wrap = new WrapLTL2Never();
		
		AstNode ast = null;
		try {
			ast = wrap.ltl2Ast("[] a");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			assertTrue(false);
		}
		assertNotSame(null, ast);
	}

}
