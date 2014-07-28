package de.uni_freiburg.informatik.ultimate.LTL2aut.test;

import java.io.IOException;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.LTL2aut.WrapLTL2Never;
import junit.framework.TestCase;

public class PluginTest extends TestCase {
	
	public void testInvokeAutomatonBuilder() throws IOException, InterruptedException
	{
		WrapLTL2Never wrap = new WrapLTL2Never(Logger.getRootLogger());
		String result = wrap.execLTLXBA("\"[] a\"");
		
		assertNotSame("", result);
	}
	

}
