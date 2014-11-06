package de.uni_freiburg.informatik.ultimate.LTL2aut.test;

import junit.framework.TestCase;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.*;

public class AstTest extends TestCase {
	
	public void testNeverStatement()
	{
		NeverStatement ns = new NeverStatement();
		assertEquals("never {\n}", ns.toString());
	}
	
	public void testLabledBlockStatement()
	{
		LabeledBlock ns = new LabeledBlock(new Name("testinput"));
		assertEquals("testinput:\n\n", ns.toString());
	}
	
	public void testChildRelation()
	{
		NeverStatement ns = new NeverStatement();
		LabeledBlock lb = new LabeledBlock(new Name("testinput"));
		ns.addOutgoing(lb);
		
		assertEquals("never {\ntestinput:\n\n}", ns.toString() );
	}
	
	public void testAndOperator()
	{
		BinaryOperator a = new BinaryOperator(BinaryType.and);
		a.addOutgoing(new Name("a"));
		a.addOutgoing(new Name("b"));
		
		assertEquals("( a && b )", a.toString() );
		
		a.addOutgoing(new Name("c"));
		a.addOutgoing(new Name("d"));
		
		assertEquals("( a && b && c && d )", a.toString() );
	}
	
	public void testOrOperator()
	{
		BinaryOperator a = new BinaryOperator(BinaryType.or);
		a.addOutgoing(new Name("a"));
		a.addOutgoing(new Name("b"));
		
		assertEquals("( a || b )", a.toString() );
		
		a.addOutgoing(new Name("c"));
		a.addOutgoing(new Name("d"));
		
		assertEquals("( a || b || c || d )", a.toString() );
	}
	
	public void testAddOperator()
	{
		BinaryOperator a = new BinaryOperator(BinaryType.plus);
		a.addOutgoing(new Name("a"));
		a.addOutgoing(new Name("b"));
		
		assertEquals("( a + b )", a.toString() );
		
		a.addOutgoing(new Name("c"));
		a.addOutgoing(new Name("d"));
		
		assertEquals("( a + b + c + d )", a.toString() );
	}
	
	public void testMinusOperator()
	{
		BinaryOperator a = new BinaryOperator(BinaryType.minus);
		a.addOutgoing(new Name("a"));
		a.addOutgoing(new Name("b"));
		
		assertEquals("( a - b )", a.toString() );
		
		a.addOutgoing(new Name("c"));
		a.addOutgoing(new Name("d"));
		
		assertEquals("( a - b - c - d )", a.toString() );
	}
	
	public void testTimesOperator()
	{
		BinaryOperator a = new BinaryOperator(BinaryType.times);
		a.addOutgoing(new Name("a"));
		a.addOutgoing(new Name("b"));
		
		assertEquals("( a * b )", a.toString() );
		
		a.addOutgoing(new Name("c"));
		a.addOutgoing(new Name("d"));
		
		assertEquals("( a * b * c * d )", a.toString() );
	}
	
	public void testDivideOperator()
	{
		BinaryOperator a = new BinaryOperator(BinaryType.divide);
		a.addOutgoing(new Name("a"));
		a.addOutgoing(new Name("b"));
		
		assertEquals("( a / b )", a.toString() );
		
		a.addOutgoing(new Name("c"));
		a.addOutgoing(new Name("d"));
		
		assertEquals("( a / b / c / d )", a.toString() );
	}
	
		

}
