package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct.test;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import junit.framework.TestCase;

import org.junit.Test;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.BuchiProgramProduct.Never2Automaton;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.*;

public class TestPromela2Automaton extends TestCase{

	/**
	 * test basic functionality, reading an AST and 
	 * figuring out that there is one symbol
	 */
	public void testSymbolCollectorTrivial()
	{
		AstNode skip = new SkipStatement();
		AstNode label = new Name("accept_n1");
		AstNode lb1 = new LabeledBlock(label, skip);
		AstNode never = new NeverStatement(lb1);
		
		Never2Automaton na = new Never2Automaton(never);	
		AstNode[] symbols = na.collectAlphabet().toArray(new AstNode[0]);
		
		assertEquals(1,symbols.length);
		assertTrue(symbols[0] instanceof SkipStatement); 
		
	}
	
	/**
	 * test all different kinds of symbols that can 
	 * be part of the ast conditions.
	 */
	public void testSymbolCollector()
	{
		AstNode skip = new SkipStatement();
		AstNode label = new Name("accept_init");
		AstNode lb1 = new LabeledBlock(label, skip);
		AstNode never = new NeverStatement(lb1);
		
		AstNode con1 = new ComperativeOperator(ComperativeType.geq, new IntLiteral(5), new Name("x"));
		AstNode con2 = new Not(new ComperativeOperator(ComperativeType.equals, new IntLiteral(5), new Name("x")));
		AstNode o1 = new OptionStatement(con1 , new GotoStatement(label));
		AstNode o2 = new OptionStatement(con2 , new GotoStatement(label));
		AstNode b = new BoolLiteral(true);
		AstNode o3 = new OptionStatement(b , new GotoStatement(label));
	
		never.addOutgoing(new LabeledBlock(new Name("accept_n2"), new ConditionalBlock(new ArrayList<AstNode>(Arrays.asList(o1,o2,o3)))));
		
		Never2Automaton na = new Never2Automaton(never);	
		Set<AstNode> symbols = na.collectAlphabet();
		
		
		assertEquals(4,symbols.size());
		assertTrue(symbols.contains(skip)); //skip
		assertTrue(symbols.contains(con1)); //5>=x
		assertTrue(symbols.contains(con2)); //(!5=x)
		assertTrue(symbols.contains(b)); 	//true
	}

}
