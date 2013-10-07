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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;

public class TestPromela2Automaton extends TestCase{

	/**
	 * test basic functionality, reading an AST and 
	 * figuring out that there is one symbol
	 * @throws Exception 
	 */
	public void testSymbolCollectorTrivialTrue() throws Exception
	{
		AstNode skip = new SkipStatement();
		AstNode label = new Name("accept_init");
		AstNode lb1 = new LabeledBlock(label, skip);
		AstNode never = new NeverStatement(lb1);
		
		Never2Automaton na = new Never2Automaton(never);
		Set<ASTNode> symbset = na.collectAlphabet();
		ASTNode[] symbols = symbset.toArray(new ASTNode[symbset.size()]);
		
		assertEquals(1,symbols.length);
		assertTrue(symbols[0] instanceof BooleanLiteral); 	
	}
	
	/**
	 * test all different kinds of symbols that can 
	 * be part of the ast conditions.
	 * @throws Exception 
	 */
	public void testSymbolCollector() throws Exception
	{
		AstNode skip = new SkipStatement();
		AstNode label = new Name("accept_init");
		AstNode lb1 = new LabeledBlock(label, skip);
		AstNode never = new NeverStatement(lb1);
		
		AstNode con1 = new ComperativeOperator(ComperativeType.geq, 
				new BinaryOperator(BinaryType.plus,
						new Name("y"),
						new IntLiteral(5)),
				new Name("x"));
		AstNode con2 = new Not(new ComperativeOperator(ComperativeType.equals, new IntLiteral(5), new Name("x")));
		AstNode o1 = new OptionStatement(con1 , new GotoStatement(label));
		AstNode o2 = new OptionStatement(con2 , new GotoStatement(label));
		AstNode b = new BoolLiteral(true);
		AstNode o3 = new OptionStatement(b , new GotoStatement(label));
	
		never.addOutgoing(new LabeledBlock(new Name("accept_n2"), new ConditionalBlock(new ArrayList<AstNode>(Arrays.asList(o1,o2,o3)))));
		
		Never2Automaton na = new Never2Automaton(never);	
		Set<ASTNode> symbols = na.collectAlphabet();
		
		
		assertEquals(4,symbols.size());
		ArrayList<String> symbstrings = new ArrayList<String>();
		for(ASTNode a : symbols)
		{
			symbstrings.add(a.toString());
		}
		assertTrue(symbstrings.contains("BooleanLiteral[true]")); //skip
		symbstrings.remove("BooleanLiteral[true]");
		assertTrue(symbstrings.contains("BinaryExpression[COMPGEQ,BinaryExpression[ARITHPLUS,IdentifierExpression[y],IntegerLiteral[5]],IdentifierExpression[x]]")); //5+y>=x
		assertTrue(symbstrings.contains("UnaryExpression[LOGICNEG,BinaryExpression[COMPEQ,IntegerLiteral[5],IdentifierExpression[x]]]")); //(!5=x)
		assertTrue(symbstrings.contains("BooleanLiteral[true]")); 	//true
	}
	
	/**
	 * testing basic transformation from ast to automaton
	 * @throws Exception 
	 */
	public void testAutomatonCreationsSimple() throws Exception
	{
		AstNode skip = new SkipStatement();
		AstNode label = new Name("accept_init");
		AstNode lb1 = new LabeledBlock(label, skip);
		AstNode never = new NeverStatement(lb1);
		
		Never2Automaton na = new Never2Automaton(never);
		NestedWordAutomaton<ASTNode, String> aut = na.getAutomaton();
	
		assertTrue(aut.getInitialStates().contains("accept_init"));
		assertTrue(aut.getFinalStates().contains("accept_init"));
		assertTrue(aut.getInitialStates().size() == 1);
		assertTrue(aut.getFinalStates().size() == 1);
		//test if transition is present
	}

	//TODO: test of more involved example 
}
