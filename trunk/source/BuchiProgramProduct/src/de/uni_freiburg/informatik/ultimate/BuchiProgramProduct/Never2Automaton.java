package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.BoolLiteral;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.LabeledBlock;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.Name;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.NeverStatement;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.OptionStatement;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.SkipStatement;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.model.IElement;


/**
 * Never2Automaton converts the never claim description
 * of an automaton into an an automaton off the nwa lib.
 * 
 * @author Langenfeld
 *
 */
public class Never2Automaton{
	
	private AstNode ast;
	
	private NestedWordAutomaton<AstNode, String> aut;
	
	/**
	 * The Never2Automaton instance will build a Büchi automaton
	 * from the input.
	 * @param ast
	 */
	public Never2Automaton(AstNode ast)
	{
		this.ast = ast;
		
		
		this.aut = new NestedWordAutomaton<AstNode,String>(
				this.collectAlphabet(), 
				null, //call
				null, //return
				new DummyStateFactory<String>()  //state factory?!?
				);
		
		this.collectStates(this.ast, null);
	}
	
	/**
	 * get the constructed automaton
	 * @return automaton
	 */
	public NestedWordAutomaton<AstNode, String> getAutomaton()
	{
		return this.aut;
	}
	
	/**
	 * Walks the AST for labeled blocks and extracts the names as Nodes in the
	 * automaton. Nodes starting with "accept" are accepting nodes, the one called init 
	 * is the initial one. 
	 * @see LTL2BA, LTL3BA output format
 	 * @param branch Ast of the Automaton description in Promela
	 */
	private void collectStates(AstNode branch, String pred)
	{
		if (branch instanceof LabeledBlock) 			//add nodes
		{
			String n = ((Name)((LabeledBlock)branch).getValue()).getIdent();
			this.aut.addState(n.endsWith("init"), n.startsWith("accept"), n);
			for(AstNode a: branch.getOutgoingNodes())
				this.collectStates(a, n);
		}
		else if (branch instanceof BoolLiteral)
			return;
		else if (branch instanceof SkipStatement)
			return;
		else if (branch instanceof Name)
			return;
		else if (branch instanceof OptionStatement) 	//add transitions
		{
			AstNode cond = ((OptionStatement)branch).getCondition();
			//			  option.body                     		 .goto					    .name
			String succ = ((Name)branch.getOutgoingNodes().get(0).getOutgoingNodes().get(0)).getIdent();
			this.aut.addInternalTransition(pred, cond, succ);
		}
		else
		{
			for(AstNode a: branch.getOutgoingNodes())
				this.collectStates(a, pred);
		}
	}
	
	/**
	 * Collect all symbols that the automaton will have from the
	 * AST which will be all conditions found in the AST.
	 * @param ast Ast of the Automaton description in Promela
	 * @return
	 */
	public Set<AstNode> collectAlphabet()
	{
		Set<AstNode> symbols = new HashSet<AstNode>();

		this.visitAstForSymbols(this.ast, symbols);
		
		return symbols;
	}
	private void visitAstForSymbols(AstNode branch, Set<AstNode> symbols)
	{
		if (branch instanceof BoolLiteral)
			return;
		else if (branch instanceof SkipStatement)
			symbols.add(branch);
		else if (branch instanceof Name)
			return;
		else if (branch instanceof OptionStatement)
		{
			symbols.add(((OptionStatement)branch).getCondition());
		}
		else
		{
			for(AstNode a: branch.getOutgoingNodes())
				this.visitAstForSymbols(a, symbols);
		}
	}
}


















































