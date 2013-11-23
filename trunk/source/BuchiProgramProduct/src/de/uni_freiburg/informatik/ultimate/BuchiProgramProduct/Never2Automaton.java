package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AtomicProposition;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.BinaryOperator;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.BoolLiteral;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.ComperativeOperator;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.IntLiteral;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.LabeledBlock;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.Name;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.NeverStatement;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.Not;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.OptionStatement;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.SkipStatement;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;


/**
 * Never2Automaton converts the never claim description
 * of an automaton into an an automaton off the nwa lib.
 * 
 * @author Langenfeld
 * @note the transformation from Ast to Automaton also 
 * bringst a transformation from Promela Ast to Boogie Ast  nodes.
 */
public class Never2Automaton{
	
	private AstNode ast;
	
	private NestedWordAutomaton<ASTNode, String> automaton;
	
	/**
	 * The Never2Automaton instance will build a Büchi automaton
	 * from the input.
	 * @param ast
	 * @throws Exception 
	 */
	public Never2Automaton(AstNode ast) throws Exception
	{
		this.ast = ast;
		
		
		this.automaton = new NestedWordAutomaton<ASTNode,String>(
				this.collectAlphabet(), 
				null, //call
				null, //return
				new DummyStateFactory<String>()  //state factory?!?
				);
		
		this.collectStates(this.ast, null);
		System.out.println(this.automaton.toString());
	}
	
	/**
	 * get the constructed automaton
	 * @return automaton
	 */
	public NestedWordAutomaton<ASTNode, String> getAutomaton()
	{
		return this.automaton;
	}
	
	/**
	 * Walks the AST for labeled blocks and extracts the names as Nodes in the
	 * automaton. Nodes starting with "accept" are accepting nodes, the one called init 
	 * is the initial one. 
	 * @see LTL2BA, LTL3BA output format
 	 * @param branch Ast of the Automaton description in Promela
	 * @throws Exception 
	 */
	private void collectStates(AstNode branch, String pred) throws Exception
	{
		if (branch instanceof LabeledBlock) 			//add nodes
		{
			String n = ((Name)((LabeledBlock)branch).getValue()).getIdent();
			if( !this.automaton.getStates().contains(n)){
				this.automaton.addState(n.endsWith("init"), n.startsWith("accept"), n);
			}
			for(AstNode a: branch.getOutgoingNodes())
				this.collectStates(a, n);
		}
		else if (branch instanceof BoolLiteral)
			return;
		else if (branch instanceof SkipStatement) {
			//case " accept_all: skip
			this.automaton.addInternalTransition(pred, new BooleanLiteral(null, true), pred);
			return;
		} else if (branch instanceof Name)
			return;
		else if (branch instanceof OptionStatement) 	//add transitions
		{
			ASTNode cond = this.toBoogieAst(((OptionStatement)branch).getCondition());
			//			  option.body                     		 .goto					    .name
			String succ = ((Name)branch.getOutgoingNodes().get(0).getOutgoingNodes().get(0)).getIdent();
			
			if( !this.automaton.getStates().contains(succ)){
				this.automaton.addState(succ.endsWith("init"), succ.startsWith("accept"), succ);
			}
				
			this.automaton.addInternalTransition(pred, cond, succ);
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
	 * @throws Exception 
	 */
	public Set<ASTNode> collectAlphabet() throws Exception
	{
		Set<ASTNode> symbols = new HashSet<ASTNode>();

		this.visitAstForSymbols(this.ast, symbols);
		
		return symbols;
	}
	private void visitAstForSymbols(AstNode branch, Set<ASTNode> symbols) throws Exception
	{
		if (branch instanceof BoolLiteral)
			return;
		else if (branch instanceof SkipStatement)
			symbols.add(new BooleanLiteral(null, true));
		else if (branch instanceof Name)
			return;
		else if (branch instanceof OptionStatement)
		{
			symbols.add(this.toBoogieAst(((OptionStatement)branch).getCondition()));
		}
		else
		{
			for(AstNode a: branch.getOutgoingNodes())
				this.visitAstForSymbols(a, symbols);
		}
	}
	
	/**
	 * Translates the atomic propositions from LTL2Aut.AstNode into 
	 * Boogie ASTNode for further processing.
	 * @return root node of the proposition as Boogie ASTNodes
	 * @throws Exception 
	 */
	public Expression toBoogieAst(AstNode branch) throws Exception
	{
		if (branch instanceof BinaryOperator){
			BinaryExpression.Operator op;
			switch(((BinaryOperator)branch).getType()){
			case and:
				op = BinaryExpression.Operator.LOGICAND; break;
			case minus:
				op = BinaryExpression.Operator.ARITHMINUS;break;
			case or:
				op = BinaryExpression.Operator.LOGICOR;break;
			case plus:
				op = BinaryExpression.Operator.ARITHPLUS;break;
			case times:
				op = BinaryExpression.Operator.ARITHMUL;break;
			default:
				throw new Exception("Binary Operator unknown");
			}
			BinaryExpression b;
			b = new BinaryExpression(null, null, op, 
					this.toBoogieAst(branch.getOutgoingNodes().get(0)), 
					this.toBoogieAst(branch.getOutgoingNodes().get(1)));
			if (branch.getOutgoingNodes().size() > 2){
				for(int i = 2; i < branch.getOutgoingNodes().size(); i++){
					b = new BinaryExpression(null, null, op, 
							b, 
							this.toBoogieAst(branch.getOutgoingNodes().get(i)));	
				}
			}
			return b;
					
		} else if (branch instanceof BoolLiteral)
			return new BooleanLiteral(null, ((BoolLiteral)branch).getValue());
		else if (branch instanceof ComperativeOperator){
			BinaryExpression.Operator op;
			switch(((ComperativeOperator)branch).getType()){
			case equals:
				op = BinaryExpression.Operator.COMPEQ;break;
			case geq:
				op = BinaryExpression.Operator.COMPGEQ;break;
			case greater:
				op = BinaryExpression.Operator.COMPGT;break;
			default:
				throw new Exception("Binary Operator unknown");
			}
			return new BinaryExpression(null, null, op, 
					this.toBoogieAst(branch.getOutgoingNodes().get(0)), 
					this.toBoogieAst(branch.getOutgoingNodes().get(1)));
		} else if (branch instanceof IntLiteral)
			return new IntegerLiteral(null, Integer.toString(((IntLiteral)branch).getValue()));
		else if (branch instanceof Name)
			return new IdentifierExpression(null, ((Name)branch).getIdent());
		else if (branch instanceof Not)
			return new UnaryExpression(null,UnaryExpression.Operator.LOGICNEG, 
					this.toBoogieAst(branch.getOutgoingNodes().get(0)));
		
		throw new Exception("Type " + branch.getClass().toString() + " should not occur as part of a atomic Proposition in LTL");

	}
}


















































