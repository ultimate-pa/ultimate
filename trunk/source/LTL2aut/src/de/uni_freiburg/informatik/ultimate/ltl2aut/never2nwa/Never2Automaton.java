package de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.BinaryOperator;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.BoolLiteral;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.ComperativeOperator;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.IntLiteral;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.LabeledBlock;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.Name;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.Not;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.OptionStatement;
import de.uni_freiburg.informatik.ultimate.ltl2aut.ast.SkipStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.result.LTLPropertyCheck.CheckableExpression;

/**
 * Never2Automaton converts the never claim description of an automaton into an
 * an NWA automaton of the AutomataLibrary.
 * 
 * @author Langenfeld
 * @note the transformation from Ast to Automaton also bringst a transformation
 *       from Promela Ast to Boogie Ast nodes.
 */
public class Never2Automaton {

	private final AstNode mNeverClaim;
	private final Logger mLogger;
	private final Map<String, CheckableExpression> mIRS;

	private NestedWordAutomaton<CodeBlock, String> mAutomaton;

	/**
	 * The Never2Automaton instance will build a Büchi automaton from the input.
	 * 
	 * @param ast
	 * @param irs
	 * @param services
	 * @throws Exception
	 */
	public Never2Automaton(AstNode ast, BoogieSymbolTable boogieSymbolTable, Map<String, CheckableExpression> irs,
			Logger logger, IUltimateServiceProvider services) throws Exception {
		mLogger = logger;
		mNeverClaim = ast;
		mIRS = irs;

		mAutomaton = new NestedWordAutomaton<CodeBlock, String>(collectAlphabet(), null, // call
				null, // return
				new DummyStateFactory<String>());

		collectStates(mNeverClaim, null);

		mLogger.debug(String.format("Resulting automaton is:\n%s", mAutomaton));
	}

	/**
	 * get the constructed automaton
	 * 
	 * @return automaton
	 */
	public NestedWordAutomaton<CodeBlock, String> getAutomaton() {
		return mAutomaton;
	}

	/**
	 * Walks the AST for labeled blocks and extracts the names as Nodes in the
	 * automaton. Nodes starting with "accept" are accepting nodes, the one
	 * called init is the initial one.
	 * 
	 * @see LTL2BA, LTL3BA output format
	 * @param branch
	 *            Ast of the Automaton description in Promela
	 * @throws Exception
	 */
	private void collectStates(AstNode branch, String pred) throws Exception {
		if (branch instanceof LabeledBlock) // add nodes
		{
			String n = ((Name) ((LabeledBlock) branch).getValue()).getIdent();
			if (!mAutomaton.getStates().contains(n)) {
				mAutomaton.addState(n.endsWith("init"), n.startsWith("accept"), n);
			}
			for (AstNode a : branch.getOutgoingNodes()) {
				collectStates(a, n);
			}
		} else if (branch instanceof BoolLiteral) {
			return;
		} else if (branch instanceof SkipStatement) {
			// case " accept_all: skip
			mAutomaton.addInternalTransition(pred, getAssumeTrue(), pred);
			return;
		} else if (branch instanceof Name) {
			return;
		} else if (branch instanceof OptionStatement) {
			// add transitions

			CodeBlock cond = getAssume(((OptionStatement) branch).getCondition());
			// option.body .goto .name
			String succ = ((Name) branch.getOutgoingNodes().get(0).getOutgoingNodes().get(0)).getIdent();

			if (!mAutomaton.getStates().contains(succ)) {
				mAutomaton.addState(succ.endsWith("init"), succ.startsWith("accept"), succ);
			}

			mAutomaton.addInternalTransition(pred, cond, succ);
		} else {
			for (AstNode a : branch.getOutgoingNodes()) {
				collectStates(a, pred);
			}
		}
	}

	/**
	 * Collect all symbols that the automaton will have from the AST which will
	 * be all conditions found in the AST.
	 * 
	 * @param mNeverClaim
	 *            Ast of the Automaton description in Promela
	 * @return
	 * @throws Exception
	 */
	public Set<CodeBlock> collectAlphabet() throws Exception {
		Set<CodeBlock> symbols = new HashSet<CodeBlock>();

		visitAstForSymbols(mNeverClaim, symbols);

		return symbols;
	}

	private void visitAstForSymbols(AstNode branch, Set<CodeBlock> symbols) throws Exception {
		if (branch instanceof BoolLiteral)
			return;
		else if (branch instanceof SkipStatement)
			symbols.add(getAssumeTrue());
		else if (branch instanceof Name)
			return;
		else if (branch instanceof OptionStatement) {
			symbols.add(getAssume(((OptionStatement) branch).getCondition()));
		} else {
			for (AstNode a : branch.getOutgoingNodes()) {
				visitAstForSymbols(a, symbols);
			}
		}
	}

	private CodeBlock getAssumeTrue() {
		ILocation loc = null;
		StatementSequence ss = new StatementSequence(null, null,
				new AssumeStatement(loc, new BooleanLiteral(loc, true)), mLogger);
		return ss;
	}

	private CodeBlock getAssume(AstNode condition) throws Exception {
		if (condition instanceof Name) {
			// this may be already translated by the IRS
			Name name = (Name) condition;
			CheckableExpression checkExpr = mIRS.get(name.getIdent().toUpperCase());
			if (checkExpr != null) {
				List<Statement> stmts = new ArrayList<>();
				if (checkExpr.getStatements() != null) {
					stmts.addAll(checkExpr.getStatements());
				}
				stmts.add(new AssumeStatement(checkExpr.getExpression().getLocation(), checkExpr.getExpression()));
				return new StatementSequence(null, null, stmts, Origin.ASSERT, mLogger);
			} else {
				mLogger.warn("Root condition is a name, but no mapping in IRS found: " + name.getIdent());
			}
		}

		// this could be an actual neverclaim and we have to translate it
		// manually
		CheckableExpression checkExpr = toBoogieAst(condition);
		List<Statement> stmts = new ArrayList<>();
		if (checkExpr.getStatements() != null) {
			stmts.addAll(checkExpr.getStatements());
		}
		stmts.add(new AssumeStatement(checkExpr.getExpression().getLocation(), checkExpr.getExpression()));
		return new StatementSequence(null, null, stmts, Origin.ASSERT, mLogger);
	}

	/**
	 * Translates the atomic propositions from LTL2Aut.AstNode into Boogie
	 * ASTNode for further processing.
	 * 
	 * @return root node of the proposition as Boogie ASTNodes
	 * @throws Exception
	 */
	public CheckableExpression toBoogieAst(AstNode branch) throws Exception {
		if (branch instanceof BinaryOperator) {
			BinaryOperator ncBinOp = (BinaryOperator) branch;
			BinaryExpression.Operator op;
			switch (ncBinOp.getType()) {
			case and:
				op = BinaryExpression.Operator.LOGICAND;
				break;
			case minus:
				op = BinaryExpression.Operator.ARITHMINUS;
				break;
			case or:
				op = BinaryExpression.Operator.LOGICOR;
				break;
			case plus:
				op = BinaryExpression.Operator.ARITHPLUS;
				break;
			case times:
				op = BinaryExpression.Operator.ARITHMUL;
				break;
			case divide:
				op = BinaryExpression.Operator.ARITHDIV;
				break;
			default:
				throw new Exception("Binary Operator unknown");
			}

			CheckableExpression left = toBoogieAst(branch.getOutgoingNodes().get(0));
			CheckableExpression right = toBoogieAst(branch.getOutgoingNodes().get(1));
			CheckableExpression expr = new CheckableExpression(new BinaryExpression(null, op, left.getExpression(),
					right.getExpression()), mergeStatements(left, right));

			if (branch.getOutgoingNodes().size() > 2) {
				for (int i = 2; i < branch.getOutgoingNodes().size(); i++) {
					right = toBoogieAst(branch.getOutgoingNodes().get(i));
					expr = new CheckableExpression(new BinaryExpression(null, op, expr.getExpression(),
							right.getExpression()), mergeStatements(expr, right));
				}
			}
			return expr;

		} else if (branch instanceof BoolLiteral) {
			return new CheckableExpression(new BooleanLiteral(null, ((BoolLiteral) branch).getValue()), null);
		} else if (branch instanceof ComperativeOperator) {
			BinaryExpression.Operator op;
			switch (((ComperativeOperator) branch).getType()) {
			case equals:
				op = BinaryExpression.Operator.COMPEQ;
				break;
			case geq:
				op = BinaryExpression.Operator.COMPGEQ;
				break;
			case greater:
				op = BinaryExpression.Operator.COMPGT;
				break;
			default:
				throw new Exception("Binary Operator unknown");
			}
			CheckableExpression left = toBoogieAst(branch.getOutgoingNodes().get(0));
			CheckableExpression right = toBoogieAst(branch.getOutgoingNodes().get(1));
			CheckableExpression expr = new CheckableExpression(new BinaryExpression(null, op, left.getExpression(),
					right.getExpression()), mergeStatements(left, right));
			return expr;
		} else if (branch instanceof IntLiteral) {
			return new CheckableExpression(
					new IntegerLiteral(null, Integer.toString(((IntLiteral) branch).getValue())), null);
		} else if (branch instanceof Name) {
			Name name = (Name) branch;
			CheckableExpression checkExpr = mIRS.get(name.getIdent().toUpperCase());
			if (checkExpr != null) {
				return checkExpr;
			}
		} else if (branch instanceof Not) {
			CheckableExpression right = toBoogieAst(branch.getOutgoingNodes().get(0));
			return new CheckableExpression(new UnaryExpression(null, UnaryExpression.Operator.LOGICNEG,
					right.getExpression()), right.getStatements());
		}

		throw new Exception(String.format("Type %s should not occur as part of a atomic Proposition in LTL", branch
				.getClass().toString()));
	}

	private List<Statement> mergeStatements(CheckableExpression... exprs) {
		List<Statement> rtr = new ArrayList<>();

		for (CheckableExpression expr : exprs) {
			if (expr.getStatements() != null) {
				rtr.addAll(expr.getStatements());
			}
		}

		return rtr;
	}
}
