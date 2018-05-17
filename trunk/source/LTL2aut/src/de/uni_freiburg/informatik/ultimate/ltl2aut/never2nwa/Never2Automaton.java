/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 *
 * This file is part of the ULTIMATE LTL2Aut plug-in.
 *
 * The ULTIMATE LTL2Aut plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LTL2Aut plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LTL2Aut plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LTL2Aut plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LTL2Aut plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.ltl2aut.never2nwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.DummyStateFactory;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieExpressionTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck.CheckableExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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
import de.uni_freiburg.informatik.ultimate.ltl2aut.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.util.simplifier.NormalFormTransformer;

/**
 * Never2Automaton converts the never claim description of an automaton into an an NWA automaton of the AutomataLibrary.
 *
 * @author Langenfeld
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @note the transformation from Ast to Automaton also brings a transformation from Promela Ast to Boogie Ast nodes.
 */
public class Never2Automaton {
	private final IUltimateServiceProvider mServices;
	private final AstNode mNeverClaim;
	private final ILogger mLogger;
	private final Map<String, CheckableExpression> mIRS;
	private final CodeBlockFactory mCodeblockFactory;
	
	private final NestedWordAutomaton<CodeBlock, String> mAutomaton;
	
	private final boolean mUseSBE;
	private final boolean mRewriteAssumeDuringSBE;
	
	/**
	 * The Never2Automaton instance will build a Büchi automaton from the input.
	 *
	 * @param ast
	 * @param irs
	 * @param services
	 * @param cbf
	 * @throws Exception
	 */
	public Never2Automaton(final AstNode ast, final BoogieSymbolTable boogieSymbolTable,
			final Map<String, CheckableExpression> irs, final ILogger logger, final IUltimateServiceProvider services,
			final CodeBlockFactory cbf) throws Exception {
		mServices = services;
		mLogger = logger;
		mNeverClaim = ast;
		mIRS = irs;
		mCodeblockFactory = cbf;
		
		final IPreferenceProvider ups =
				mServices.getPreferenceProvider(de.uni_freiburg.informatik.ultimate.ltl2aut.Activator.PLUGIN_ID);
		mUseSBE = ups.getBoolean(PreferenceInitializer.LABEL_OPTIMIZE_SBE);
		mRewriteAssumeDuringSBE = ups.getBoolean(PreferenceInitializer.LABEL_OPTIMIZE_REWRITEASSUME);
		
		mAutomaton = new NestedWordAutomaton<>(new AutomataLibraryServices(mServices),
				new VpAlphabet<>(collectAlphabet()),
				new DummyStateFactory<String>());
		
		collectStates(mNeverClaim, null);
		
		mLogger.debug(String.format("Resulting automaton is:\n%s", mAutomaton));
	}
	
	/**
	 * get the constructed automaton
	 *
	 * @return automaton
	 */
	public INestedWordAutomaton<CodeBlock, String> getAutomaton() {
		return mAutomaton;
	}
	
	/**
	 * Walks the AST for labeled blocks and extracts the names as Nodes in the automaton. Nodes starting with "accept"
	 * are accepting nodes, the one called init is the initial one.
	 *
	 * @see LTL2BA, LTL3BA output format
	 * @param branch
	 *            Ast of the Automaton description in Promela
	 * @throws Exception
	 */
	private void collectStates(final AstNode branch, final String preState) throws Exception {
		if (branch instanceof LabeledBlock) // add nodes
		{
			final String state = ((Name) ((LabeledBlock) branch).getValue()).getIdent();
			addState(state);
			for (final AstNode a : branch.getOutgoingNodes()) {
				collectStates(a, state);
			}
		} else if (branch instanceof BoolLiteral) {
			return;
		} else if (branch instanceof SkipStatement) {
			// case " accept_all: skip
			addTransition(preState, getAssumeTrue(), preState);
			return;
		} else if (branch instanceof Name) {
			return;
		} else if (branch instanceof OptionStatement) {
			
			// option.body .goto .name
			final String succ = ((Name) branch.getOutgoingNodes().get(0).getOutgoingNodes().get(0)).getIdent();
			
			addState(succ);
			
			// add transitions
			for (final CodeBlock cond : getAssume(((OptionStatement) branch).getCondition())) {
				addTransition(preState, cond, succ);
			}
		} else {
			for (final AstNode a : branch.getOutgoingNodes()) {
				collectStates(a, preState);
			}
		}
	}
	
	/**
	 * Collect all symbols that the automaton will have from the AST which will be all conditions found in the AST.
	 *
	 * @param mNeverClaim
	 *            Ast of the Automaton description in Promela
	 * @return
	 * @throws Exception
	 */
	public Set<CodeBlock> collectAlphabet() throws Exception {
		final Set<CodeBlock> symbols = new HashSet<>();
		visitAstForSymbols(mNeverClaim, symbols);
		return symbols;
	}
	
	private void visitAstForSymbols(final AstNode branch, final Set<CodeBlock> symbols) throws Exception {
		if (branch instanceof BoolLiteral) {
			return;
		} else if (branch instanceof SkipStatement) {
			symbols.add(getAssumeTrue());
		} else if (branch instanceof Name) {
			return;
		} else if (branch instanceof OptionStatement) {
			symbols.addAll(getAssume(((OptionStatement) branch).getCondition()));
		} else {
			for (final AstNode a : branch.getOutgoingNodes()) {
				visitAstForSymbols(a, symbols);
			}
		}
	}
	
	private CodeBlock getAssumeTrue() {
		final ILocation loc = null;
		final StatementSequence ss = mCodeblockFactory.constructStatementSequence(null, null,
				new AssumeStatement(loc, new BooleanLiteral(loc, true)));
		return ss;
	}
	
	private List<CodeBlock> getAssume(final AstNode condition) throws Exception {
		if (condition instanceof Name) {
			// this may be already translated by the IRS
			final Name name = (Name) condition;
			final CheckableExpression checkExpr = mIRS.get(name.getIdent().toUpperCase());
			if (checkExpr != null) {
				return getAssumeFromCheckableExpression(checkExpr);
			} else {
				mLogger.warn("Root condition is a name, but no mapping in IRS found: " + name.getIdent());
			}
		}
		
		// this could be an actual neverclaim and we have to translate it
		// manually
		final CheckableExpression checkExpr = toBoogieAst(condition);
		return getAssumeFromCheckableExpression(checkExpr);
	}
	
	private List<CodeBlock> getAssumeFromCheckableExpression(final CheckableExpression checkExpr) {
		final ArrayList<CodeBlock> rtr = new ArrayList<>();
		final List<Statement> preStmts = new ArrayList<>();
		if (checkExpr.getStatements() != null) {
			preStmts.addAll(checkExpr.getStatements());
		}
		
		final ILocation loc = checkExpr.getExpression().getLocation();
		for (final Expression expr : simplify(checkExpr.getExpression())) {
			final List<Statement> stmts = new ArrayList<>(preStmts);
			stmts.add(new AssumeStatement(loc, expr));
			rtr.add(mCodeblockFactory.constructStatementSequence(null, null, stmts, Origin.ASSERT));
		}
		return rtr;
	}
	
	private Collection<Expression> simplify(Expression expr) {
		if (mUseSBE) {
			final NormalFormTransformer<Expression> ct = new NormalFormTransformer<>(new BoogieExpressionTransformer());
			if (mRewriteAssumeDuringSBE) {
				expr = ct.rewriteNotEquals(expr);
			}
			return ct.toDnfDisjuncts(expr);
		} else {
			return Collections.singleton(expr);
		}
	}
	
	/**
	 * Translates the atomic propositions from LTL2Aut.AstNode into Boogie ASTNode for further processing.
	 *
	 * @return root node of the proposition as Boogie ASTNodes
	 * @throws Exception
	 */
	public CheckableExpression toBoogieAst(final AstNode branch) throws Exception {
		if (branch instanceof BinaryOperator) {
			final BinaryOperator ncBinOp = (BinaryOperator) branch;
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
			
			final CheckableExpression left = toBoogieAst(branch.getOutgoingNodes().get(0));
			CheckableExpression right = toBoogieAst(branch.getOutgoingNodes().get(1));
			CheckableExpression expr =
					new CheckableExpression(new BinaryExpression(null, op, left.getExpression(), right.getExpression()),
							mergeStatements(left, right));
			
			if (branch.getOutgoingNodes().size() > 2) {
				for (int i = 2; i < branch.getOutgoingNodes().size(); i++) {
					right = toBoogieAst(branch.getOutgoingNodes().get(i));
					expr = new CheckableExpression(
							new BinaryExpression(null, op, expr.getExpression(), right.getExpression()),
							mergeStatements(expr, right));
				}
			}
			return expr;
			
		} else if (branch instanceof BoolLiteral) {
			return new CheckableExpression(
					new BooleanLiteral(null, BoogieType.TYPE_BOOL, ((BoolLiteral) branch).getValue()), null);
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
			final CheckableExpression left = toBoogieAst(branch.getOutgoingNodes().get(0));
			final CheckableExpression right = toBoogieAst(branch.getOutgoingNodes().get(1));
			final CheckableExpression expr =
					new CheckableExpression(new BinaryExpression(null, op, left.getExpression(), right.getExpression()),
							mergeStatements(left, right));
			return expr;
		} else if (branch instanceof IntLiteral) {
			return new CheckableExpression(new IntegerLiteral(null, Integer.toString(((IntLiteral) branch).getValue())),
					null);
		} else if (branch instanceof Name) {
			final Name name = (Name) branch;
			final CheckableExpression checkExpr = mIRS.get(name.getIdent().toUpperCase());
			if (checkExpr != null) {
				return checkExpr;
			}
		} else if (branch instanceof Not) {
			final CheckableExpression right = toBoogieAst(branch.getOutgoingNodes().get(0));
			return new CheckableExpression(
					new UnaryExpression(null, UnaryExpression.Operator.LOGICNEG, right.getExpression()),
					right.getStatements());
		} else if (branch instanceof Name) {
			final Name name = (Name) branch;
			if ("true".equalsIgnoreCase(name.getIdent())) {
				return new CheckableExpression(new BooleanLiteral(null, true), null);
			} else if ("false".equalsIgnoreCase(name.getIdent())) {
				return new CheckableExpression(new BooleanLiteral(null, false), null);
			}
		}
		
		throw new Exception(String.format("Type %s should not occur as part of a atomic Proposition in LTL",
				branch.getClass().toString()));
	}
	
	private List<Statement> mergeStatements(final CheckableExpression... exprs) {
		final List<Statement> rtr = new ArrayList<>();
		for (final CheckableExpression expr : exprs) {
			if (expr.getStatements() != null) {
				rtr.addAll(expr.getStatements());
			}
		}
		return rtr;
	}
	
	private void addTransition(final String predecessor, final CodeBlock letter, final String successor) {
		mAutomaton.getVpAlphabet().getInternalAlphabet().add(letter);
		mAutomaton.addInternalTransition(predecessor, letter, successor);
	}
	
	private void addState(final String state) {
		if (!mAutomaton.getStates().contains(state)) {
			mAutomaton.addState(state.endsWith("init"), state.startsWith("accept"), state);
		}
	}
}
