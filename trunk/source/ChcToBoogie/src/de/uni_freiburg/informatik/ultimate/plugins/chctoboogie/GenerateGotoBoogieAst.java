package de.uni_freiburg.informatik.ultimate.plugins.chctoboogie;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcBodyVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class GenerateGotoBoogieAst {

	private static final String INPARAMSUFFIX = "_inprm";

	private final Unit mResult;

	private final GenerateBoogieAstHelper mHelper;

	private final HcSymbolTable mHcSymbolTable;

	public GenerateGotoBoogieAst(final HashRelation<HcPredicateSymbol, HornClause> hornClauseHeadPredicateToHornClauses,
			final GenerateBoogieAstHelper helper) {
		mHelper = helper;
		mHcSymbolTable = helper.getSymbolTable();
		mResult = generateBoogieAstWithGotos(hornClauseHeadPredicateToHornClauses);
	}

	/**
	 * Generates a Boogie program, that has tail-recursion eliminated in favor of goto statements.
	 *
	 * <ul>
	 *  <li> Contains two procedures, the main entry point and a "goto-procedure" that simulates all the procedures
	 *   corresponding to a predicate from the standard approach. It has one label per CHC predicate symbol.
	 *  <li> the goto-procedure takes as arguments all the possible arguments of the other procedures, and one extra
	 *   argument that controls which of the procedures would have been called
	 *  <li> the goto-procedure starts with a switch over the extra parameter in order to jump to the right label
	 * </ul>
	 *
	 *
	 * @param hornClauseHeadPredicateToHornClauses
	 * @return
	 */
	private Unit generateBoogieAstWithGotos(
			final HashRelation<HcPredicateSymbol, HornClause> hornClauseHeadPredicateToHornClauses) {

		final ILocation loc = mHelper.getLoc();

		// variable declarations of the main procedure
		final List<Declaration> declarations = new ArrayList<>();
		// the statements of the main procedure
		final List<Statement> labeledBlocks = new ArrayList<>();

		// label corresponding the "False" procedure block
		final Label falseLabel = new Label(loc, "False");

		// goto var
//		final IdentifierExpression gotoVarExp = ExpressionFactory.constructIdentifierExpression(loc, BoogieType.TYPE_INT,
//				mGotoVarName, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, mGotoProcName));

		final Map<HcPredicateSymbol, Label> predSymbolToLabel = new LinkedHashMap<>();
		final Map<Label, Integer> predLabelToNumber = new LinkedHashMap<>();
		{
			Integer predsymCounter = 0;
			// generate the labels
			for (final HcPredicateSymbol predSym : hornClauseHeadPredicateToHornClauses.getDomain()) {
				final Label label = new Label(loc, mHelper.predSymToMethodName(predSym));
				final Integer number = predsymCounter++;
				predSymbolToLabel.put(predSym, label);
				predLabelToNumber.put(label, number);
			}
		}




		final Deque<HcPredicateSymbol> headPredQueue = new ArrayDeque<>();
		final Set<HcPredicateSymbol> addedToQueueBefore = new HashSet<>();

		headPredQueue.push(mHelper.getBottomPredSym());
		addedToQueueBefore.add(mHelper.getBottomPredSym());

		final Set<HcBodyVar> allBodyPredVariables = new HashSet<>();

		while (!headPredQueue.isEmpty()) {
			// breadth-first (pollFirst) or depth-first (pop) should not matter here
			final HcPredicateSymbol headPredSymbol = headPredQueue.pop();

			final Set<HornClause> hornClausesForHeadPred =
					hornClauseHeadPredicateToHornClauses.getImage(headPredSymbol);

			final List<Statement> nondetSwitch = generateNondetSwitchForPred(loc,
					predSymbolToLabel,
					predLabelToNumber,
					hornClausesForHeadPred,
					headPredQueue,
					addedToQueueBefore,
					allBodyPredVariables);


			assert hornClausesForHeadPred.isEmpty() || !nondetSwitch.stream().anyMatch(Objects::isNull);
			labeledBlocks.add(predSymbolToLabel.get(headPredSymbol));
			if (hornClausesForHeadPred.isEmpty()) {
				// "assume false; return;"
				labeledBlocks.add(new AssumeStatement(loc, ExpressionFactory.createBooleanLiteral(loc, false)));
				labeledBlocks.add(new ReturnStatement(loc));
			} else {
				assert nondetSwitch != null && nondetSwitch.get(nondetSwitch.size() - 1) instanceof GotoStatement;
				labeledBlocks.addAll(nondetSwitch);
			}
		}

		declarations.add(constructGotoProc(loc, labeledBlocks, predSymbolToLabel, predLabelToNumber,
				allBodyPredVariables));

		// add the main entry point
		declarations.add(constructMainEntryPointProcedure(loc));

		declarations.addAll(mHelper.getDeclarationsForSkolemFunctions());

		return new Unit(loc,
				declarations.toArray(new Declaration[declarations.size()]));
	}



	/**
	 * Put together the final goto-procedure, after the goto blocks have been computed.
	 * Adds the switch in front and builds the Boogie procedure.
	 *
	 * @param loc
	 * @param labeledBlocks
	 * @param predSymbolToLabel
	 * @param predLabelToNumber
	 * @param allBodyPredVariables
	 * @return
	 */
	public Procedure constructGotoProc(final ILocation loc, final List<Statement> labeledBlocks,
			final Map<HcPredicateSymbol, Label> predSymbolToLabel, final Map<Label, Integer> predLabelToNumber,
			final Set<HcBodyVar> allBodyPredVariables) {
		final List<Statement> gotoProcBody = new ArrayList<>();
		// method starts with a switch that jumps according to the argument
		{
			final List<Statement> predSwitch = null;

			for (final Entry<HcPredicateSymbol, Label> en : predSymbolToLabel.entrySet()) {
				final HcPredicateSymbol predSym = en.getKey();
				final Label predSymLabel = en.getValue();
				final Integer predSymNumber = predLabelToNumber.get(predSymLabel);


				final List<Statement> branchBody = new ArrayList<>();
				{
					final List<LeftHandSide> lhss = new ArrayList<>();
					final List<Expression> rhss = new ArrayList<>();
					for (final HcHeadVar inParam : mHcSymbolTable.getHcHeadVarsForPredSym(predSym, false)) {
						lhss.add(constructLhsForHeadVar(inParam));
						rhss.add(mHelper.getArgumentVarExp(inParam.getIndex(), inParam.getSort()));

					}
					final Statement assignment = StatementFactory.constructAssignmentStatement(loc,
							lhss.toArray(new LeftHandSide[lhss.size()]),
							rhss.toArray(new Expression[rhss.size()]));
					branchBody.add(assignment);

					branchBody.add(new GotoStatement(loc, new String[]{ en.getKey().toString() }));
				}

				final Expression condition = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ,
						getGotoVarExp(), ExpressionFactory.createIntegerLiteral(loc, predSymNumber.toString()));
				mHelper.addIteBranch(loc, predSwitch, branchBody, condition);
			}

			gotoProcBody.addAll(predSwitch);
			gotoProcBody.addAll(labeledBlocks);
		}


		// the args of the goto proc are all head vars and all body vars of all occurring predicates
		final List<VarList> gotoProgLocaLVarLists = new ArrayList<>();
		final List<VarList> headPrdVarLists = new ArrayList<>();
		predSymbolToLabel.keySet()
			.forEach(ps -> mHcSymbolTable.getHcHeadVarsForPredSym(ps, false)
				.forEach(hcv -> headPrdVarLists.add(new VarList(loc, new String[] { hcv.getGloballyUniqueId() },
						mHelper.getCorrespondingAstType(loc, hcv.getSort())))));
		gotoProgLocaLVarLists.addAll(headPrdVarLists);
		allBodyPredVariables.forEach(hcv -> gotoProgLocaLVarLists.add(
				new VarList(loc, new String[] { hcv.getGloballyUniqueId() },
						mHelper.getCorrespondingAstType(loc, hcv.getSort()))));
		final VariableDeclaration localVarDec = new VariableDeclaration(loc, new Attribute[0],
				gotoProgLocaLVarLists.toArray(new VarList[gotoProgLocaLVarLists.size()]));

		final Procedure gotoProc = new Procedure(loc, new Attribute[0],
				mHelper.getGotoProcName(), new String[0],
				generateInParams(headPrdVarLists),
				new VarList[0],
				new Specification[0],
				new Body(loc,
						new VariableDeclaration[] { localVarDec },
						gotoProcBody.toArray(new Statement[gotoProcBody.size()])));
		return gotoProc;
	}



	private VarList[] generateInParams(final List<VarList> headPrdVarLists) {
		final List<VarList> resultList = new ArrayList<>();
		for (final VarList hpvl : headPrdVarLists) {
			assert hpvl.getIdentifiers().length == 1;
			final String id = hpvl.getIdentifiers()[0] + INPARAMSUFFIX;
			resultList.add(new VarList(hpvl.getLoc(), new String[] { id }, hpvl.getType()));
		}
		return resultList.toArray(new VarList[resultList.size()]);
	}

	private Expression getGotoVarExp() {
		return ExpressionFactory.constructIdentifierExpression(mHelper.getLoc(), BoogieType.TYPE_INT,
				mHelper.getGotoProcName(), new DeclarationInformation(StorageClass.LOCAL, mHelper.getGotoProcName()));
	}

	public VariableLHS constructLhsForHeadVar(final HcHeadVar inParam) {
		return ExpressionFactory.constructVariableLHS(mHelper.getLoc(),
				mHelper.getType(inParam.getSort()),
				inParam.getGloballyUniqueId(),
				new DeclarationInformation(StorageClass.LOCAL, mHelper.getGotoProcName()));
	}



	/**
	 *
	 * @param loc
	 * @param predSymbolToLabel null if non-goto mode
	 * @param predLabelToNumber
	 * @param hornClausesForHeadPred
	 * @param headPredQueue (updated)
	 * @param addedToQueueBefore (updated)
	 * @param allBodyPredVariables (updated)
	 * @return
	 */
	private List<Statement> generateNondetSwitchForPred(final ILocation loc,
			final Map<HcPredicateSymbol, Label> predSymbolToLabel, final Map<Label, Integer> predLabelToNumber,
			final Set<HornClause> hornClausesForHeadPred,
			final Deque<HcPredicateSymbol> headPredQueue, final Set<HcPredicateSymbol> addedToQueueBefore,
			final Set<HcBodyVar> allBodyPredVariables) {
		assert (predSymbolToLabel == null) == (predLabelToNumber == null);
		/*
		 * create the procedure body according to all Horn clauses with headPredSymbol as their head
		 */
		List<Statement> nondetSwitch = null;

		for (final HornClause hornClause : hornClausesForHeadPred) {

			allBodyPredVariables.addAll(hornClause.getBodyVariables());

			final List<Statement> branchBody = new ArrayList<>();
			final Statement assume =
					new AssumeStatement(loc, mHelper.translate(hornClause.getConstraintFormula()));
			branchBody.add(assume);

			for (int i = 0; i < hornClause.getNoBodyPredicates(); i++) {
				final HcPredicateSymbol bodyPredSym = hornClause.getBodyPredicates().get(i);
				final List<Term> bodyPredArgs = hornClause.getBodyPredToArgs().get(i);

				if (!addedToQueueBefore.contains(bodyPredSym)) {
					headPredQueue.push(bodyPredSym);
					addedToQueueBefore.add(bodyPredSym);
				}

				final List<Expression> translatedArguments = new ArrayList<>();
				// extra argument to choose the right label to jump to
				translatedArguments.add(ExpressionFactory.createIntegerLiteral(loc,
						predLabelToNumber.get(predSymbolToLabel.get(bodyPredSym)).toString()));
				translatedArguments.addAll(
						bodyPredArgs.stream().map(t -> mHelper.translate(t)).collect(Collectors.toList()));

				if (i == hornClause.getNoBodyPredicates() - 1) {
					// tail call is done as a goto
					mHelper.constructGotoReplacingTailCall(loc, branchBody, predSymbolToLabel.get(bodyPredSym), hornClause,
							bodyPredSym, translatedArguments);
				} else {
					// we have to rearrange the call arguments
					final CallStatement call = new CallStatement(loc, false, new VariableLHS[0],
							mHelper.predSymToMethodName(bodyPredSym),
							translatedArguments.toArray(new Expression[bodyPredArgs.size()]));
					branchBody.add(call);
				}
			}

			nondetSwitch = mHelper.addIteBranch(loc, nondetSwitch, branchBody,
				ExpressionFactory.constructBooleanWildCardExpression(loc));
		}
		return nondetSwitch;
	}



	public Unit getResult() {
		return mResult;
	}


	private Declaration constructMainEntryPointProcedure(final ILocation loc) {

		Statement[] statements;
		final Statement callToGotoProc = new CallStatement(loc, false, new VariableLHS[0],
				mHelper.getGotoProcName(), new Expression[0]);

		final Statement assertFalse = new AssertStatement(loc,
				ExpressionFactory.createBooleanLiteral(loc, false));

		statements = new Statement[] { callToGotoProc, assertFalse };

		final Body body = new Body(loc, new VariableDeclaration[0], statements);

		return new Procedure(loc, new Attribute[0], mHelper.getNameOfMainEntryPointProc(), new String[0],
				new VarList[0], new VarList[0], new Specification[0], body);
	}
}
