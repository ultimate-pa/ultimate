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
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
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
import de.uni_freiburg.informatik.ultimate.lib.chc.ChcPreMetaInfoProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class GenerateGotoBoogieAst {

//	private static final String INPARAMSUFFIX = "_inprm";

	private final Unit mResult;

	private final GenerateBoogieAstHelper mHelper;

	private final HcSymbolTable mHcSymbolTable;

	private final ChcPreMetaInfoProvider mChcInfo;

	private final NestedMap2<Integer, Sort, String> mIndexToSortToGotoProcArgId;
	private final List<Triple<Integer, Sort, String>> mIndexToSortToGotoProcArgIdList;

	private final String mGotoVarName;

	private final Set<HcPredicateSymbol> mPredicatesThatHaveANonTailCall;

	public GenerateGotoBoogieAst(final ChcPreMetaInfoProvider preAnalysis,
			final GenerateBoogieAstHelper helper,
			final String gotoVarName) {
		mHelper = helper;
		mHcSymbolTable = helper.getSymbolTable();
		mChcInfo = preAnalysis;

		mGotoVarName = gotoVarName;

		mPredicatesThatHaveANonTailCall = new HashSet<>();
		mPredicatesThatHaveANonTailCall.add(helper.getBottomPredSym());

		mIndexToSortToGotoProcArgId = new NestedMap2<>();
		mIndexToSortToGotoProcArgIdList = new ArrayList<>();
		// fills the map
		constructGotoProcArgIds();

		mResult = generateBoogieAstWithGotos();
	}

	public Unit getResult() {
		return mResult;
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
	private Unit generateBoogieAstWithGotos() {
//			final HashRelation<HcPredicateSymbol, HornClause> hornClauseHeadPredicateToHornClauses) {

		final ILocation loc = mHelper.getLoc();

		// variable declarations of the main procedure
		final List<Declaration> declarations = new ArrayList<>();
		// the statements of the main procedure
		final List<Statement> labeledBlocks = new ArrayList<>();

		// label corresponding the "False" procedure block
//		final Label falseLabel = new Label(loc, "False");

		// goto var
//		final IdentifierExpression gotoVarExp = ExpressionFactory.constructIdentifierExpression(loc, BoogieType.TYPE_INT,
//				mGotoVarName, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, mGotoProcName));

		final Map<HcPredicateSymbol, Label> predSymbolToLabel = new LinkedHashMap<>();
		final Map<Label, Integer> predLabelToNumber = new LinkedHashMap<>();
		{
			Integer predsymCounter = 0;
			// generate the labels
//			for (final HcPredicateSymbol predSym : mChcInfo.getHornClausesSorted().getDomain()) {
			for (final HcPredicateSymbol predSym : mChcInfo.getAllReachablePredSymbols()) {
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

		final Set<HcVar> allBodyPredVariables = new HashSet<>();

		while (!headPredQueue.isEmpty()) {
			// breadth-first (pollFirst) or depth-first (pop) should not matter here
			final HcPredicateSymbol headPredSymbol = headPredQueue.pop();

			final Set<HornClause> hornClausesForHeadPred =
					mChcInfo.getHornClausesSorted().getImage(headPredSymbol);

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
//				assert nondetSwitch != null && nondetSwitch.get(nondetSwitch.size() - 1) instanceof GotoStatement;
				labeledBlocks.addAll(nondetSwitch);
			}
		}

		declarations.add(constructGotoProc(loc, labeledBlocks, predSymbolToLabel, predLabelToNumber,
				allBodyPredVariables));

		// add the main entry point
		declarations.add(constructMainEntryPointProcedure(loc,
				predLabelToNumber.get(predSymbolToLabel.get(mHelper.getBottomPredSym()))));

		declarations.addAll(mHelper.getAuxDeclarations());

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
	private Procedure constructGotoProc(final ILocation loc, final List<Statement> labeledBlocks,
			final Map<HcPredicateSymbol, Label> predSymbolToLabel, final Map<Label, Integer> predLabelToNumber,
			final Set<HcVar> allBodyPredVariables) {
		final List<Statement> gotoProcBody = new ArrayList<>();
		// method starts with a switch that jumps according to the argument
		{
			List<Statement> predSwitch = null;

			for (final Entry<HcPredicateSymbol, Label> en : predSymbolToLabel.entrySet()) {

				if (!mPredicatesThatHaveANonTailCall.contains(en.getKey())) {
					// switch branch is unecessary, leave it out
					continue;
				}

				final HcPredicateSymbol predSym = en.getKey();
				final Label predSymLabel = en.getValue();
				final Integer predSymNumber = predLabelToNumber.get(predSymLabel);


				final List<Statement> branchBody = new ArrayList<>();


				{
					final List<LeftHandSide> lhss = new ArrayList<>();
					final List<Expression> rhss = new ArrayList<>();



					for (final HcHeadVar headVar : mHcSymbolTable.getHcHeadVarsForPredSym(predSym, false)) {
						lhss.add(constructLhsForHeadVar(headVar));
						rhss.add(getArgumentVarExp(headVar.getIndex(), headVar.getSort()));
					}

					if (lhss.size() > 0) {
						final Statement assignment = StatementFactory.constructAssignmentStatement(loc,
								lhss.toArray(new LeftHandSide[lhss.size()]),
								rhss.toArray(new Expression[rhss.size()]));
						branchBody.add(assignment);
					}

					branchBody.add(new GotoStatement(loc, new String[]{ en.getValue().getName() }));
				}

				final Expression condition = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ,
						getGotoVarExp(), ExpressionFactory.createIntegerLiteral(loc, predSymNumber.toString()));
				predSwitch = mHelper.addIteBranch(loc, predSwitch, branchBody, condition);
			}


			// gotoSwitch := gotoSwitch_in
			final Statement gotoSwitchAssign = StatementFactory.constructAssignmentStatement(loc,
					new LeftHandSide[] { ExpressionFactory.constructVariableLHS(loc, BoogieType.TYPE_INT, getGotoVarName(),
							new DeclarationInformation(StorageClass.LOCAL, getGotoProcName())) },
					new Expression[] { ExpressionFactory.constructIdentifierExpression(loc, BoogieType.TYPE_INT,
							getGotoVarInParamName(),
							new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, getGotoProcName())) });

			gotoProcBody.add(gotoSwitchAssign);
			gotoProcBody.addAll(predSwitch);
			gotoProcBody.addAll(labeledBlocks);
		}


		// the args of the goto proc are all head vars and all body vars of all occurring predicates
		final VariableDeclaration localVarDec;
		{
			final List<VarList> gotoProgLocaLVarLists = new ArrayList<>();


			// goto switch
			gotoProgLocaLVarLists.add(new VarList(loc, new String[] { getGotoVarName() },
					new PrimitiveType(loc, BoogieType.TYPE_INT, "int")));

			// head vars
			final List<VarList> headPrdVarLists = new ArrayList<>();
			predSymbolToLabel.keySet()
			.forEach(ps -> mHcSymbolTable.getHcHeadVarsForPredSym(ps, false)
					.forEach(hcv -> headPrdVarLists.add(new VarList(loc, new String[] { hcv.getGloballyUniqueId() },
							mHelper.getCorrespondingAstType(loc, hcv.getSort())))));
			gotoProgLocaLVarLists.addAll(headPrdVarLists);

			// body vars
			allBodyPredVariables.forEach(hcv -> gotoProgLocaLVarLists.add(
					new VarList(loc, new String[] { hcv.getGloballyUniqueId() },
							mHelper.getCorrespondingAstType(loc, hcv.getSort()))));

			localVarDec = new VariableDeclaration(loc, new Attribute[0],
					gotoProgLocaLVarLists.toArray(new VarList[gotoProgLocaLVarLists.size()]));
		}

		final Procedure gotoProc = new Procedure(loc, new Attribute[0],
				getGotoProcName(), new String[0],
				generateGotoProcInParams(),
				new VarList[0],
				new Specification[0],
				new Body(loc,
						new VariableDeclaration[] { localVarDec },
						gotoProcBody.toArray(new Statement[gotoProcBody.size()])));
		return gotoProc;
	}



//	private VarList[] generateInParams(final List<VarList> headPrdVarLists) {
	private VarList[] generateGotoProcInParams() {
		final ILocation loc = mHelper.getLoc();
		final List<VarList> resultList = new ArrayList<>();

		// first inparam: goto var
		resultList.add(new VarList(loc, new String[] { getGotoVarInParamName() },
				new PrimitiveType(loc, BoogieType.TYPE_INT, "int")));

//		for (final HcHeadVar headVar : mChcInfo.getAllHeadHcVarsAsList()) {
//			final String id = headVar.getGloballyUniqueId() + INPARAMSUFFIX;
//		for (final String id : constructGotoProcArgIds()) {
//		for (final Triple<Integer, Sort, String> triple : mIndexToSortToGotoProcArgId.entrySet()) {
		for (final Triple<Integer, Sort, String> triple : mIndexToSortToGotoProcArgIdList) {
			resultList.add(new VarList(loc, new String[] { triple.getThird() },
					mHelper.getCorrespondingAstType(loc, triple.getSecond())));
		}

//		for (final VarList hpvl : headPrdVarLists) {
//			assert hpvl.getIdentifiers().length == 1;
//			final String id = hpvl.getIdentifiers()[0] + INPARAMSUFFIX;
//			resultList.add(new VarList(hpvl.getLoc(), new String[] { id }, hpvl.getType()));
//		}
		return resultList.toArray(new VarList[resultList.size()]);
	}

	private String getGotoVarInParamName() {
		return getGotoVarName() + "_in";
	}

	private Expression getGotoVarExp() {
		return ExpressionFactory.constructIdentifierExpression(mHelper.getLoc(), BoogieType.TYPE_INT,
				getGotoVarName(), new DeclarationInformation(StorageClass.LOCAL, getGotoProcName()));
	}

	private VariableLHS constructLhsForHeadVar(final HcHeadVar inParam) {
		return ExpressionFactory.constructVariableLHS(mHelper.getLoc(),
				mHelper.getType(inParam.getSort()),
				inParam.getGloballyUniqueId(),
				new DeclarationInformation(StorageClass.LOCAL, getGotoProcName()));
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
			final Set<HcVar> allBodyPredVariables) {
		assert (predSymbolToLabel == null) == (predLabelToNumber == null);
		/*
		 * create the procedure body according to all Horn clauses with headPredSymbol as their head
		 */
		List<Statement> nondetSwitch = null;

		for (final HornClause hornClause : hornClausesForHeadPred) {
			if (SmtUtils.isFalseLiteral(hornClause.getConstraintFormula())) {
				// branch with an "assume false" --> can be skipped
				continue;
			}

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


				final IntegerLiteral targetLabelNumber = ExpressionFactory.createIntegerLiteral(loc,
									predLabelToNumber.get(predSymbolToLabel.get(bodyPredSym)).toString());
				final List<Expression> translatedArgs =
						bodyPredArgs.stream().map(t -> mHelper.translate(t)).collect(Collectors.toList());

				if (i == hornClause.getNoBodyPredicates() - 1) {
					// tail call is done as a goto
					constructGotoReplacingTailCall(loc, branchBody,
							predSymbolToLabel.get(bodyPredSym),
							hornClause,
							bodyPredSym,
							targetLabelNumber,
							translatedArgs
							);
				} else {
					// we have to rearrange the call arguments

					mPredicatesThatHaveANonTailCall.add(bodyPredSym);

					final List<Expression> splatArgs = new ArrayList<>();
					splatArgs.add(targetLabelNumber);

					int bodyVarIndex = 0;

//					for (final HcHeadVar headVar : mChcInfo.getAllHeadHcVarsAsList()) {
					for (final Triple<Integer, Sort, String> tr : mIndexToSortToGotoProcArgIdList) {

//						final Term currentBodyPredArg = bodyPredArgs.get(bodyVarIndex);

//						if (currentBodyPredArg.getSort().equals(headVar.getSort())) {
						if (bodyVarIndex < bodyPredArgs.size() &&
								bodyPredArgs.get(bodyVarIndex).getSort().equals(tr.getSecond())) {
//							splatArgs.add(mHelper.translate(currentBodyPredArg));
							splatArgs.add(translatedArgs.get(bodyVarIndex));
							bodyVarIndex++;
						} else {
//							splatArgs.add(getDummyArgForSort(headVar.getSort()));
							splatArgs.add(getDummyArgForSort(tr.getSecond()));
						}
					}

					final CallStatement call = new CallStatement(loc, false, new VariableLHS[0],
							getGotoProcName(),
//							mHelper.predSymToMethodName(bodyPredSym),
							splatArgs.toArray(new Expression[bodyPredArgs.size()]));
					branchBody.add(call);
				}
			}

			if (hornClause.getNoBodyPredicates() == 0) {
				branchBody.add(new ReturnStatement(loc));
			}

			nondetSwitch = mHelper.addIteBranch(loc, nondetSwitch, branchBody,
				ExpressionFactory.constructBooleanWildCardExpression(loc));
		}
		return nondetSwitch;
	}



	private Expression getDummyArgForSort(final Sort sort) {
		if ("Bool".equals(sort.getName())) {
			return ExpressionFactory.createBooleanLiteral(mHelper.getLoc(), false);
		} else if ("Int".equals(sort.getName())) {
			return ExpressionFactory.createIntegerLiteral(mHelper.getLoc(), "0");
		} else if ("Real".equals(sort.getName())) {
			return ExpressionFactory.createRealLiteral(mHelper.getLoc(), "0");
		} else {
			return mHelper.getDummyArgForArraySort(sort);
		}
	}

	private Declaration constructMainEntryPointProcedure(final ILocation loc, final Integer falseLabelGotoNumber) {

		Expression[] gotoProcCallArgs;
		{
			final List<Expression> gpcas = new ArrayList<>();
			gpcas.add(ExpressionFactory.createIntegerLiteral(loc, falseLabelGotoNumber.toString()));
			for (final Triple<Integer, Sort, String> tr : mIndexToSortToGotoProcArgIdList) {
				// fill the rest with dummy args
				gpcas.add(getDummyArgForSort(tr.getSecond()));
			}
			gotoProcCallArgs = gpcas.toArray(new Expression[gpcas.size()]);
		}

		Statement[] statements;
		final Statement callToGotoProc = new CallStatement(loc, false, new VariableLHS[0],
				getGotoProcName(), gotoProcCallArgs);

		final Statement assertFalse = new AssertStatement(loc,
				ExpressionFactory.createBooleanLiteral(loc, false));

		statements = new Statement[] { callToGotoProc, assertFalse };

		final Body body = new Body(loc, new VariableDeclaration[0], statements);

		return new Procedure(loc, new Attribute[0], mHelper.getNameOfMainEntryPointProc(), new String[0],
				new VarList[0], new VarList[0], new Specification[0], body);
	}


	/**
	 *  (not including the goto var)
	 * @return
	 */
	private void constructGotoProcArgIds() {
//		final Set<String> result = new LinkedHashSet<>();
		for (final HcHeadVar hv : mChcInfo.getAllHeadHcVarsAsList()) {
//			final String argId = getArgumentVarId(hv.getIndex(), hv.getSort());
			final boolean isNew = constructArgumentVarId(hv.getIndex(), hv.getSort());
			if (isNew) {
				mIndexToSortToGotoProcArgIdList.add(
						new Triple<>(hv.getIndex(), hv.getSort(), getArgumentVarId(hv.getIndex(), hv.getSort())));
			}
//			result.add(argId);
		}
//		return new ArrayList<>(result);
	}

	Expression getArgumentVarExp(final int index, final Sort sort) {
		return ExpressionFactory.constructIdentifierExpression(mHelper.getLoc(), mHelper.getType(sort),
				getArgumentVarId(index, sort), new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, getGotoProcName()));
	}


	/**
	 *
	 * @return true iff was newly constructed
	 */
	private boolean constructArgumentVarId(final int index, final Sort sort) {
		String result = mIndexToSortToGotoProcArgId.get(index, sort);
		if (result == null) {
			result = "gpav_" + index + "_" + HornUtilConstants.sanitzeSortNameForBoogie(sort);
			mIndexToSortToGotoProcArgId.put(index, sort, result);
			return true;
		}
		return false;
	}

	private String getArgumentVarId(final int index, final Sort sort) {
		final String result = mIndexToSortToGotoProcArgId.get(index, sort);
		assert result != null;
//		if (result == null) {
//			constructArgumentVarId(index, sort);
//			result = mIndexToSortToGotoProcArgId.get(index, sort);
//		}
		return result;
	}

	VariableLHS getArgumentVarLhs(final int index, final Sort sort) {
		return ExpressionFactory.constructVariableLHS(mHelper.getLoc(), mHelper.getType(sort),
				getArgumentVarId(index, sort), new DeclarationInformation(StorageClass.LOCAL, getGotoProcName()));
	}

	public String getGotoProcName() {
		return HornUtilConstants.GOTO_PROC_NAME;
	}

	private VariableLHS getGotoVarLhs() {
		return ExpressionFactory.constructVariableLHS(mHelper.getLoc(), BoogieType.TYPE_INT, mGotoVarName,
				new DeclarationInformation(StorageClass.LOCAL, getGotoProcName()));
	}

	private String getGotoVarName() {
		return mGotoVarName;
	}

	/**
	 *
	 * @param loc
	 * @param branchBody (updated)
	 * @param labelForBodyPredSym
	 * @param hornClause
	 * @param bodyPredSym
	 * @param integerLiteral
	 * @param translatedArguments (contains goto switch var)
	 */
	private void constructGotoReplacingTailCall(final ILocation loc, final List<Statement> branchBody,
			final Label labelForBodyPredSym, final HornClause hornClause,
			final HcPredicateSymbol bodyPredSym,
			final IntegerLiteral predicateLabelNumberToJumpTo,
			final List<Expression> translatedArguments) {

		// EDIT: makes no sense -- we are using a direct goto, the switch will not be reached from here..
//		final Statement gotoVarAssignment = StatementFactory.constructAssignmentStatement(loc,
//				new VariableLHS[] { getGotoVarLhs() },
//				new Expression[] { predicateLabelNumberToJumpTo });
//		branchBody.add(gotoVarAssignment);

		if (translatedArguments.size() > 0) {
			// assignment of head vars (analogous to what a call would have done implicitly)
			final Statement argAssignment = StatementFactory.constructAssignmentStatement(loc,
					mHelper.toVariableLhss(mHcSymbolTable.getHcHeadVarsForPredSym(bodyPredSym, false),
							new DeclarationInformation(StorageClass.LOCAL, getGotoProcName())),
					translatedArguments.toArray(new Expression[translatedArguments.size()]));
			branchBody.add(argAssignment);
		}
		if (hornClause.getBodyVariables().size() > 0) {
			// havoc body vars
			branchBody.add(new HavocStatement(loc, mHelper.toVariableLhss(hornClause.getBodyVariables(),
					new DeclarationInformation(StorageClass.LOCAL, getGotoProcName()))));
		}

		// add goto statement
		branchBody.add(new GotoStatement(loc, new String[] { labelForBodyPredSym.getName().toString() }));
	}
}
