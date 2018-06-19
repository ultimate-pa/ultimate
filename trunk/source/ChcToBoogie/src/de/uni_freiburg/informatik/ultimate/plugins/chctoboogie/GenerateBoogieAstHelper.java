package de.uni_freiburg.informatik.ultimate.plugins.chctoboogie;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcBodyVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TypeSortTranslator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class GenerateBoogieAstHelper {

	private final ILocation mLocation;
	private final HcSymbolTable mHcSymbolTable;
	private final TypeSortTranslator mTypeSortTanslator;
	private final Term2Expression mTerm2Expression;
	private final HcPredicateSymbol mBottomPredSym;
	private final String mNameOfEntryPointProc;
	private final String mGotoProcName;
	private final String mGotoVarName;

	public GenerateBoogieAstHelper(final ILocation location, final HcSymbolTable hcSymbolTable,
			final Term2Expression term2Expression, final TypeSortTranslator typeSortTranslator,
			final String nameOfMainEntryPointProc, final String gotoProcName,
			final String gotoVarName) {
		mLocation = location;
		mHcSymbolTable = hcSymbolTable;
		mNameOfEntryPointProc = nameOfMainEntryPointProc;
		mGotoProcName = gotoProcName;
		mGotoVarName = gotoVarName;

		mTypeSortTanslator = typeSortTranslator;
		mTerm2Expression = term2Expression;

		mBottomPredSym = mHcSymbolTable.getFalseHornClausePredicateSymbol();
	}

	ILocation getLoc() {
		return mLocation;
	}

	String predSymToMethodName(final HcPredicateSymbol predSym) {
		return mHcSymbolTable.getMethodNameForPredSymbol(predSym);
	}




	List<Statement> addIteBranch(final ILocation loc, final List<Statement> statementsToAddTo,
			final List<Statement> branchBody, final Expression condition) {
		if (statementsToAddTo == null) {
			return branchBody;
		} else if (statementsToAddTo.size() == 1 && statementsToAddTo.get(0) instanceof IfStatement) {
			final Statement[] oldIfStm = new Statement[] { statementsToAddTo.get(0)};

			final Statement newIfStm = new IfStatement(loc,
					condition,
//					ExpressionFactory.constructBooleanWildCardExpression(loc),
					branchBody.toArray(new Statement[branchBody.size()]),
					oldIfStm);

			return Collections.singletonList(newIfStm);
		} else {
			assert statementsToAddTo.get(0) instanceof AssumeStatement
				|| statementsToAddTo.get(0) instanceof CallStatement;
			final Statement newIfStm = new IfStatement(loc,
					condition,
//					ExpressionFactory.constructBooleanWildCardExpression(loc),
//					nondetSwitch.toArray(new Statement[nondetSwitch.size()]),
					branchBody.toArray(new Statement[branchBody.size()]),
					statementsToAddTo.toArray(new Statement[statementsToAddTo.size()]));

			return Collections.singletonList(newIfStm);
		}
	}

	ASTType getCorrespondingAstType(final ILocation loc, final Sort sort) {
		if (sort.getName().equals("Int")) {
			return new PrimitiveType(loc, BoogieType.TYPE_INT, "int");
		} else if (sort.getName().equals("Real")) {
			return new PrimitiveType(loc, BoogieType.TYPE_REAL, "real");
		} else if (sort.getName().equals("Bool")) {
			return new PrimitiveType(loc, BoogieType.TYPE_BOOL, "bool");
		} else if (sort.isArraySort()) {
			final List<Sort> args = Arrays.asList(sort.getArguments());
			final List<ASTType> converted =
					args.stream().map(arg -> getCorrespondingAstType(loc, arg)).collect(Collectors.toList());
			final IBoogieType boogieType = mTypeSortTanslator.getType(sort);
			return new ArrayType(loc, boogieType , new String[0],
					converted.subList(0, converted.size() - 1).toArray(new ASTType[converted.size() -1]),
					converted.get(converted.size() - 1));
		} else {
			throw new AssertionError("case not implemented");
		}
	}

		/**
	 * For each procedure we create here, the inParams are determined by the signature of the HornClausePredicateSymbol
	 * that is associated with the procedure.
	 * This methods computes those inParams in the right format.
	 *
	 * @param loc
	 * @param headPredSym
	 * @return
	 */
	VarList[] getInParamsForHeadPredSymbol(final ILocation loc, final HcPredicateSymbol headPredSym,
			final boolean constructIfNecessary) {
		final VarList[] result = new VarList[headPredSym.getArity()];
		final List<HcHeadVar> headVars = mHcSymbolTable.getHcHeadVarsForPredSym(headPredSym, constructIfNecessary);
		for (int i = 0; i < headPredSym.getArity(); i++) {
			final HcHeadVar hchv = headVars.get(i);
			final Sort sort = hchv.getTermVariable().getSort();
			final ASTType correspondingType = getCorrespondingAstType(loc, sort);
			final VarList vl = new VarList(loc, new String[] { hchv.getGloballyUniqueId() }, correspondingType);
			result[i] = vl;
		}
		return result;
	}


	VarList[] getInParamsForSorts(final ILocation loc, final Sort[] sorts) {
		final VarList[] result = new VarList[sorts.length];
		for (int i = 0; i < sorts.length; i++) {
			final Sort sort = sorts[i];
			final ASTType correspondingType = getCorrespondingAstType(loc, sort);
			final VarList vl = new VarList(loc, new String[] { "in_" + i }, correspondingType);
			result[i] = vl;
		}
		return result;

	}

	public String getNameOfMainEntryPointProc() {
		return mNameOfEntryPointProc;
	}

	public List<Declaration> getDeclarationsForSkolemFunctions() {
		final List<Declaration> declarations = new ArrayList<>();
		/*
		 * Add body-less boogie functions for the uninterpreted function appearing in constraints (e.g. skolem
		 *  functions)
		 */
		for (final Triple<String, Sort[], Sort> sf : mHcSymbolTable.getSkolemFunctions()) {
			final VarList[] inParams = getInParamsForSorts(getLoc(), sf.getSecond());
			final VarList outParam = getInParamsForSorts(getLoc(), new Sort[] { sf.getThird() })[0];
			final FunctionDeclaration boogieFun = new FunctionDeclaration(getLoc(), new Attribute[0], sf.getFirst(),
					new String[0], inParams, outParam);
			declarations.add(boogieFun);
		}
		return declarations;
	}

	void updateLocalVarDecs(final List<VariableDeclaration> localVarDecs, final Set<HcBodyVar> bpvs,
			final ILocation loc) {
		for (final HcBodyVar bodyPredVar : bpvs) {
			final String boogieVarName = bodyPredVar.getGloballyUniqueId();
			final Sort sort = bodyPredVar.getSort();
			final VarList varList = new VarList(loc, new String[] { boogieVarName },
					getCorrespondingAstType(loc, sort));
			localVarDecs.add(new VariableDeclaration(loc, new Attribute[0], new VarList[] { varList }));
		}
	}

	public Expression translate(final Term constraintFormula) {
		return mTerm2Expression.translate(constraintFormula);
	}

	public HcPredicateSymbol getBottomPredSym() {
		return mBottomPredSym;
	}

	public BoogieType getType(final Sort sort) {
		return (BoogieType) mTypeSortTanslator.getType(sort);
	}

	public HcSymbolTable getSymbolTable() {
		return mHcSymbolTable;
	}


//	/**
//	 *
//	 * @param loc
//	 * @param predSymbolToLabel null if non-goto mode
//	 * @param predLabelToNumber
//	 * @param hornClausesForHeadPred
//	 * @param headPredQueue (updated)
//	 * @param addedToQueueBefore (updated)
//	 * @param allBodyPredVariables (updated)
//	 * @return
//	 */
//	public List<Statement> generateNondetSwitchForPred(final ILocation loc,
//			final Map<HcPredicateSymbol, Label> predSymbolToLabel, final Map<Label, Integer> predLabelToNumber,
//			final Set<HornClause> hornClausesForHeadPred,
//			final Deque<HcPredicateSymbol> headPredQueue, final Set<HcPredicateSymbol> addedToQueueBefore,
//			final Set<HcBodyVar> allBodyPredVariables) {
//		assert (predSymbolToLabel == null) == (predLabelToNumber == null);
//		/*
//		 * create the procedure body according to all Horn clauses with headPredSymbol as their head
//		 */
//		List<Statement> nondetSwitch = null;
//
//		for (final HornClause hornClause : hornClausesForHeadPred) {
//
//			allBodyPredVariables.addAll(hornClause.getBodyVariables());
//
//			final List<Statement> branchBody = new ArrayList<>();
//			final Statement assume =
//					new AssumeStatement(loc, translate(hornClause.getConstraintFormula()));
//			branchBody.add(assume);
//
//			for (int i = 0; i < hornClause.getNoBodyPredicates(); i++) {
//				final HcPredicateSymbol bodyPredSym = hornClause.getBodyPredicates().get(i);
//				final List<Term> bodyPredArgs = hornClause.getBodyPredToArgs().get(i);
//
//				if (!addedToQueueBefore.contains(bodyPredSym)) {
//					headPredQueue.push(bodyPredSym);
//					addedToQueueBefore.add(bodyPredSym);
//				}
//
//				final List<Expression> translatedArguments = new ArrayList<>();
//				if (predSymbolToLabel != null) {
//					// extra argument to choose the right label to jump to
//					translatedArguments.add(ExpressionFactory.createIntegerLiteral(loc,
//							predLabelToNumber.get(predSymbolToLabel.get(bodyPredSym)).toString()));
//				}
//				translatedArguments.addAll(
//						bodyPredArgs.stream().map(t -> translate(t)).collect(Collectors.toList()));
//
//				if (i == hornClause.getNoBodyPredicates() - 1 && predSymbolToLabel != null) {
//					// tail call is done as a goto
//					constructGotoReplacingTailCall(loc, branchBody, predSymbolToLabel.get(bodyPredSym), hornClause,
//							bodyPredSym, translatedArguments);
//				} else if (predSymbolToLabel != null) {
//					// we have to rearrange the call arguments
//					final CallStatement call = new CallStatement(loc, false, new VariableLHS[0],
//							predSymToMethodName(bodyPredSym),
//							translatedArguments.toArray(new Expression[bodyPredArgs.size()]));
//					branchBody.add(call);
//				} else  {
//					final CallStatement call = new CallStatement(loc, false, new VariableLHS[0],
//							predSymToMethodName(bodyPredSym),
//							translatedArguments.toArray(new Expression[bodyPredArgs.size()]));
//					branchBody.add(call);
//				}
//			}
//
//			nondetSwitch = addIteBranch(loc, nondetSwitch, branchBody,
//				ExpressionFactory.constructBooleanWildCardExpression(loc));
//		}
//		return nondetSwitch;
//	}

	/**
	 *
	 * @param loc
	 * @param branchBody (updated)
	 * @param labelForBodyPredSym
	 * @param hornClause
	 * @param bodyPredSym
	 * @param translatedArguments (contains goto switch var)
	 */
	void constructGotoReplacingTailCall(final ILocation loc, final List<Statement> branchBody,
			final Label labelForBodyPredSym, final HornClause hornClause,
			final HcPredicateSymbol bodyPredSym, final List<Expression> translatedArguments) {

		// assignment of head vars (analogous to what a call would have done implicitly)
		{
			final List<VariableLHS> lhss = new ArrayList<>();
			lhss.add(getGotoVarLhs());
			lhss.addAll(Arrays.asList(toVariableLhss(mHcSymbolTable.getHcHeadVarsForPredSym(bodyPredSym, false))));

			final Statement assignment = StatementFactory.constructAssignmentStatement(loc,
					lhss.toArray(new LeftHandSide[lhss.size()]),
					translatedArguments.toArray(new Expression[translatedArguments.size()]));
			branchBody.add(assignment);
		}

		// havoc body vars
		branchBody.add(new HavocStatement(loc, toVariableLhss(hornClause.getBodyVariables())));

		// add goto statement
		branchBody.add(new GotoStatement(loc, new String[] {
				labelForBodyPredSym.toString() }));
	}

	private VariableLHS[] toVariableLhss(final Collection<? extends HcVar> hcVariables) {
		final List<VariableLHS> resultList = new ArrayList<>();
		for (final HcVar bv : hcVariables) {
			resultList.add(ExpressionFactory.constructVariableLHS(getLoc(),
					(BoogieType) mTypeSortTanslator.getType(bv.getSort()),
					bv.getGloballyUniqueId(), new DeclarationInformation(StorageClass.LOCAL, mGotoProcName)));
		}
		return resultList.toArray(new VariableLHS[resultList.size()]);
	}

	Expression getArgumentVarExp(final int index, final Sort sort) {
		return ExpressionFactory.constructIdentifierExpression(getLoc(), getType(sort),
				getArgumentVarId(index, sort), new DeclarationInformation(StorageClass.LOCAL, mGotoProcName));
	}

	private String getArgumentVarId(final int index, final Sort sort) {
		return "gpav_" + index + "_" + sort;
	}

	VariableLHS getArgumentVarLhs(final int index, final Sort sort) {
		return ExpressionFactory.constructVariableLHS(getLoc(), getType(sort),
				getArgumentVarId(index, sort), new DeclarationInformation(StorageClass.LOCAL, mGotoProcName));
	}

	public String getGotoProcName() {
		return mGotoProcName;
	}

	private VariableLHS getGotoVarLhs() {
		return ExpressionFactory.constructVariableLHS(getLoc(), BoogieType.TYPE_INT, mGotoVarName,
				new DeclarationInformation(StorageClass.LOCAL, mGotoProcName));
	}
}
