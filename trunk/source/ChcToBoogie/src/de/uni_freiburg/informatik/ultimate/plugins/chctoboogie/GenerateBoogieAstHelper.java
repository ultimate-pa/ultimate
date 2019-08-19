package de.uni_freiburg.informatik.ultimate.plugins.chctoboogie;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcHeadVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcVar;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.TypeSortTranslator;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public class GenerateBoogieAstHelper {

	private final ILocation mLocation;
	private final HcSymbolTable mHcSymbolTable;
	private final TypeSortTranslator mTypeSortTanslator;
	private final Term2Expression mTerm2Expression;
	private final HcPredicateSymbol mBottomPredSym;
	private final String mNameOfEntryPointProc;

	/**
	 * Stores for each array sort for which we need a dummy var the name of that dummy var.
	 * Updated on demand.
	 * Is used to declare the dummy vars in the Boogie program.
	 */
	private final Map<Sort, String> mArraySortToDummyVarName;

	public GenerateBoogieAstHelper(final ILocation location, final HcSymbolTable hcSymbolTable,
			final Term2Expression term2Expression, final TypeSortTranslator typeSortTranslator,
			final String nameOfMainEntryPointProc) {
		mLocation = location;
		mHcSymbolTable = hcSymbolTable;
		mNameOfEntryPointProc = nameOfMainEntryPointProc;

		mTypeSortTanslator = typeSortTranslator;
		mTerm2Expression = term2Expression;

		mBottomPredSym = mHcSymbolTable.getFalseHornClausePredicateSymbol();

		mArraySortToDummyVarName = new LinkedHashMap<>();
//		mAuxDeclarations = new ArrayList<>();
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
//			assert statementsToAddTo.get(0) instanceof AssumeStatement
//				|| statementsToAddTo.get(0) instanceof CallStatement;
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


	/**
	 * Auxiliary declarations that should be added to the Boogie program.
	 * (here, auxiliary means "not one of the procedures that provide the main behaviour of the program, the main proc
	 *  and the goto proc..)
	 *
	 * This should be called at the end of the construction of the program.
	 *
	 * @return
	 */
	public List<Declaration> getAuxDeclarations() {
		final List<Declaration> declarations = new ArrayList<>();

		declarations.addAll(getDeclarationsForSkolemFunctions());

		declarations.addAll(getDeclarationsForArrayDummyVars());

		return declarations;
	}

	private List<Declaration> getDeclarationsForArrayDummyVars() {
		final List<Declaration> declarations = new ArrayList<>();
		for (final Entry<Sort, String> en : mArraySortToDummyVarName.entrySet()) {
			declarations.add(new VariableDeclaration(mLocation, new Attribute[0],
					new VarList[] {
							new VarList(mLocation,
									new String[] { en.getValue() },
									getType(en.getKey()).toASTType(mLocation)) }));
		}
		return declarations;
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

	void updateLocalVarDecs(final List<VariableDeclaration> localVarDecs, final Set<HcVar> bpvs,
			final ILocation loc) {
		for (final HcVar bodyPredVar : bpvs) {
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



	public VariableLHS[] toVariableLhss(final Collection<? extends HcVar> hcVariables,
			final DeclarationInformation declInfo) {
		final List<VariableLHS> resultList = new ArrayList<>();
		for (final HcVar bv : hcVariables) {
			resultList.add(ExpressionFactory.constructVariableLHS(getLoc(),
					(BoogieType) mTypeSortTanslator.getType(bv.getSort()),
					bv.getGloballyUniqueId(), declInfo));//new DeclarationInformation(StorageClass.LOCAL, mGotoProcName)));
		}
		return resultList.toArray(new VariableLHS[resultList.size()]);
	}

	public Expression getDummyArgForArraySort(final Sort sort) {
		String varName = mArraySortToDummyVarName.get(sort);
		if (varName == null) {
			final String dummyArrayPrefix = "#dummy~";
			varName = dummyArrayPrefix + HornUtilConstants.sanitzeSortNameForBoogie(sort);
			mArraySortToDummyVarName.put(sort, varName);
		}
		return ExpressionFactory.constructIdentifierExpression(mLocation, getType(sort), varName, DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}
}
