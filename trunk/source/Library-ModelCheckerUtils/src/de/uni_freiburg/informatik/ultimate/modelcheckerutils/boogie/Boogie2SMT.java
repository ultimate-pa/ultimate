/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnsupportedSyntaxResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.IIdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;

/**
 * Main class for the translation from Boogie to SMT. Constructs other Objects needed for this translation.
 *
 * @author Matthias Heizmann
 *
 */
public class Boogie2SMT {

	public static final int HARDCODED_SERIALNUMBER_FOR_AXIOMS = 0;

	private final BoogieDeclarations mBoogieDeclarations;
	private final ManagedScript mScript;

	private final TypeSortTranslator mTypeSortTranslator;
	private final IOperationTranslator mOperationTranslator;
	private final Boogie2SmtSymbolTable mBoogie2SmtSymbolTable;
	private final Expression2Term mExpression2Term;
	private final Term2Expression mTerm2Expression;

	private final Statements2TransFormula mStatements2TransFormula;

	// private final ConstOnlyIdentifierTranslator mConstOnlyIdentifierTranslator;

	private final IPredicate mAxioms;

	private final IUltimateServiceProvider mServices;

	private final ConcurrencyInformation mConcurrencyInformation;

	public Boogie2SMT(final ManagedScript maScript, final BoogieDeclarations boogieDeclarations,
			final boolean bitvectorInsteadOfInt, final IUltimateServiceProvider services,
			final boolean simplePartialSkolemization, final List<ForkStatement> forkStatements) {
		mServices = services;
		mBoogieDeclarations = boogieDeclarations;
		mScript = maScript;

		if (bitvectorInsteadOfInt) {
			mTypeSortTranslator = new TypeSortTranslatorBitvectorWorkaround(boogieDeclarations.getTypeDeclarations(),
					mScript.getScript(), mServices);
			mConcurrencyInformation = constructConcurrencyInformation(forkStatements, mScript, mTypeSortTranslator);
			final Set<IProgramNonOldVar> concurInUseVars;
			final Set<IProgramNonOldVar[]> concurIdVars;
			if (mConcurrencyInformation == null) {
				concurInUseVars = Collections.emptySet();
				concurIdVars = Collections.emptySet();
			} else {
				concurInUseVars = new HashSet<>();
				concurIdVars = new HashSet<>();
				concurInUseVars.addAll(mConcurrencyInformation.getThreadInUseVars().entrySet().stream().map(Entry::getValue)
						.collect(Collectors.toSet()));
				concurIdVars.addAll(mConcurrencyInformation.getProcedureNameThreadIdMap().entrySet().stream().map(Entry::getValue)
						.collect(Collectors.toSet()));
			}
			mBoogie2SmtSymbolTable = new Boogie2SmtSymbolTable(boogieDeclarations, mScript, mTypeSortTranslator, concurInUseVars);
			// TODO: add concurIdVars to mBoogie2SmtSymbolTable
			mOperationTranslator =
					new BitvectorWorkaroundOperationTranslator(mBoogie2SmtSymbolTable, mScript.getScript());
			mExpression2Term = new Expression2Term(mServices, mScript.getScript(), mTypeSortTranslator,
					mBoogie2SmtSymbolTable, mOperationTranslator, mScript);
		} else {
			mTypeSortTranslator =
					new TypeSortTranslator(boogieDeclarations.getTypeDeclarations(), mScript.getScript(), mServices);
			mConcurrencyInformation = constructConcurrencyInformation(forkStatements, mScript, mTypeSortTranslator);
			final Set<IProgramNonOldVar> concurInUseVars;
			final Set<IProgramNonOldVar[]> concurIdVars;
			if (mConcurrencyInformation == null) {
				concurInUseVars = Collections.emptySet();
				concurIdVars = Collections.emptySet();
			} else {
				concurInUseVars = new HashSet<>();
				concurIdVars = new HashSet<>();
				concurInUseVars.addAll(mConcurrencyInformation.getThreadInUseVars().entrySet().stream().map(Entry::getValue)
						.collect(Collectors.toSet()));
				concurIdVars.addAll(mConcurrencyInformation.getProcedureNameThreadIdMap().entrySet().stream().map(Entry::getValue)
						.collect(Collectors.toSet()));
			}
			mBoogie2SmtSymbolTable = new Boogie2SmtSymbolTable(boogieDeclarations, mScript, mTypeSortTranslator, concurInUseVars);
			// TODO: add concurIdVars to mBoogie2SmtSymbolTable  ? Why duplicated code here?

			mOperationTranslator = new DefaultOperationTranslator(mBoogie2SmtSymbolTable, mScript.getScript());
			mExpression2Term = new Expression2Term(mServices, mScript.getScript(), mTypeSortTranslator,
					mBoogie2SmtSymbolTable, mOperationTranslator, mScript);
		}

		final ArrayList<Term> axiomList = new ArrayList<>(boogieDeclarations.getAxioms().size());
		for (final Axiom decl : boogieDeclarations.getAxioms()) {
			final Term term = declareAxiom(decl, mExpression2Term);
			axiomList.add(term);
		}
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(SmtUtils.and(mScript.getScript(), axiomList),
				maScript.getScript(), mBoogie2SmtSymbolTable);
		assert tvp.getVars().isEmpty() : "axioms must not have variables";
		mAxioms = new BasicPredicate(HARDCODED_SERIALNUMBER_FOR_AXIOMS, tvp.getProcedures(), tvp.getFormula(),
				tvp.getVars(), tvp.getClosedFormula());
		mStatements2TransFormula = new Statements2TransFormula(this, mServices, mExpression2Term,
				simplePartialSkolemization);
		mTerm2Expression = new Term2Expression(mTypeSortTranslator, mBoogie2SmtSymbolTable, maScript);

	}

	public Script getScript() {
		return mScript.getScript();
	}

	public ManagedScript getManagedScript() {
		return mScript;
	}

	public Term2Expression getTerm2Expression() {
		return mTerm2Expression;
	}

	public Expression2Term getExpression2Term() {
		return mExpression2Term;
	}

	static String quoteId(final String id) {
		// return Term.quoteId(id);
		return id;
	}

	public Boogie2SmtSymbolTable getBoogie2SmtSymbolTable() {
		return mBoogie2SmtSymbolTable;
	}

	public Statements2TransFormula getStatements2TransFormula() {
		return mStatements2TransFormula;
	}

	public BoogieDeclarations getBoogieDeclarations() {
		return mBoogieDeclarations;
	}

	public TypeSortTranslator getTypeSortTranslator() {
		return mTypeSortTranslator;
	}

	// ConstOnlyIdentifierTranslator getConstOnlyIdentifierTranslator() {
	// return mConstOnlyIdentifierTranslator;
	// }

	public IPredicate getAxioms() {
		return mAxioms;
	}

	public ConcurrencyInformation getConcurrencyInformation() {
		return mConcurrencyInformation;
	}

	private Term declareAxiom(final Axiom ax, final Expression2Term expression2term) {
		final ConstOnlyIdentifierTranslator coit = new ConstOnlyIdentifierTranslator();
		final IIdentifierTranslator[] its = new IIdentifierTranslator[] { coit };
		final Term closedTerm = expression2term.translateToTerm(its, ax.getFormula()).getTerm();
		mScript.getScript().assertTerm(closedTerm);
		return closedTerm;
	}

	public static void reportUnsupportedSyntax(final BoogieASTNode astNode, final String longDescription,
			final IUltimateServiceProvider services) {
		final UnsupportedSyntaxResult<BoogieASTNode> result = new UnsupportedSyntaxResult<>(astNode,
				ModelCheckerUtils.PLUGIN_ID, services.getBacktranslationService(), longDescription);
		services.getResultService().reportResult(ModelCheckerUtils.PLUGIN_ID, result);
		services.getProgressMonitorService().cancelToolchain();
	}

	private static ConcurrencyInformation constructConcurrencyInformation(final List<ForkStatement> forkStatements,
			final ManagedScript mgdScript, final TypeSortTranslator typeSortTranslator) {
		ConcurrencyInformation concurInfo;
		if (forkStatements.isEmpty()) {
			concurInfo = null;
		} else {
			final Map<String, BoogieNonOldVar> mProcedureNameToThreadInUseMap = constructProcedureNameToThreadInUseMap(
					forkStatements, mgdScript);
			final Map<String, BoogieNonOldVar[]> procedureNameToThreadIdMap = constructProcedureNameToThreadIdMap(
					forkStatements, mgdScript, typeSortTranslator);
			concurInfo = new ConcurrencyInformation(mProcedureNameToThreadInUseMap, procedureNameToThreadIdMap);
		}
		return concurInfo;
	}

	private static Map<String, BoogieNonOldVar> constructProcedureNameToThreadInUseMap(
			final List<ForkStatement> forkStatements, final ManagedScript mgdScript) {
		final Map<String, BoogieNonOldVar> result = new HashMap<>();
		for (final ForkStatement st : forkStatements) {
			final BoogieNonOldVar threadInUseVar = constructThreadInUseVariable(st, mgdScript);
			result.put(st.getMethodName(), threadInUseVar);
		}
		return result;
	}

	private static Map<String, BoogieNonOldVar[]> constructProcedureNameToThreadIdMap(
			final List<ForkStatement> forkStatements, final ManagedScript mgdScript,
			final TypeSortTranslator typeSortTranslator) {
		final Map<String, BoogieNonOldVar[]> result = new HashMap<>();
		for (final ForkStatement st : forkStatements) {
			final BoogieNonOldVar[] threadIdVars = constructThreadIdVariable(st, mgdScript, typeSortTranslator);
			result.put(st.getMethodName(), threadIdVars);
		}
		return result;
	}

	public static BoogieNonOldVar constructThreadInUseVariable(final ForkStatement st, final ManagedScript mgdScript) {
		final Sort booleanSort = SmtSortUtils.getBoolSort(mgdScript);
		final BoogieNonOldVar threadInUseVar = constructThreadAuxiliaryVariable("th_" + st.getMethodName() + "_inUse",
				booleanSort, mgdScript);
		return threadInUseVar;
	}

	public static BoogieNonOldVar[] constructThreadIdVariable(final ForkStatement st, final ManagedScript mgdScript,
			final TypeSortTranslator typeSortTranslator) {
		final BoogieNonOldVar[] threadIdVars = new BoogieNonOldVar[st.getForkID().length];
		int i = 0;
		for (final Expression forkId : st.getForkID()) {
			final Sort expressionSort = typeSortTranslator.getSort(forkId.getType(), st);
			threadIdVars[i] = constructThreadAuxiliaryVariable("thidvar" + i + "_" + st.getMethodName(), expressionSort, mgdScript);
			i++;
		}
		return threadIdVars;
	}


	/**
	 * TODO Concurrent Boogie:
	 */
	public static BoogieNonOldVar constructThreadAuxiliaryVariable(final String id, final Sort sort,
			final ManagedScript mgdScript) {
		mgdScript.lock(id);
		final BoogieNonOldVar var = ProgramVarUtils.constructGlobalProgramVarPair(id, sort, mgdScript, id);
		mgdScript.unlock(id);
		return var;
	}



	public class ConstOnlyIdentifierTranslator implements IIdentifierTranslator {

		private final Set<BoogieConst> mNonTheoryConsts = new HashSet<>();

		public ConstOnlyIdentifierTranslator() {
		}

		@Override
		public Term getSmtIdentifier(final String id, final DeclarationInformation declInfo, final boolean isOldContext,
				final BoogieASTNode boogieASTNode) {
			if (declInfo.getStorageClass() != StorageClass.GLOBAL) {
				throw new AssertionError();
			}
			final BoogieConst bc = mBoogie2SmtSymbolTable.getBoogieConst(id);
			if (!bc.belongsToSmtTheory()) {
				mNonTheoryConsts.add(bc);
			}
			return bc.getDefaultConstant();
		}

		public Set<BoogieConst> getNonTheoryConsts() {
			return mNonTheoryConsts;
		}

	}
}
