package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator.EvalResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Expression2Term.IIdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.MappedTerm2Expression;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalTermUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman.Boogie2SmtSymbolTableTmpVars;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.BoogieVarFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.CallInfoCache;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.TemporaryBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence.Origin;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ArrayDomainToolkit<STATE extends IAbstractState<STATE>> {
	private static final String BOUND_NAME = "b";
	private static final String VALUE_NAME = "v";
	private static final String AUX_NAME = "aux";

	private final IAbstractDomain<STATE, IcfgEdge> mSubDomain;
	private final BoogieVarFactory mBoogieVarFactory;
	private final Boogie2SMT mBoogie2Smt;
	private final CodeBlockFactory mCodeBlockFactory;
	private final CallInfoCache mCallInfoCache;
	private final TemporaryBoogieVar mMinBound;
	private final TemporaryBoogieVar mMaxBound;
	private final Map<TermVariable, String> mAuxVarNameMap;
	private final MappedTerm2Expression mMappedTerm2Expression;
	private final Boogie2SmtSymbolTableTmpVars mVariableProvider;
	private final IUltimateServiceProvider mServices;
	private final Map<Term, EvalResult> mEvaluationCache;
	private final ILogger mLogger;

	public ArrayDomainToolkit(final IAbstractDomain<STATE, IcfgEdge> subDomain, final IIcfg<?> icfg,
			final IUltimateServiceProvider services, final BoogieSymbolTable boogieSymbolTable,
			final Boogie2SmtSymbolTableTmpVars variableProvider, final ILogger logger) {
		mSubDomain = subDomain;
		final BoogieIcfgContainer rootAnnotation = AbsIntUtil.getBoogieIcfgContainer(icfg);
		mBoogie2Smt = rootAnnotation.getBoogie2SMT();
		mCodeBlockFactory = rootAnnotation.getCodeBlockFactory();
		final Script script = mBoogie2Smt.getScript();
		final ManagedScript managedScript = mBoogie2Smt.getManagedScript();
		mBoogieVarFactory = new BoogieVarFactory(managedScript);
		mCallInfoCache = new CallInfoCache(icfg.getCfgSmtToolkit(), boogieSymbolTable);
		mMappedTerm2Expression = new MappedTerm2Expression(mBoogie2Smt.getTypeSortTranslator(),
				mBoogie2Smt.getBoogie2SmtSymbolTable(), managedScript);
		mVariableProvider = variableProvider;
		mAuxVarNameMap = new HashMap<>();
		mMinBound = createVariable("-inf", SmtSortUtils.getIntSort(script));
		mMaxBound = createVariable("inf", SmtSortUtils.getIntSort(script));
		mServices = services;
		mLogger = logger;
		mEvaluationCache = new HashMap<>();
	}

	private TemporaryBoogieVar createVariable(final String name, final Sort sort) {
		final TemporaryBoogieVar result = mBoogieVarFactory.createFreshBoogieVar(name, sort);
		mAuxVarNameMap.put(result.getTermVariable(), result.getGloballyUniqueId());
		mVariableProvider.addTemporaryVariable(result);
		return result;
	}

	public TemporaryBoogieVar createBoundVar(final Sort sort) {
		return createVariable(BOUND_NAME, sort);
	}

	public TemporaryBoogieVar createValueVar(final Sort sort) {
		return createVariable(VALUE_NAME, sort);
	}

	public TemporaryBoogieVar createAuxVar(final Sort sort) {
		return createVariable(AUX_NAME, sort);
	}

	public ManagedScript getManagedScript() {
		return mBoogie2Smt.getManagedScript();
	}

	public Script getScript() {
		return mBoogie2Smt.getScript();
	}

	public CallInfoCache getCallInfoCache() {
		return mCallInfoCache;
	}

	public TemporaryBoogieVar getMinBound() {
		return mMinBound;
	}

	public TemporaryBoogieVar getMaxBound() {
		return mMaxBound;
	}

	public IAbstractStateBinaryOperator<STATE> getWideningOperator() {
		return mSubDomain.getWideningOperator();
	}

	public IUltimateServiceProvider getServices() {
		return mServices;
	}

	public STATE handleAssumptionBySubdomain(final STATE currentState, final Term assumption) {
		STATE last = null;
		STATE result = currentState;
		final Statement assume = new AssumeStatement(null, getExpression(assumption));
		// Workaround: Apply post-operator until there's no change
		while (last == null || !last.isEqualTo(result)) {
			last = result;
			result = handleStatementBySubdomain(result, assume);
		}
		return result;
	}

	public STATE handleStatementBySubdomain(final STATE currentState, final Statement statement) {
		if (currentState.isBottom()) {
			return currentState;
		}
		final CodeBlock codeBlock =
				mCodeBlockFactory.constructStatementSequence(null, null, statement, Origin.IMPLEMENTATION);
		final Collection<STATE> newStates = mSubDomain.getPostOperator().apply(currentState, codeBlock);
		if (newStates.isEmpty()) {
			return mSubDomain.createBottomState();
		}
		return DisjunctiveAbstractState.union(newStates);
	}

	public EvalResult evaluate(final STATE state, final Term formula, final boolean useCache) {
		if (!useCache) {
			return mSubDomain.getPostOperator().evaluate(state, formula, getScript());
		}
		EvalResult result = mEvaluationCache.get(formula);
		if (result == null) {
			result = mSubDomain.getPostOperator().evaluate(state, formula, getScript());
			mEvaluationCache.put(formula, result);
		}
		return result;
	}

	public Expression getExpression(final Term term) {
		return mMappedTerm2Expression.translate(term, Collections.emptySet(), mAuxVarNameMap);
	}

	public Term getTerm(final Expression expression) {
		return mBoogie2Smt.getExpression2Term()
				.translateToTerm(new IIdentifierTranslator[] { new IdentifierTranslator() }, expression).getTerm();
	}

	private IProgramVarOrConst getBoogieVar(final String id, final DeclarationInformation declInfo,
			final boolean isOldContext) {
		final IProgramVarOrConst returnVar = mVariableProvider.getBoogieVar(id, declInfo, isOldContext);
		if (returnVar != null) {
			return returnVar;
		}
		return mVariableProvider.getBoogieConst(id);
	}

	public IProgramVarOrConst getBoogieVar(final IdentifierExpression expr) {
		return getBoogieVar(expr.getIdentifier(), expr.getDeclarationInformation(), false);
	}

	public IProgramVar getBoogieVar(final VariableLHS variable) {
		IProgramVar rtr =
				mVariableProvider.getBoogieVar(variable.getIdentifier(), variable.getDeclarationInformation(), false);
		if (rtr == null) {
			// hack for oldvars
			final String newIdent = variable.getIdentifier().replaceAll("old\\((.*)\\)", "$1");
			rtr = mVariableProvider.getBoogieVar(newIdent, variable.getDeclarationInformation(), false);
			rtr = ((BoogieNonOldVar) rtr).getOldVar();
		}
		assert rtr != null : "Could not find boogie var";
		return rtr;
	}

	public Pair<IProgramVar, Segmentation> createTopSegmentation(final Sort arraySort) {
		final IProgramVar newValue = createValueVar(TypeUtils.getValueSort(arraySort));
		final Segmentation segmentation =
				new Segmentation(Arrays.asList(mMinBound, mMaxBound), Arrays.asList(newValue));
		return new Pair<>(newValue, segmentation);
	}

	private class IdentifierTranslator implements IIdentifierTranslator {
		@Override
		public Term getSmtIdentifier(final String id, final DeclarationInformation declInfo, final boolean isOldContext,
				final BoogieASTNode boogieASTNode) {
			return getBoogieVar(id, declInfo, isOldContext).getTerm();
		}
	}

	public Term connstructEquivalentConstraint(final IProgramVarOrConst newVariable, final IProgramVar oldVariable,
			final Term baseTerm) {
		final Term newTerm = NonrelationalTermUtils.getTermVar(newVariable);
		final TermVariable oldTerm = oldVariable.getTermVariable();
		final Term constraint = SmtUtils.filterFormula(baseTerm, Collections.singleton(oldTerm), getScript());
		return new Substitution(getScript(), Collections.singletonMap(oldTerm, newTerm)).transform(constraint);
	}

	public ArrayDomainState<STATE> createBottomState() {
		final STATE substate = mSubDomain.createBottomState();
		return new ArrayDomainState<>(substate, substate.getVariables(), this);
	}

	public ArrayDomainState<STATE> createTopState() {
		final STATE substate = mSubDomain.createTopState();
		return new ArrayDomainState<>(substate, substate.getVariables(), this);
	}

	public Term eliminateQuantifier(final Term term) {
		return PartialQuantifierElimination.tryToEliminate(mServices, mLogger, getManagedScript(), term,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
	}
}
