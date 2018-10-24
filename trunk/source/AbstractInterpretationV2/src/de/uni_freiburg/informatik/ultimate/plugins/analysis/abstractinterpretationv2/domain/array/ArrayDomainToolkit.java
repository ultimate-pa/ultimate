package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.IIdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.MappedTerm2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TypeSortTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalTermUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman.Boogie2SmtSymbolTableTmpVars;
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

	private final IAbstractDomain<STATE, IcfgEdge> mSubDomain;
	private final BoogieVarFactory mBoogieVarFactory;
	private final Boogie2SMT mBoogie2Smt;
	private final CodeBlockFactory mCodeBlockFactory;
	private final CallInfoCache mCallInfoCache;
	private final TemporaryBoogieVar mMinBound;
	private final TemporaryBoogieVar mMaxBound;
	private final TypeSortTranslator mTypeSortTranslator;
	private final Set<TemporaryBoogieVar> mCreatedVars;
	private final MappedTerm2Expression mMappedTerm2Expression;
	private final Boogie2SmtSymbolTableTmpVars mVariableProvider;
	private final IUltimateServiceProvider mServices;

	public ArrayDomainToolkit(final IAbstractDomain<STATE, IcfgEdge> subDomain, final IIcfg<?> icfg,
			final IUltimateServiceProvider services, final BoogieSymbolTable boogieSymbolTable,
			final Boogie2SmtSymbolTableTmpVars variableProvider) {
		mSubDomain = subDomain;
		final BoogieIcfgContainer rootAnnotation = AbsIntUtil.getBoogieIcfgContainer(icfg);
		mBoogie2Smt = rootAnnotation.getBoogie2SMT();
		mCodeBlockFactory = rootAnnotation.getCodeBlockFactory();
		final Script script = mBoogie2Smt.getScript();
		final ManagedScript managedScript = mBoogie2Smt.getManagedScript();
		mBoogieVarFactory = new BoogieVarFactory(managedScript);
		mCallInfoCache = new CallInfoCache(icfg.getCfgSmtToolkit(), boogieSymbolTable);
		mTypeSortTranslator = new TypeSortTranslator(script, services);
		mMappedTerm2Expression = new MappedTerm2Expression(mBoogie2Smt.getTypeSortTranslator(),
				mBoogie2Smt.getBoogie2SmtSymbolTable(), managedScript);
		mVariableProvider = variableProvider;
		mCreatedVars = new HashSet<>();
		mMinBound = createVariable("-inf", BoogieType.TYPE_INT);
		mMaxBound = createVariable("inf", BoogieType.TYPE_INT);
		mServices = services;
	}

	public TemporaryBoogieVar createVariable(final String name, final IBoogieType type) {
		final TemporaryBoogieVar result = mBoogieVarFactory.createFreshBoogieVar(name, type);
		mCreatedVars.add(result);
		mVariableProvider.addTemporaryVariable(result);
		return result;
	}

	public TemporaryBoogieVar createBoundVar(final IBoogieType type) {
		return createVariable(BOUND_NAME, type);
	}

	public TemporaryBoogieVar createValueVar(final IBoogieType type) {
		return createVariable(VALUE_NAME, type);
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

	public Expression getExpression(final Term term) {
		final Map<TermVariable, String> namesMap =
				mCreatedVars.stream().filter(TemporaryBoogieVar::hasTermVariable).collect(
						Collectors.toMap(TemporaryBoogieVar::getTermVariable, TemporaryBoogieVar::getGloballyUniqueId));
		return mMappedTerm2Expression.translate(term, Collections.emptySet(), namesMap);
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

	public IBoogieType getType(final Sort sort) {
		return mTypeSortTranslator.getType(sort);
	}

	public Pair<IProgramVar, Segmentation> createTopSegmentation(final IBoogieType type) {
		final IProgramVar newValue = createValueVar(type);
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
}
