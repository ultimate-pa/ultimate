package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbsIntBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */

public class CongruenceDomain implements IAbstractDomain<CongruenceDomainState, IcfgEdge> {

	private final BoogieSymbolTable mSymbolTable;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final BoogieIcfgContainer mRootAnnotation;

	private NonrelationalPostOperator<CongruenceDomainState, CongruenceDomainValue> mPostOperator;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final IBoogieSymbolTableVariableProvider mBpl2SmtSymbolTable;

	public CongruenceDomain(final ILogger logger, final IUltimateServiceProvider services,
			final BoogieSymbolTable symbolTable, final BoogieIcfgContainer icfg,
			final IBoogieSymbolTableVariableProvider variableProvider) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		mServices = services;
		mCfgSmtToolkit = icfg.getCfgSmtToolkit();
		mRootAnnotation = icfg;
		mBpl2SmtSymbolTable = variableProvider;
	}

	@Override
	public CongruenceDomainState createTopState() {
		return new CongruenceDomainState(mLogger, false);
	}

	@Override
	public CongruenceDomainState createBottomState() {
		return new CongruenceDomainState(mLogger, true);
	}

	@Override
	public IAbstractStateBinaryOperator<CongruenceDomainState> getWideningOperator() {
		return (a, b) -> a.union(b);
	}

	@Override
	public NonrelationalPostOperator<CongruenceDomainState, CongruenceDomainValue> getPostOperator() {
		if (mPostOperator == null) {
			final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
			final int maxParallelStates = prefs.getInt(AbsIntPrefInitializer.LABEL_MAX_PARALLEL_STATES);
			final int maxRecursionDepth = prefs.getInt(AbsIntPrefInitializer.LABEL_MAX_EVALUATION_RECURSION_DETPH);
			final Boogie2SMT boogie2smt = mRootAnnotation.getBoogie2SMT();
			final CongruenceDomainEvaluator evaluator = new CongruenceDomainEvaluator(mLogger, mSymbolTable,
					mBpl2SmtSymbolTable, maxParallelStates, maxRecursionDepth);
			mPostOperator = new CongruencePostOperator(mLogger, mSymbolTable, mBpl2SmtSymbolTable, maxParallelStates,
					boogie2smt, mCfgSmtToolkit, evaluator);
		}
		return mPostOperator;
	}

	@Override
	public void beforeFixpointComputation(final Object... objects) {
		for (final Object o : objects) {
			if (o instanceof AbsIntBenchmark) {
				@SuppressWarnings("unchecked")
				final AbsIntBenchmark<IcfgEdge> absIntBenchmark = (AbsIntBenchmark<IcfgEdge>) o;
				getPostOperator().setAbsIntBenchmark(absIntBenchmark);
			}
		}
	}
}
