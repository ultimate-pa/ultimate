package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
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

	private IAbstractStateBinaryOperator<CongruenceDomainState> mWideningOperator;
	private IAbstractPostOperator<CongruenceDomainState, IcfgEdge> mPostOperator;
	private final CfgSmtToolkit mCfgSmtToolkit;

	public CongruenceDomain(final ILogger logger, final IUltimateServiceProvider services,
			final BoogieSymbolTable symbolTable, final IIcfg<?> icfg) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		mServices = services;
		mCfgSmtToolkit = icfg.getCfgSmtToolkit();
		mRootAnnotation = AbsIntUtil.getBoogieIcfgContainer(icfg);
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
		if (mWideningOperator == null) {
			// Widening is the same as merge, so we don't need an extra operator
			mWideningOperator = new CongruenceMergeOperator<>();
		}
		return mWideningOperator;
	}

	@Override
	public IAbstractPostOperator<CongruenceDomainState, IcfgEdge> getPostOperator() {
		if (mPostOperator == null) {
			final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
			final int maxParallelStates = prefs.getInt(AbsIntPrefInitializer.LABEL_MAX_PARALLEL_STATES);
			final Boogie2SMT boogie2smt = mRootAnnotation.getBoogie2SMT();
			final IBoogieSymbolTableVariableProvider bpl2SmtSymbolTable = boogie2smt.getBoogie2SmtSymbolTable();
			final CongruenceDomainStatementProcessor stmtProcessor = new CongruenceDomainStatementProcessor(mLogger,
					mSymbolTable, bpl2SmtSymbolTable, maxParallelStates);
			mPostOperator = new CongruencePostOperator(mLogger, mSymbolTable, stmtProcessor, bpl2SmtSymbolTable,
					maxParallelStates, boogie2smt, mCfgSmtToolkit);
		}
		return mPostOperator;
	}
}
