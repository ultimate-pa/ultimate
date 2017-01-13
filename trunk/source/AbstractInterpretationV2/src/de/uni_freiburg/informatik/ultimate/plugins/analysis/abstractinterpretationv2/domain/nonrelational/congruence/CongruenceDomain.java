package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */

public class CongruenceDomain implements IAbstractDomain<CongruenceDomainState<IBoogieVar>, CodeBlock, IBoogieVar> {
	
	private final BoogieSymbolTable mSymbolTable;
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final BoogieIcfgContainer mRootAnnotation;

	private IAbstractStateBinaryOperator<CongruenceDomainState<IBoogieVar>> mWideningOperator;
	private IAbstractStateBinaryOperator<CongruenceDomainState<IBoogieVar>> mMergeOperator;
	private IAbstractPostOperator<CongruenceDomainState<IBoogieVar>, CodeBlock, IBoogieVar> mPostOperator;

	public CongruenceDomain(final ILogger logger, final IUltimateServiceProvider services,
			final BoogieSymbolTable symbolTable, final BoogieIcfgContainer rootAnnotation) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		mServices = services;
		mRootAnnotation = rootAnnotation;
	}

	@Override
	public CongruenceDomainState<IBoogieVar> createFreshState() {
		return new CongruenceDomainState<>(mLogger, IBoogieVar.class);
	}

	@Override
	public CongruenceDomainState<IBoogieVar> createTopState() {
		return new CongruenceDomainState<>(mLogger, false, IBoogieVar.class);
	}
	
	@Override
	public CongruenceDomainState<IBoogieVar> createBottomState() {
		return new CongruenceDomainState<>(mLogger, true, IBoogieVar.class);
	}

	@Override
	public IAbstractStateBinaryOperator<CongruenceDomainState<IBoogieVar>> getWideningOperator() {
		if (mWideningOperator == null) {
			// Widening is the same as merge, so we don't need an extra operator
			mWideningOperator = new CongruenceMergeOperator<>();
		}
		return mWideningOperator;
	}

	@Override
	public IAbstractStateBinaryOperator<CongruenceDomainState<IBoogieVar>> getMergeOperator() {
		if (mMergeOperator == null) {
			mMergeOperator = new CongruenceMergeOperator<>();
		}
		return mMergeOperator;
	}

	@Override
	public IAbstractPostOperator<CongruenceDomainState<IBoogieVar>, CodeBlock, IBoogieVar> getPostOperator() {
		if (mPostOperator == null) {
			final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
			final int maxParallelStates = prefs.getInt(AbsIntPrefInitializer.LABEL_MAX_PARALLEL_STATES);
			final CongruenceDomainStatementProcessor stmtProcessor = new CongruenceDomainStatementProcessor(mLogger,
					mSymbolTable, mRootAnnotation.getBoogie2SMT().getBoogie2SmtSymbolTable(), maxParallelStates);
			final Boogie2SmtSymbolTable bpl2SmtSymbolTable = mRootAnnotation.getBoogie2SMT().getBoogie2SmtSymbolTable();
			mPostOperator = new CongruencePostOperator(mLogger, mSymbolTable, stmtProcessor, bpl2SmtSymbolTable,
					maxParallelStates, mRootAnnotation.getBoogie2SMT(), mRootAnnotation);
		}
		return mPostOperator;
	}

	@Override
	public int getDomainPrecision() {
		return 300;
	}
}
