package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.Collection;
import java.util.function.Function;
import java.util.function.Supplier;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctPreferences.LogMessageFormatting;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctPreferences.WideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter.LiteralCollectorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class OctagonDomain implements IAbstractDomain<OctDomainState, CodeBlock, IBoogieVar> {

	private BoogieSymbolTable mSymbolTable;
	private Logger mLogger;
	private LiteralCollectorFactory mLiteralCollectorFactory;
	private Supplier<OctDomainState> mOctDomainStateFactory; 
	private Supplier<IAbstractStateBinaryOperator<OctDomainState>> mWideningOperatorFactory; 
	private Supplier<IAbstractPostOperator<OctDomainState, CodeBlock, IBoogieVar>> mPostOperatorFactory; 
	
	public OctagonDomain(Logger logger, BoogieSymbolTable symbolTable, LiteralCollectorFactory literalCollectorFactory) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		mLiteralCollectorFactory = literalCollectorFactory;

		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		mOctDomainStateFactory = makeDomainStateFactory(ups);
		mWideningOperatorFactory = makeWideningOperatorFactory(ups);
		mPostOperatorFactory = makePostOperatorFactory(ups);
	}

	private Supplier<OctDomainState> makeDomainStateFactory(UltimatePreferenceStore ups) {

		String settingLabel = OctPreferences.LOG_STRING_FORMAT;
		LogMessageFormatting settingValue = ups.getEnum(settingLabel, LogMessageFormatting.class);

		Function<OctDomainState, String> logStringFunction;
		switch (settingValue) {
		case FULL_MATRIX:
			logStringFunction = OctDomainState::logStringFullMatrix;
			break;
		case HALF_MATRIX:
			logStringFunction = OctDomainState::logStringHalfMatrix;
			break;
		case TERM:
			logStringFunction = OctDomainState::logStringTerm;
			break;
		default:
			throw makeIllegalSettingException(settingLabel, settingValue);
		}
		
		return () -> OctDomainState.createFreshState(logStringFunction);
	}

	private Supplier<IAbstractStateBinaryOperator<OctDomainState>> makeWideningOperatorFactory(
			UltimatePreferenceStore ups) {

		String settingLabel = OctPreferences.WIDENING_OPERATOR;
		WideningOperator settingValue = ups.getEnum(settingLabel, WideningOperator.class);

		switch (settingValue) {
		case SIMPLE:
			return () -> new OctSimpleWideningOperator();
		case EXPONENTIAL:
			String thresholdString = ups.getString(OctPreferences.EXP_WIDENING_THRESHOLD);
			try {
				BigDecimal threshold = new BigDecimal(thresholdString);
				return () -> new OctExponentialWideningOperator(threshold);
			} catch (NumberFormatException nfe) {
				throw makeIllegalSettingException(settingLabel, settingValue);
			} 
		case LITERAL:
			Collection<BigDecimal> literals = mLiteralCollectorFactory.create().getNumberLiterals();
			return () -> new OctLiteralWideningOperator(literals);
		default:
			throw makeIllegalSettingException(OctPreferences.WIDENING_OPERATOR, settingValue);
		}
	}
	
	private Supplier<IAbstractPostOperator<OctDomainState, CodeBlock, IBoogieVar>> makePostOperatorFactory(
			UltimatePreferenceStore ups) {

		int maxParallelStates = ups.getInt(AbsIntPrefInitializer.LABEL_MAX_PARALLEL_STATES);
		boolean fallbackAssignIntervalProjection = ups.getBoolean(OctPreferences.FALLBACK_ASSIGN_INTERVAL_PROJECTION);
		return () -> new OctPostOperator(mLogger, mSymbolTable, maxParallelStates, fallbackAssignIntervalProjection);
	}
	
	private IllegalArgumentException makeIllegalSettingException(String settingLabel, Object settingValue) {
		String msg = "Illegal value for setting \"" + settingLabel + "\": " + settingValue;
		return new IllegalArgumentException(msg);
	}

	@Override
	public OctDomainState createFreshState() {
		return mOctDomainStateFactory.get();
	}

	@Override
	public IAbstractStateBinaryOperator<OctDomainState> getWideningOperator() {
		return mWideningOperatorFactory.get();
	}

	@Override
	public IAbstractStateBinaryOperator<OctDomainState> getMergeOperator() {
		return new IAbstractStateBinaryOperator<OctDomainState>() {
			@Override
			public OctDomainState apply(OctDomainState first, OctDomainState second) {
				return first.join(second);
			}
		};
	}

	@Override
	public IAbstractPostOperator<OctDomainState, CodeBlock, IBoogieVar> getPostOperator() {
		return mPostOperatorFactory.get();
	}

	@Override
	public int getDomainPrecision() {
		return 2000;
	}
	
}