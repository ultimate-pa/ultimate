package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctPreferences.WideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter.LiteralCollectorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class OctagonDomain implements IAbstractDomain<OctagonDomainState, CodeBlock, IBoogieVar> {

	private final BoogieSymbolTable mSymbolTable;
	private final Logger mLogger;
	private final LiteralCollectorFactory mLiteralCollectorFactory;

	public OctagonDomain(Logger logger, BoogieSymbolTable symbolTable, LiteralCollectorFactory literalCollectorFactory) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		mLiteralCollectorFactory = literalCollectorFactory;
	}

	@Override
	public OctagonDomainState createFreshState() {
		return OctagonDomainState.createFreshState();
	}

	@Override
	public IAbstractStateBinaryOperator<OctagonDomainState> getWideningOperator() {
		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		WideningOperator wOp = ups.getEnum(OctPreferences.WIDENING_OPERATOR, WideningOperator.class);
		switch (wOp) {
		case SIMPLE:
			return new OctSimpleWideningOperator();
		case EXPONENTIAL:
			String thresholdString = ups.getString(OctPreferences.EXP_WIDENING_THRESHOLD);
			BigDecimal threshold = null;
			try {
				threshold = new BigDecimal(thresholdString);
			} catch (NumberFormatException nfe) {
				throw new IllegalArgumentException("Setting \"threshold\" is not a valid number: " + thresholdString);
			} 
			return new OctExponentialWideningOperator(threshold);
		case LITERAL:
			return new OctLiteralWideningOperator(mLiteralCollectorFactory.create().getNumberLiterals());
		default:
			throw new IllegalArgumentException("Unknown value for setting \"widening operator\": " + wOp);
		}
	}

	@Override
	public IAbstractStateBinaryOperator<OctagonDomainState> getMergeOperator() {
		return new IAbstractStateBinaryOperator<OctagonDomainState>() {
			@Override
			public OctagonDomainState apply(OctagonDomainState first, OctagonDomainState second) {
				return first.join(second);
			}
		};
	}

	@Override
	public IAbstractPostOperator<OctagonDomainState, CodeBlock, IBoogieVar> getPostOperator() {
		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		return new OctPostOperator(mLogger, mSymbolTable,
				ups.getInt(AbsIntPrefInitializer.LABEL_STATES_UNTIL_MERGE),
				ups.getBoolean(OctPreferences.FALLBACK_ASSIGN_INTERVAL_PROJECTION));
	}
	
}