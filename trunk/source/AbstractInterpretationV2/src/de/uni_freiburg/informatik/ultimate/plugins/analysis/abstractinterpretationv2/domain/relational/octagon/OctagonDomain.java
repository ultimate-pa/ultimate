/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.Collection;
import java.util.function.Function;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RCFGLiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomainPreferences.LogMessageFormatting;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomainPreferences.WideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlockFactory;

/**
 * Octagon abstract domain, based on A. Miné's "The octagon abstract domain"
 * (https://www-apr.lip6.fr/~mine/publi/article-mine-ast01.pdf).
 *
 * Octagons are a weakly relational abstract domain and store constraints of the form "±x ± y ≤ c" for numerical (ints
 * and reals) variables x, y and a constant c. Boolean variables are stored separately, using the non-relation powerset
 * domain. Other types (bit-vectors for instance) are not supported.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class OctagonDomain implements IAbstractDomain<OctDomainState, IcfgEdge> {

	private final BoogieSymbolTable mSymbolTable;
	private final ILogger mLogger;
	private final LiteralCollectorFactory mLiteralCollectorFactory;
	private final Function<Boolean, OctDomainState> mOctDomainStateFactory;
	private final Supplier<IAbstractStateBinaryOperator<OctDomainState>> mWideningOperatorFactory;
	private final Supplier<IAbstractPostOperator<OctDomainState, IcfgEdge>> mPostOperatorFactory;
	private final BoogieIcfgContainer mBoogieIcfg;
	private final IBoogieSymbolTableVariableProvider mBoogie2SmtSymbolTableVariableProvider;

	public OctagonDomain(final ILogger logger, final BoogieSymbolTable symbolTable,
			final LiteralCollectorFactory literalCollectorFactory, final IUltimateServiceProvider services,
			final BoogieIcfgContainer icfg,
			final IBoogieSymbolTableVariableProvider boogie2SmtSymbolTableVariableProvider) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		mLiteralCollectorFactory = literalCollectorFactory;
		mBoogieIcfg = icfg;

		final IPreferenceProvider ups = services.getPreferenceProvider(Activator.PLUGIN_ID);
		mOctDomainStateFactory = makeDomainStateFactory(ups);
		mWideningOperatorFactory = makeWideningOperatorFactory(ups);
		final IAbstractPostOperator<IntervalDomainState, IcfgEdge> fallBackPostOperator =
				new IntervalDomain(logger, mSymbolTable, mLiteralCollectorFactory.create().getLiteralCollection(),
						services, mBoogieIcfg, boogie2SmtSymbolTableVariableProvider).getPostOperator();
		mPostOperatorFactory = makePostOperatorFactory(ups, fallBackPostOperator, mBoogieIcfg.getCodeBlockFactory());
		mBoogie2SmtSymbolTableVariableProvider = boogie2SmtSymbolTableVariableProvider;
	}

	/**
	 * Creates a factory for generating empty octagon abstract states (that is, states without any variables). The
	 * factory method caches and passes the abstract domain preferences to each new octagon to prevent the preferences
	 * to be read each time (which would be slow).
	 *
	 * @param ups
	 *            Preferences
	 * @return Factory for creating empty octagons
	 */
	private static Function<Boolean, OctDomainState> makeDomainStateFactory(final IPreferenceProvider ups) {
		final String settingLabel = OctagonDomainPreferences.LOG_STRING_FORMAT;
		final LogMessageFormatting settingValue = ups.getEnum(settingLabel, LogMessageFormatting.class);

		final Function<OctDomainState, String> logStringFunction;
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

		return (isBottom) -> OctDomainState.createFreshState(logStringFunction, isBottom);
	}

	/**
	 * Creates a factory for generating octagon widening operators. The factory method caches and passes the abstract
	 * domain settings to each new widening operator to prevent the preferences to be read each time (which would be
	 * slow).
	 *
	 * @param ups
	 *            Preferences
	 * @return Factory for creating widening operators
	 */
	private Supplier<IAbstractStateBinaryOperator<OctDomainState>>
			makeWideningOperatorFactory(final IPreferenceProvider ups) {
		final String settingLabel = OctagonDomainPreferences.WIDENING_OPERATOR;
		final WideningOperator settingValue = ups.getEnum(settingLabel, WideningOperator.class);

		switch (settingValue) {
		case SIMPLE:
			return () -> new OctSimpleWideningOperator();
		case EXPONENTIAL:
			final String thresholdString = ups.getString(OctagonDomainPreferences.EXP_WIDENING_THRESHOLD);
			try {
				final BigDecimal threshold = AbsIntUtil.sanitizeBigDecimalValue(thresholdString);
				return () -> new OctExponentialWideningOperator(threshold);
			} catch (final NumberFormatException nfe) {
				throw makeIllegalSettingException(settingLabel, settingValue);
			}
		case LITERAL:
			final Collection<BigDecimal> literals = mLiteralCollectorFactory.create().getNumberLiterals();
			return () -> new OctLiteralWideningOperator(literals);
		default:
			throw makeIllegalSettingException(OctagonDomainPreferences.WIDENING_OPERATOR, settingValue);
		}
	}

	/**
	 * Creates a factory for generating octagon post operators. The factory method caches and passes the abstract domain
	 * settings to each new post operator to prevent the preferences to be read each time (which would be slow).
	 *
	 * @param ups
	 *            Preferences
	 * @param fallBackPostOperator
	 *            The nonrelational post operator (preferably intervals) to fall back on if octagons can't compute
	 *            affine expressions.
	 * @param codeBlockFactory
	 *            The {@link CodeBlockFactory} for the current Boogie environment.
	 * @return Factory for creating widening operators
	 */
	private Supplier<IAbstractPostOperator<OctDomainState, IcfgEdge>> makePostOperatorFactory(
			final IPreferenceProvider ups,
			final IAbstractPostOperator<IntervalDomainState, IcfgEdge> fallBackPostOperator,
			final CodeBlockFactory codeBlockFactory) {
		final int maxParallelStates = ups.getInt(AbsIntPrefInitializer.LABEL_MAX_PARALLEL_STATES);
		final boolean fallbackAssignIntervalProjection =
				ups.getBoolean(OctagonDomainPreferences.FALLBACK_ASSIGN_INTERVAL_PROJECTION);
		return () -> new OctPostOperator(mLogger, mSymbolTable, mBoogieIcfg.getCfgSmtToolkit(), maxParallelStates,
				fallbackAssignIntervalProjection, mBoogie2SmtSymbolTableVariableProvider, fallBackPostOperator,
				codeBlockFactory);
	}

	/**
	 * Creates an exception for illegal settings.
	 *
	 * @param settingLabel
	 *            Label of the setting.
	 * @param settingValue
	 *            (Illegal) value of the setting.
	 * @return Excpetion to be thrown
	 */
	private static IllegalArgumentException makeIllegalSettingException(final String settingLabel,
			final Object settingValue) {
		final String msg = "Illegal value for setting \"" + settingLabel + "\": " + settingValue;
		return new IllegalArgumentException(msg);
	}

	@Override
	public OctDomainState createTopState() {
		return mOctDomainStateFactory.apply(false);
	}

	@Override
	public OctDomainState createBottomState() {
		return mOctDomainStateFactory.apply(true);
	}

	@Override
	public IAbstractStateBinaryOperator<OctDomainState> getWideningOperator() {
		return mWideningOperatorFactory.get();
	}

	@Override
	public IAbstractPostOperator<OctDomainState, IcfgEdge> getPostOperator() {
		return mPostOperatorFactory.get();
	}

	@FunctionalInterface
	public interface LiteralCollectorFactory {
		RCFGLiteralCollector create();
	}
}