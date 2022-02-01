/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.initializer;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngineParameters;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IAbstractStateStorage;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.IcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array.ArrayDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array.ArrayDomainPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomainPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence.CongruenceDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.explicit.ExplicitValueDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain.LiteralCollectorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman.Boogie2SmtSymbolTableTmpVars;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.poorman.PoormanAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 * Sets-up the fixpoint engine for abstract interpretation.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class FixpointEngineParameterFactory {

	private final BoogieSymbolTable mSymbolTable;
	private final IIcfg<?> mRoot;
	private final BoogieIcfgContainer mBoogieIcfg;
	private final IUltimateServiceProvider mServices;
	private final LiteralCollectorFactory mLiteralCollector;
	private final IBoogieSymbolTableVariableProvider mVariableProvider;

	public FixpointEngineParameterFactory(final IIcfg<?> root, final LiteralCollectorFactory literalCollector,
			final IUltimateServiceProvider services) {
		mRoot = root;
		mBoogieIcfg = AbsIntUtil.getBoogieIcfgContainer(mRoot);
		mServices = services;

		final PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null || pa.getSymbolTable() == null) {
			throw new IllegalArgumentException("Could not get BoogieSymbolTable");
		}
		mSymbolTable = pa.getSymbolTable();
		mLiteralCollector = literalCollector;

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final boolean useFuture = prefs.getBoolean(AbsIntPrefInitializer.LABEL_USE_FUTURE_RCFG);
		final boolean poormanSelected = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN_FUTURE)
				.equals(PoormanAbstractDomain.class.getSimpleName());
		final boolean arraySelected =
				prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN).equals(ArrayDomain.class.getSimpleName());
		if (useFuture && poormanSelected || arraySelected) {
			mVariableProvider =
					new Boogie2SmtSymbolTableTmpVars(mBoogieIcfg.getBoogie2SMT().getBoogie2SmtSymbolTable());
		} else {
			mVariableProvider = mBoogieIcfg.getBoogie2SMT().getBoogie2SmtSymbolTable();
		}
	}

	@SuppressWarnings("unchecked")
	public <STATE extends IAbstractState<STATE>>
			FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, IcfgLocation>
			createParams(final IProgressAwareTimer timer,
					final ITransitionProvider<IcfgEdge, IcfgLocation> transitionProvider,
					final ILoopDetector<IcfgEdge> loopDetector) {
		final IAbstractDomain<STATE, IcfgEdge> domain = (IAbstractDomain<STATE, IcfgEdge>) selectDomain();
		final IAbstractStateStorage<STATE, IcfgEdge, IcfgLocation> storageProvider =
				new IcfgAbstractStateStorageProvider<>(mServices, transitionProvider);

		final IVariableProvider<STATE, IcfgEdge> variableProvider =
				new RcfgVariableProvider<>(mRoot.getCfgSmtToolkit(), mServices);
		final IDebugHelper<STATE, IcfgEdge, IProgramVarOrConst, IcfgLocation> debugHelper =
				new RcfgDebugHelper<>(mRoot.getCfgSmtToolkit(), mServices, mRoot.getCfgSmtToolkit().getSymbolTable());
		return new FixpointEngineParameters<STATE, IcfgEdge, IProgramVarOrConst, IcfgLocation>(mServices,
				IProgramVarOrConst.class).setDomain(domain).setLoopDetector(loopDetector).setStorage(storageProvider)
						.setTransitionProvider(transitionProvider).setVariableProvider(variableProvider)
						.setDebugHelper(debugHelper).setTimer(timer);
	}

	private IAbstractDomain<?, IcfgEdge> selectDomain() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String selectedDomain = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		final IAbstractDomain<?, IcfgEdge> domain = getFlatDomainOrNull(selectedDomain, logger);
		if (domain != null) {
			return domain;
		}

		if (ArrayDomain.class.getSimpleName().equals(selectedDomain)) {
			final String subDomainName = prefs.getString(ArrayDomainPreferences.LABEL_ABSTRACT_DOMAIN);
			final IAbstractDomain<?, IcfgEdge> subDomain;
			if (CompoundDomain.class.getSimpleName().equals(subDomainName)) {
				subDomain = createCompoundDomain(prefs, logger);
			} else {
				subDomain = getFlatDomainOrFail(subDomainName, logger);
			}
			return new ArrayDomain<>(subDomain, mBoogieIcfg, mServices, logger, mSymbolTable, mVariableProvider);
		} else if (CompoundDomain.class.getSimpleName().equals(selectedDomain)) {
			return createCompoundDomain(prefs, logger);
		}
		throw new UnsupportedOperationException(getFailureString(selectedDomain));
	}

	private IAbstractDomain<?, IcfgEdge> createCompoundDomain(final IPreferenceProvider prefs, final ILogger logger) {
		final List<String> domainNames = new ArrayList<>();
		if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_EMPTY_DOMAIN)) {
			domainNames.add(EmptyDomain.class.getSimpleName());
		}
		if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_SIGN_DOMAIN)) {
			domainNames.add(SignDomain.class.getSimpleName());
		}
		if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_CONGRUENCE_DOMAIN)) {
			domainNames.add(CongruenceDomain.class.getSimpleName());
		}
		if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_INTERVAL_DOMAIN)) {
			domainNames.add(IntervalDomain.class.getSimpleName());
		}
		if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_OCTAGON_DOMAIN)) {
			domainNames.add(OctagonDomain.class.getSimpleName());
		}
		if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_EXP_DOMAIN)) {
			domainNames.add(ExplicitValueDomain.class.getSimpleName());
		}
		return new CompoundDomain(mServices,
				domainNames.stream().map(a -> getFlatDomainOrFail(a, logger)).collect(Collectors.toList()),
				mBoogieIcfg);
	}

	private IAbstractDomain<?, IcfgEdge> getFlatDomainOrNull(final String domainName, final ILogger logger) {
		if (EmptyDomain.class.getSimpleName().equals(domainName)) {
			return new EmptyDomain<>();
		} else if (SignDomain.class.getSimpleName().equals(domainName)) {
			return new SignDomain(mServices, mBoogieIcfg, mSymbolTable, mVariableProvider);
		} else if (IntervalDomain.class.getSimpleName().equals(domainName)) {
			return new IntervalDomain(logger, mSymbolTable, mLiteralCollector.create().getLiteralCollection(),
					mServices, mBoogieIcfg, mVariableProvider);
		} else if (OctagonDomain.class.getSimpleName().equals(domainName)) {
			return new OctagonDomain(logger, mSymbolTable, mLiteralCollector, mServices, mBoogieIcfg,
					mVariableProvider);
		} else if (CongruenceDomain.class.getSimpleName().equals(domainName)) {
			return new CongruenceDomain(logger, mServices, mSymbolTable, mBoogieIcfg, mVariableProvider);
		} else if (ExplicitValueDomain.class.getSimpleName().equals(domainName)) {
			return new ExplicitValueDomain(logger, mSymbolTable, mLiteralCollector.create().getLiteralCollection(),
					mServices, mBoogieIcfg, mVariableProvider);
		}
		return null;
	}

	private IAbstractDomain<?, IcfgEdge> getFlatDomainOrFail(final String domainName, final ILogger logger) {
		final IAbstractDomain<?, IcfgEdge> rtr = getFlatDomainOrNull(domainName, logger);
		if (rtr == null) {
			throw new UnsupportedOperationException(getFailureString(domainName));
		}
		return rtr;
	}

	/**
	 * @return The symbol table's variable provider for usage in abstract domains.
	 */
	public IBoogieSymbolTableVariableProvider getSymbolTableVariableProvider() {
		return mVariableProvider;
	}

	private static String getFailureString(final String selectedDomain) {
		return "The value \"" + selectedDomain + "\" of preference \"" + AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN
				+ "\" was not considered before! ";
	}
}
