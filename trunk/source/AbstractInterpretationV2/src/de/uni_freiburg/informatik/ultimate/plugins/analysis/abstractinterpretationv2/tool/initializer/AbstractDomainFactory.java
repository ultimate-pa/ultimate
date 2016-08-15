package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.initializer;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.compound.CompoundDomainPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence.CongruenceDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.dataflow.DataflowDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon.OctagonDomain.LiteralCollectorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.PointerExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.RCFGArrayIndexCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class AbstractDomainFactory {

	private final BoogieSymbolTable mSymbolTable;
	private final RootNode mRoot;
	private final IUltimateServiceProvider mServices;
	private final LiteralCollectorFactory mLiteralCollector;

	public AbstractDomainFactory(final RootNode root, final LiteralCollectorFactory literalCollector,
			final IUltimateServiceProvider services) {
		mRoot = root;
		mServices = services;

		final PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null || pa.getSymbolTable() == null) {
			throw new IllegalArgumentException("Could not get BoogieSymbolTable");
		}
		mSymbolTable = pa.getSymbolTable();
		mLiteralCollector = literalCollector;

	}

	private IAbstractDomain<?, CodeBlock, IProgramVar> selectDomainFutureCfg() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String selectedDomain = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>();
		} else if (DataflowDomain.class.getSimpleName().equals(selectedDomain)) {
			return new DataflowDomain();
		}
		throw new UnsupportedOperationException(getFailureString(selectedDomain));
	}

	private IAbstractDomain<?, CodeBlock, IBoogieVar> selectDomain() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final String selectedDomain = prefs.getString(AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN);
		final ILogger logger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>();
		} else if (SignDomain.class.getSimpleName().equals(selectedDomain)) {
			return new SignDomain(mServices, mRoot.getRootAnnot(), mSymbolTable);
		} else if (IntervalDomain.class.getSimpleName().equals(selectedDomain)) {
			return new IntervalDomain(logger, mSymbolTable, mLiteralCollector.create().getLiteralCollection(),
					mServices, mRoot.getRootAnnot());
		} else if (OctagonDomain.class.getSimpleName().equals(selectedDomain)) {
			return new OctagonDomain(logger, mSymbolTable, mLiteralCollector, mServices, mRoot.getRootAnnot());
		} else if (VPDomain.class.getSimpleName().equals(selectedDomain)) {
			final RCFGArrayIndexCollector arrayIndexCollector = new RCFGArrayIndexCollector(mRoot);
			if (logger.isDebugEnabled()) {
				printVPDomainDebug(logger, arrayIndexCollector);
			}
			return new VPDomain(mServices, arrayIndexCollector.getPointerMap(),
					arrayIndexCollector.getIndexToArraysMap(), mRoot.getRootAnnot());
		} else if (CongruenceDomain.class.getSimpleName().equals(selectedDomain)) {
			return new CongruenceDomain(logger, mServices, mSymbolTable, mRoot.getRootAnnot());
		} else if (CompoundDomain.class.getSimpleName().equals(selectedDomain)) {
			@SuppressWarnings("rawtypes")
			final List<IAbstractDomain> domainList = new ArrayList<>();
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_EMPTY_DOMAIN)) {
				domainList.add(new EmptyDomain<>());
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_SIGN_DOMAIN)) {
				domainList.add(new SignDomain(mServices, mRoot.getRootAnnot(), mSymbolTable));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_CONGRUENCE_DOMAIN)) {
				domainList.add(new CongruenceDomain(logger, mServices, mSymbolTable, mRoot.getRootAnnot()));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_INTERVAL_DOMAIN)) {
				domainList.add(new IntervalDomain(logger, mSymbolTable,
						mLiteralCollector.create().getLiteralCollection(), mServices, mRoot.getRootAnnot()));
			}
			if (prefs.getBoolean(CompoundDomainPreferences.LABEL_USE_OCTAGON_DOMAIN)) {
				domainList.add(
						new OctagonDomain(logger, mSymbolTable, mLiteralCollector, mServices, mRoot.getRootAnnot()));
			}
			return new CompoundDomain(mServices, domainList, mRoot.getRootAnnot());
		}
		throw new UnsupportedOperationException(getFailureString(selectedDomain));
	}

	private String getFailureString(final String selectedDomain) {
		return "The value \"" + selectedDomain + "\" of preference \"" + AbsIntPrefInitializer.LABEL_ABSTRACT_DOMAIN
				+ "\" was not considered before! ";
	}

	private static void printVPDomainDebug(final ILogger logger, final RCFGArrayIndexCollector arrayIndexCollector) {
		for (final Entry<IProgramVar, Set<PointerExpression>> bv : arrayIndexCollector.getPointerMap().entrySet()) {
			logger.debug("PointerMap Key: " + bv.getKey());
			for (final PointerExpression val : bv.getValue()) {
				logger.debug("PointerMap Value: " + val.toString());
			}
		}
		logger.debug("============");
		for (final Entry<IProgramVar, Set<IProgramVar>> bv : arrayIndexCollector.getIndexToArraysMap().entrySet()) {
			logger.debug("IndexToArraysMap Key: " + bv.getKey());
			for (final IProgramVar val : bv.getValue()) {
				logger.debug("IndexToArraysMap Value: " + val);
			}
		}
	}
}
