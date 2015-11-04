package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.function.BiFunction;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.boogie.type.PreprocessorAnnotation;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.FixpointEngine;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ILoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.ITransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.AnnotatingRcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.BaseRcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.DummyReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgAbstractStateStorageProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgResultReporter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgVariableProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty.EmptyDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval.IntervalDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbstractInterpretationPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector.RCFGLoopDetector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * Should be used by other tools to run abstract interpretation on various parts
 * of the RCFG.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public final class AbstractInterpreter {

	/**
	 * Run abstract interpretation on the whole RCFG.
	 * 
	 * Suppress all exceptions except {@link OutOfMemoryError},
	 * {@link ToolchainCanceledException}, {@link IllegalArgumentException}.
	 * Produce no results.
	 */
	public static Map<CodeBlock, Map<ProgramPoint, Term>> runSilently(final RootNode root,
			final Collection<CodeBlock> initials, final IProgressAwareTimer timer,
			final IUltimateServiceProvider services) {
		final Logger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		final Map<CodeBlock, Map<ProgramPoint, Term>> rtr = new HashMap<CodeBlock, Map<ProgramPoint, Term>>();
		try {
			runInternal(root, initials, timer, services, (a, b) -> new DummyReporter<>(), rtr);
		} catch (OutOfMemoryError oom) {
			throw oom;
		} catch (IllegalArgumentException iae) {
			throw iae;
		} catch (ToolchainCanceledException tce) {
			// suppress timeouts
			return rtr;
		} catch (Throwable t) {
			logger.fatal("Suppressed exception in AIv2: " + t.getMessage());
			return Collections.emptyMap();
		}
		return rtr;
	}

	/**
	 * Run abstract interpretation on the whole RCFG.
	 * 
	 */
	public static Map<CodeBlock, Map<ProgramPoint, Term>> run(final RootNode root, final Collection<CodeBlock> initials,
			final IProgressAwareTimer timer, final IUltimateServiceProvider services) throws Throwable {
		final Map<CodeBlock, Map<ProgramPoint, Term>> rtr = new HashMap<CodeBlock, Map<ProgramPoint, Term>>();
		runInternal(root, initials, timer, services, (a, b) -> new RcfgResultReporter(a, b), rtr);
		return rtr;
	}

	private static void runInternal(final RootNode root, final Collection<CodeBlock> initials,
			final IProgressAwareTimer timer, final IUltimateServiceProvider services,
			BiFunction<IUltimateServiceProvider, BaseRcfgAbstractStateStorageProvider, IResultReporter<CodeBlock>> funCreateReporter,
			Map<CodeBlock, Map<ProgramPoint, Term>> predicates) throws Throwable {
		if (initials == null) {
			throw new IllegalArgumentException("No initial edges provided");
		}
		if (timer == null) {
			throw new IllegalArgumentException("timer is null");
		}

		final BoogieSymbolTable symbolTable = getSymbolTable(root);
		if (symbolTable == null) {
			throw new IllegalArgumentException("Could not get BoogieSymbolTable");
		}

		final RootAnnot rootAnnot = root.getRootAnnot();
		final Boogie2SMT bpl2smt = rootAnnot.getBoogie2SMT();
		final Script script = rootAnnot.getScript();
		final Boogie2SmtSymbolTable boogieVarTable = bpl2smt.getBoogie2SmtSymbolTable();

		final RCFGLoopDetector externalLoopDetector = new RCFGLoopDetector(services);
		externalLoopDetector.process(root);

		final IAbstractDomain<?, CodeBlock, BoogieVar> domain = selectDomain(symbolTable, services);
		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		final ITransitionProvider<CodeBlock> transitionProvider = new RcfgTransitionProvider();

		final IVariableProvider<CodeBlock, BoogieVar> varProvider = new RcfgVariableProvider(symbolTable,
				boogieVarTable);
		final ILoopDetector<CodeBlock> loopDetector = new RcfgLoopDetector(externalLoopDetector);

		final Collection<CodeBlock> filteredInitialElements = transitionProvider.filterInitialElements(initials);
		final boolean persist = ups.getBoolean(AbstractInterpretationPreferenceInitializer.LABEL_PERSIST_ABS_STATES);

		if (filteredInitialElements.isEmpty()) {
			final BaseRcfgAbstractStateStorageProvider storage = createStorage(services, domain, persist);
			final IResultReporter<CodeBlock> reporter = funCreateReporter.apply(services, storage);
			reporter.reportSafe("The program is empty");
			return;
		}

		for (CodeBlock initial : filteredInitialElements) {
			final BaseRcfgAbstractStateStorageProvider storage = createStorage(services, domain, persist);
			final IResultReporter<CodeBlock> reporter = funCreateReporter.apply(services, storage);
			final FixpointEngine<CodeBlock, BoogieVar, ProgramPoint> interpreter = new FixpointEngine<CodeBlock, BoogieVar, ProgramPoint>(
					services, timer, transitionProvider, storage, domain, varProvider, loopDetector, reporter);
			try {
				interpreter.run(initial);
			} catch (ToolchainCanceledException c) {
				predicates.put(initial, storage.getTerms(initial, script, bpl2smt));
				throw c;
			}
		}
	}

	private static BaseRcfgAbstractStateStorageProvider createStorage(final IUltimateServiceProvider services,
			final IAbstractDomain<?, CodeBlock, BoogieVar> domain, final boolean persist) {
		final BaseRcfgAbstractStateStorageProvider storage;
		if (persist) {
			storage = new AnnotatingRcfgAbstractStateStorageProvider(domain.getMergeOperator(), services);
		} else {
			storage = new RcfgAbstractStateStorageProvider(domain.getMergeOperator(), services);
		}
		return storage;
	}

	private static BoogieSymbolTable getSymbolTable(final RootNode root) {
		final PreprocessorAnnotation pa = PreprocessorAnnotation.getAnnotation(root);
		if (pa == null) {
			return null;
		}
		return pa.getSymbolTable();
	}

	private static IAbstractDomain<?, CodeBlock, BoogieVar> selectDomain(final BoogieSymbolTable symbolTable,
			final IUltimateServiceProvider services) {
		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		final String selectedDomain = ups.getString(AbstractInterpretationPreferenceInitializer.LABEL_ABSTRACT_DOMAIN);

		if (EmptyDomain.class.getSimpleName().equals(selectedDomain)) {
			return new EmptyDomain<>();
		} else if (SignDomain.class.getSimpleName().equals(selectedDomain)) {
			return new SignDomain(services);
		} else if (IntervalDomain.class.getSimpleName().equals(selectedDomain)) {
			return new IntervalDomain(services, symbolTable);
		}
		throw new UnsupportedOperationException("The value \"" + selectedDomain + "\" of preference \""
				+ AbstractInterpretationPreferenceInitializer.LABEL_ABSTRACT_DOMAIN + "\" was not considered before! ");
	}
}
