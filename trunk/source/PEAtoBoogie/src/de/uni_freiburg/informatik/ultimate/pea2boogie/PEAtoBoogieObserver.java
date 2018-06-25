package de.uni_freiburg.informatik.ultimate.pea2boogie;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.preferences.Pea2BoogiePreferences;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.Req2BoogieTranslator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class PEAtoBoogieObserver implements IUnmanagedObserver {
	
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private IElement mBoogieAST;
	private PeaResultUtil mReporter;
	private IToolchainStorage mStorage;
	
	public PEAtoBoogieObserver(final ILogger logger, final IUltimateServiceProvider services, final IToolchainStorage storage) {
		mLogger = logger;
		mServices = services;
		mStorage = storage;
	}

	@Override
	public void init(ModelType modelType, int currentModelIndex, int numberOfModels) throws Throwable {
		// TODO Auto-generated method stub
	}

	@Override
	public void finish() throws Throwable {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (!(root instanceof ObjectContainer)) {
			throw new Exception("Expected ObjectContainer as input Model.");
		}
		final List<PatternType> rawPatterns = (List<PatternType>) ((ObjectContainer) root).getValue();
		
		logPatternSize(rawPatterns, "in total");
		final List<PatternType> unifiedPatterns = unify(rawPatterns);
		logPatternSize(unifiedPatterns, "after unification");

		if (!mServices.getProgressMonitorService().continueProcessing()) {
			return false;
		}

		mReporter = new PeaResultUtil(mLogger, mServices);
		// register CEX transformer that removes program executions from CEX.
		final Function<IResult, IResult> resultTransformer = mReporter::convertTraceAbstractionResult;
		mServices.getResultService().registerTransformer("CexReducer", resultTransformer);

		mBoogieAST = generateBoogie(unifiedPatterns);
		
		return false;
	}
	
	public IElement getResult() {
		return mBoogieAST;
	}
	
	private void logPatternSize(final List<PatternType> patterns, final String suffix) {
		final long patternWithId = patterns.stream().filter(a -> !(a instanceof InitializationPattern)).count();
		if (suffix == null) {
			mLogger.info(String.format("%s requirements (%s non-initialization)", patterns.size(), patternWithId));
		} else {
			mLogger.info(String.format("%s requirements (%s non-initialization) %s", patterns.size(), patternWithId,
					suffix));
		}
	}
	
	private List<PatternType> unify(final List<PatternType> patterns) {
		final List<PatternType> rtr = new ArrayList<>();
		final List<InitializationPattern> init = patterns.stream().filter(a -> a instanceof InitializationPattern)
				.map(a -> (InitializationPattern) a).collect(Collectors.toList());
		final UnionFind<InitializationPattern> uf = createUnionFind(init);
		checkTypeConflicts(uf.getAllRepresentatives());
		rtr.addAll(merge(uf));

		final List<PatternType> reqs =
				patterns.stream().filter(a -> !(a instanceof InitializationPattern)).collect(Collectors.toList());
		if (reqs.isEmpty()) {
			return rtr;
		}
		final UnionFind<PatternType> ufreq = createUnionFind(reqs);
		rtr.addAll(merge(ufreq));

		return rtr;
	}

	private <T extends PatternType> UnionFind<T> createUnionFind(final List<T> patterns) {
		final UnionFind<T> uf = new UnionFind<>();
		for (final T pattern : patterns) {
			final T rep = uf.findAndConstructEquivalenceClassIfNeeded(pattern);
			if (rep != pattern) {
				mReporter.mergedRequirements(pattern, rep);
			}
		}
		return uf;
	}

	private List<PatternType> merge(final UnionFind<? extends PatternType> ufreq) {
		final List<PatternType> rtr = new ArrayList<>();
		for (final Set<? extends PatternType> eqclass : ufreq.getAllEquivalenceClasses()) {
			if (eqclass.size() == 1) {
				rtr.addAll(eqclass);
				continue;
			}
			mReporter.mergedRequirements(eqclass);
			rtr.add(merge(eqclass));
		}
		return rtr;
	}

	/**
	 * Create a new pattern from a set of patterns by concatenating their ids.
	 */
	private static PatternType merge(final Set<? extends PatternType> eqclass) {
		assert eqclass != null && eqclass.size() > 1;
		final StringBuilder newName = new StringBuilder();
		final Iterator<? extends PatternType> iter = eqclass.iterator();

		PatternType current = iter.next();
		final Class<?> last = current.getClass();
		newName.append(current.getId());
		while (iter.hasNext()) {
			current = iter.next();
			if (last != current.getClass()) {
				throw new AssertionError("Patterns with different types are assumed to be equivalent");
			}
			newName.append('_').append(current.getId());
		}
		return current.rename(newName.toString());
	}

	private void checkTypeConflicts(final Collection<InitializationPattern> inits) {
		final Map<String, InitializationPattern> seen = new HashMap<>();
		for (final InitializationPattern init : inits) {
			final InitializationPattern otherInit = seen.put(init.getId(), init);
			if (otherInit == null) {
				continue;
			}
			if (!Objects.equals(init.getType(), otherInit.getType())) {
				mReporter.unsupportedSyntaxError(new DummyLocation(),
						String.format("The initialization patterns %s and %s have conflicting types: %s vs. %s",
								init.getId(), otherInit.getId(), init.getType(), otherInit.getType()));
			}
		}
	}

	private IElement generateBoogie(final List<PatternType> patterns) {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final int length = patterns.size();
		final boolean vacuityCheck = prefs.getBoolean(Pea2BoogiePreferences.LABEL_CHECK_VACUITY);

		final int combinationNum;
		if (prefs.getBoolean(Pea2BoogiePreferences.LABEL_CHECK_RT_INCONSISTENCY)) {
			combinationNum = Math.min(length, prefs.getInt(Pea2BoogiePreferences.LABEL_RT_INCONSISTENCY_RANGE));
		} else {
			combinationNum = -1;
		}
		final boolean checkConsistency = prefs.getBoolean(Pea2BoogiePreferences.LABEL_CHECK_CONSISTENCY);
		final boolean reportTrivialRtConsistency =
				prefs.getBoolean(Pea2BoogiePreferences.LABEL_REPORT_TRIVIAL_RT_CONSISTENCY);

		final Unit unit = new Req2BoogieTranslator(mServices, mStorage, mLogger, vacuityCheck, combinationNum,
				checkConsistency, reportTrivialRtConsistency, patterns).getUnit();
		new PatternContainer(patterns).annotate(unit);
		return unit;
	}
	
	private static final class DummyLocation extends DefaultLocation {

		private static final long serialVersionUID = 1L;

		public DummyLocation() {
			super("", -1, 0, 0, 0);
		}
	}

}
