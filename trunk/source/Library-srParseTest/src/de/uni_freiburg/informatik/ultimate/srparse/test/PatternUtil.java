package de.uni_freiburg.informatik.ultimate.srparse.test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class PatternUtil {

	private PatternUtil() {
		// do not instantiate utility class
	}

	/**
	 * Create for all subclasses of {@link PatternType} and {@link SrParseScope} an instantiated requirements pattern
	 * that can be used to create a PEA.
	 */
	public static List<PatternType> createAllPatterns() {
		// first, create some observables and durartions
		final int count = 10;
		final int duration = 50;
		final CDD[] patternObs = new CDD[count];
		final String[] durations = new String[count];
		final Map<String, Integer> duration2bounds = new HashMap<>();

		for (int i = 0; i < count; ++i) {
			patternObs[i] = BooleanDecision.create(CoreUtil.alphabeticalSequence(i + 16));
			durations[i] = "c" + i;
			duration2bounds.put(durations[i], duration);
		}

		// instantiate scopes
		final List<? extends SrParseScope> scopes = ReflectionUtil.getClassesFromFolder(SrParseScope.class).stream()
				.filter(c -> !ReflectionUtil.isAbstractClass(c))
				.filter(c -> ReflectionUtil.isSubclassOfClass(c, SrParseScope.class))
				.map(a -> ReflectionUtil.instantiateClass(a, (Object[]) patternObs)).collect(Collectors.toList());
		Collections.sort(scopes, new ClassNameComparator());

		// instantiate patterns
		final List<Class<? extends PatternType>> patternTypeClazzes = ReflectionUtil
				.getClassesFromFolder(PatternType.class).stream().filter(c -> !ReflectionUtil.isAbstractClass(c))
				.filter(c -> ReflectionUtil.isSubclassOfClass(c, PatternType.class))
				.filter(c -> !c.equals(InitializationPattern.class)).collect(Collectors.toList());
		Collections.sort(patternTypeClazzes, new ClassNameComparator());

		final List<PatternType> rtr = new ArrayList<>();
		int id = 0;
		for (final Class<? extends PatternType> patternTypeClazz : patternTypeClazzes) {
			// all patterns except the initializationpattern have a constructor of the form (final SrParseScope scope,
			// final String id, final List<CDD> cdds,
			// final List<String> durations)
			// we first instantiate the pattern type to see how many cdds and durations we actually need, and then we
			// instantiate it again for real for every scope

			final PatternType dummyInstance = ReflectionUtil.instantiateClass(patternTypeClazz, null, null, null, null);
			final int cddCount = dummyInstance.getExpectedCddSize();
			final int durationCount = dummyInstance.getExpectedDurationSize();

			for (final SrParseScope scope : scopes) {
				final List<CDD> currentCdds =
						Arrays.stream(patternObs).skip(scope.getSize()).limit(cddCount).collect(Collectors.toList());
				final List<String> currentDurations =
						Arrays.stream(durations).limit(durationCount).collect(Collectors.toList());
				rtr.add(ReflectionUtil.instantiateClass(patternTypeClazz, scope, "ID_" + String.valueOf(id),
						currentCdds, currentDurations));
				id++;
			}
		}

		return rtr;
	}

	private static final class ClassNameComparator implements Comparator<Object> {
		@Override
		public int compare(final Object o1, final Object o2) {
			return o1.getClass().toString().compareTo(o2.getClass().toString());
		}
	}
}
