/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-srParse plug-in.
 *
 * The ULTIMATE Library-srParse plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-srParse plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-srParse plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-srParse plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-srParse plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.srparse;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.util.RcpUtils;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternScopeNotImplemented;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.ReflectionUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

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
	 *
	 * @param withoutNotImplemented
	 *            If true, do not generate patterns for which no countertrace is implemented (i.e., the ones that throw
	 *            {@link PatternScopeNotImplemented} when their {@link PatternType#transformToPea(ILogger, Map)} method
	 *            is called.
	 */
	public static Pair<List<? extends PatternType<?>>, Durations>
			createAllPatterns(final boolean withoutNotImplemented) {
		// first, create some observables and durartions
		final int count = 10;
		int duration = 5;
		int maxPatternObs = 2;
		final CDD[] patternObs = new CDD[count];
		final Rational[] durations = new Rational[count];

		final Durations duration2bounds = new Durations(PatternUtil::dummyConsumer);

		for (int i = 0; i < count; ++i) {
			patternObs[i] = BooleanDecision.create(CoreUtil.alphabeticalSequence(i + 15));
			durations[i] = Rational.valueOf(duration, 1);
			duration += 5;
		}

		// instantiate scopes
		final List<? extends SrParseScope<?>> scopes = ReflectionUtil
				.getClassesFromFolder(SrParseScope.class, RcpUtils.getBundleProtocolResolver()).stream()
				.filter(c -> !ReflectionUtil.isAbstractClass(c))
				.filter(c -> ReflectionUtil.isSubclassOfClass(c, SrParseScope.class))
				.map(a -> ReflectionUtil.instantiateClass(a, (Object[]) patternObs)).collect(Collectors.toList());
		Collections.sort(scopes, new ClassNameComparator());

		// instantiate patterns
		@SuppressWarnings("unchecked")
		final List<Class<? extends PatternType<?>>> patternTypeClazzes =
				ReflectionUtil.getClassesFromFolder(PatternType.class, RcpUtils.getBundleProtocolResolver()).stream()
						.filter(c -> !ReflectionUtil.isAbstractClass(c))
						.filter(c -> ReflectionUtil.isSubclassOfClass(c, PatternType.class))
						.filter(c -> !c.equals(DeclarationPattern.class)).map(a -> (Class<PatternType<?>>) a)
						.collect(Collectors.toList());
		Collections.sort(patternTypeClazzes, new ClassNameComparator());

		final List<PatternType<?>> patterns = new ArrayList<>();
		int id = 0;
		final ILogger dummyLogger = ILogger.getDummyLogger();
		for (final Class<? extends PatternType<?>> patternTypeClazz : patternTypeClazzes) {
			// all patterns except the initializationpattern have a constructor of the form
			// (final SrParseScope scope,
			// final String id, final List<CDD> cdds,
			// final List<String> durations)
			// we first instantiate the pattern type to see how many cdds and durations we
			// actually need, and then we
			// instantiate it again for real for every scope
			final PatternType<?> dummyInstance =
					ReflectionUtil.instantiateClass(patternTypeClazz, new SrParseScopeGlobally(), "",
							Collections.emptyList(), Collections.emptyList(), Collections.emptyList());
			final int cddCount = dummyInstance.getExpectedCddSize();
			final int durationCount = dummyInstance.getExpectedDurationSize();

			for (final SrParseScope<?> scope : scopes) {
				final List<CDD> currentCdds =
						Arrays.stream(patternObs).skip(maxPatternObs).limit(cddCount).collect(Collectors.toList());
				Collections.reverse(currentCdds);
				final List<Rational> currentDurations =
						Arrays.stream(durations).limit(durationCount).collect(Collectors.toList());
				final PatternType<?> pattern = ReflectionUtil.instantiateClass(patternTypeClazz, scope,
						"ID_" + String.valueOf(id), currentCdds, currentDurations, Collections.emptyList());

				if (withoutNotImplemented) {
					try {
						final ReqPeas pea = pattern.transformToPea(dummyLogger, duration2bounds);
						dummyLogger.info(pea);
					} catch (final PatternScopeNotImplemented ex) {
						continue;
					}
				}
				patterns.add(pattern);
				id++;
			}
		}

		return new Pair<>(patterns, duration2bounds);
	}

	private static void dummyConsumer(final String a) {
		// do nothing
	}

	private static final class ClassNameComparator implements Comparator<Object> {
		@Override
		public int compare(final Object o1, final Object o2) {
			return o1.getClass().toString().compareTo(o2.getClass().toString());
		}
	}
}
