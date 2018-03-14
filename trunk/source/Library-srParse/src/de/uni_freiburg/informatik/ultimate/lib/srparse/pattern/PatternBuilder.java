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
package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class PatternBuilder {

	private static final Class<?>[] PATTERNS = new Class<?>[] { BndEntryConditionPattern.class,
			BndExistencePattern.class, BndInvariancePattern.class, BndPossResponsePattern.class,
			BndReccurrencePattern.class, BndResponsePattern.class, ConstrainedChainPattern.class, InstAbsPattern.class,
			InvariantPattern.class, MaxDurationPattern.class, MinDurationPattern.class, PossibilityPattern.class,
			PrecedenceChain12Pattern.class, PrecedenceChain21Pattern.class, PrecedencePattern.class,
			ResponseChain12Pattern.class, ResponseChain21Pattern.class, ResponsePattern.class,
			UniversalityPattern.class, };

	private static final Map<Class<? extends PatternType>, PatternTypeConstructor> CONSTRUCTORS = new HashMap<>();

	static {

		// construct an entry for the constructor map from all static methods with a name starting with "create",
		// assuming it exists and has the correct type

		// final MethodType constrType =
		// MethodType.methodType(void.class, SrParseScope.class, String.class, List.class, List.class);
		// final MethodHandles.Lookup lookup = MethodHandles.lookup();
		for (final Class<?> clazz : PATTERNS) {

			final PatternTypeConstructor ptc = (a, b, c, d) -> {
				try {
					return (PatternType) clazz.getConstructor(SrParseScope.class, String.class, List.class, List.class)
							.newInstance(a, b, c, d);
				} catch (final Throwable e) {
					e.printStackTrace();
					throw new RuntimeException(e);
				}
			};
			CONSTRUCTORS.put((Class<? extends PatternType>) clazz, ptc);

			//
			// try {
			// final MethodType funType =
			// MethodType.methodType(clazz, SrParseScope.class, String.class, List.class, List.class);
			// final MethodHandle handle = lookup.findConstructor(clazz, constrType);
			// final PatternTypeConstructor f =
			// (PatternTypeConstructor) LambdaMetafactory.metafactory(lookup, "construct",
			// MethodType.methodType(PatternTypeConstructor.class), funType.generic(), handle, funType)
			// .getTarget().invokeExact();
			//
			// CONSTRUCTORS.put((Class<? extends PatternType>) clazz, f);
			// } catch (final Throwable e) {
			// e.printStackTrace();
			// throw new RuntimeException(e);
			// }
		}

	}

	private final List<CDD> mCDDs;
	private final List<String> mDurations;
	private String mId;
	private Class<? extends PatternType> mClazz;
	private SrParseScope mScope;

	public PatternBuilder() {
		mCDDs = new ArrayList<>();
		mDurations = new ArrayList<>();
	}

	public PatternBuilder addCdd(final CDD... cdds) {
		add(mCDDs, cdds);
		return this;
	}

	public PatternBuilder addDuration(final String... durations) {
		add(mDurations, durations);
		return this;
	}

	public PatternBuilder setId(final String id) {
		mId = id;
		return this;
	}

	public PatternBuilder setType(final Class<? extends PatternType> clazz) {
		mClazz = clazz;
		return this;
	}

	public PatternBuilder setScope(final SrParseScope scope) {
		mScope = scope;
		return this;
	}

	@SafeVarargs
	private static <T> void add(final Collection<T> col, final T... elems) {
		if (elems == null || elems.length == 0) {
			return;
		}
		Arrays.stream(elems).forEachOrdered(col::add);
	}

	public PatternType build() {
		if (mClazz == null || mId == null || mScope == null) {
			throw new IllegalStateException("Type, Id or Scope of pattern not yet specified");
		}
		final PatternTypeConstructor constr = CONSTRUCTORS.get(mClazz);
		if (constr == null) {
			throw new UnsupportedOperationException("Unknown pattern type " + mClazz);
		}
		return constr.construct(mScope, mId, mCDDs, mDurations);
	}

	@FunctionalInterface
	private interface PatternTypeConstructor {
		PatternType construct(final SrParseScope scope, final String id, final List<CDD> cdds,
				final List<String> durations);
	}

}
