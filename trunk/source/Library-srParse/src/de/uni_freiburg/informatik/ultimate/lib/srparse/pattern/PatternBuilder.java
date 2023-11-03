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
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.SrParseScope;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * {@link PatternBuilder} allows us to keep the state of the single patterns mostly immutable and the parser flexible.
 * You can collect the parts of a pattern in multiple steps and when you have them all you build the pattern with
 * {@link PatternBuilder#build()}.
 *
 * To avoid many methods that all call the same constructor, we build them using reflection (this might be too
 * expensive, keep an eye out for it).
 *
 * You need to update the PATTERNS list manually when you add new patterns. Just use
 * <code>ls | sed 's/\.java/\.class,/g' </code> in this package.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
@SuppressWarnings("unchecked")
public class PatternBuilder {

	private static final Class<?>[] PATTERNS = new Class<?>[] { ResponseDelayBoundL2Pattern.class,
			ResponseDelayBoundL1Pattern.class, EdgeResponseBoundL2Pattern.class, EdgeResponseDelayBoundL2Pattern.class,
			EdgeResponseBoundU1Pattern.class, BndEntryConditionPattern.class, ExistenceBoundUPattern.class,
			InvarianceBoundL2Pattern.class, ReccurrenceBoundLPattern.class, ResponseBoundL12Pattern.class,
			ResponseBoundL1Pattern.class, ResponseDelayPattern.class, TriggerResponseBoundL1Pattern.class,
			TriggerResponseDelayBoundL1Pattern.class, ConstrainedChainPattern.class, EdgeResponseDelayPattern.class,
			DeclarationPattern.class, AbsencePattern.class, InitializationPattern.class, InvariancePattern.class,
			DurationBoundUPattern.class, DurationBoundLPattern.class, PersistencePattern.class,
			PrecedenceChain12Pattern.class, PrecedenceChain21Pattern.class, PrecedencePattern.class,
			ResponseChain12Pattern.class, ResponsePattern.class, UniversalityPattern.class,
			UniversalityDelayPattern.class };

	private static final Map<Class<? extends PatternType<?>>, PatternTypeConstructor> CONSTRUCTORS = new HashMap<>();

	static {
		// TODO: Check if this can be made faster using LambdaMetafactory

		for (final Class<?> clazz : PATTERNS) {

			final PatternTypeConstructor ptc = (a, b, c, d, e) -> {
				try {
					return (PatternType<?>) clazz
							.getConstructor(SrParseScope.class, String.class, List.class, List.class, List.class)
							.newInstance(a, b, c, d, e);
				} catch (final Throwable ex) {
					ex.printStackTrace();
					throw new RuntimeException(ex);
				}
			};
			CONSTRUCTORS.put((Class<? extends PatternType<?>>) clazz, ptc);
		}

	}

	private final List<CDD> mCDDs;
	private final List<Rational> mDurations;
	private final List<String> mDurationNames;
	private String mId;
	private Class<? extends PatternType<?>> mClazz;
	private SrParseScope<?> mScope;

	public PatternBuilder() {
		mCDDs = new ArrayList<>();
		mDurations = new ArrayList<>();
		mDurationNames = new ArrayList<>();
	}

	public PatternBuilder addCdd(final CDD... cdds) {
		add(mCDDs, cdds);
		return this;
	}

	public PatternBuilder addDuration(final String... durations) {
		if (durations != null && durations.length > 0) {
			for (int i = 0; i < durations.length; ++i) {
				final String duration = durations[i];
				String name;
				Rational rational;
				try {
					rational = SmtUtils.toRational(duration);
					name = null;
				} catch (final Exception ex) {
					rational = null;
					name = duration;
				}
				mDurations.add(rational);
				mDurationNames.add(name);
			}
		}
		return this;
	}

	public PatternBuilder setId(final String id) {
		mId = id;
		return this;
	}

	public PatternBuilder setType(final Class<? extends PatternType<?>> clazz) {
		mClazz = clazz;
		return this;
	}

	public PatternBuilder setScope(final SrParseScope<?> scope) {
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

	public PatternType<?> build(final Durations durations) {
		if (mClazz == null) {
			throw new IllegalStateException("Type of pattern not yet specified");
		}
		if (mId == null) {
			throw new IllegalStateException("Id of pattern not yet specified");
		}
		if (mScope == null) {
			throw new IllegalStateException("Scope of pattern not yet specified");
		}
		final PatternTypeConstructor constr = getConstructor(mClazz);
		if (mDurationNames.stream().allMatch(Objects::isNull)) {
			return constr.construct(mScope, mId, mCDDs, mDurations, Collections.emptyList());
		}

		for (int i = 0; i < mDurations.size(); ++i) {
			final Rational dur = mDurations.get(i);
			if (dur == null) {
				final String name = mDurationNames.get(i);
				final Rational propagatedConst = durations.getConstantValue(name);
				if (propagatedConst == null) {
					return null;
				}
				mDurations.set(i, propagatedConst);
			}
		}
		return constr.construct(mScope, mId, mCDDs, mDurations, mDurationNames);
	}

	public static PatternTypeConstructor getConstructor(final Class<? extends PatternType<?>> clazz) {
		final PatternTypeConstructor constr = CONSTRUCTORS.get(clazz);
		if (constr == null) {
			throw new UnsupportedOperationException("Unknown pattern type " + clazz);
		}
		return constr;
	}

	public static PatternType<?> normalize(final PatternType<?> p, final Durations durations) {
		if (p instanceof DeclarationPattern) {
			return p;
		}
		final PatternBuilder pb = new PatternBuilder();
		pb.mId = p.getId();
		pb.mScope = p.getScope();
		pb.mClazz = (Class<? extends PatternType<?>>) p.getClass();
		pb.mDurationNames.addAll(p.getDurationNames());
		pb.mCDDs.addAll(p.getCdds());
		final Rational durationScale = durations.computeScalingFactor();
		for (final Rational d : p.getDurations()) {
			pb.mDurations.add(d.mul(durationScale));
		}
		return pb.build(durations);
	}

	@FunctionalInterface
	public interface PatternTypeConstructor {
		PatternType<?> construct(final SrParseScope<?> scope, final String id, final List<CDD> cdds,
				final List<Rational> durations, final List<String> durationNames);
	}

}
