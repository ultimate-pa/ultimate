/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import java.util.Collections;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public final class DataRaceAnnotation extends ModernAnnotations {
	private static final long serialVersionUID = 1L;

	private static final String KEY = DataRaceAnnotation.class.getName();

	private final Set<Race> mRaces;

	private DataRaceAnnotation(final Race race) {
		this(Set.of(race));
	}

	private DataRaceAnnotation(final Set<Race> races) {
		mRaces = races;
	}

	public Set<Race> getRaces() {
		return Collections.unmodifiableSet(mRaces);
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other == null || other == this) {
			return this;
		}
		if (other instanceof DataRaceAnnotation) {
			return new DataRaceAnnotation(DataStructureUtils.union(mRaces, ((DataRaceAnnotation) other).mRaces));
		}
		return super.merge(other);
	}

	public static Race annotateAccess(final IElement node, final String accessPath, final ILocation loc,
			final boolean isWrite) {
		final Race race = new Race(isWrite, accessPath, null, loc);
		node.getPayload().getAnnotations().put(KEY, new DataRaceAnnotation(race));
		return race;
	}

	public static void annotateCheck(final IElement node, final Race[] twinAccesses, final ILocation loc) {
		final boolean isWrite = twinAccesses[0].isWrite();
		final String variable = twinAccesses[0].mAccessPath;
		node.getPayload().getAnnotations().put(KEY,
				new DataRaceAnnotation(new Race(isWrite, variable, twinAccesses, loc)));
	}

	public static DataRaceAnnotation getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, KEY, DataRaceAnnotation.class::cast);
	}

	public static final class Race {
		private final boolean mIsWrite;
		private final String mAccessPath;
		private final Set<Race> mTwinAccesses;
		private final ILocation mOriginalLocation;

		private Race(final boolean isWrite, final String accessPath, final Race[] twinAccesses,
				final ILocation location) {
			mIsWrite = isWrite;
			mAccessPath = accessPath;
			mTwinAccesses = twinAccesses == null ? null : Set.of(twinAccesses);
			mOriginalLocation = location;
		}

		public boolean isTwin(final Race other) {
			if (isCheck()) {
				return mTwinAccesses.contains(other);
			}
			if (other.isCheck()) {
				return other.mTwinAccesses.contains(this);
			}
			return false;
		}

		public Optional<Boolean> isConflictingAccess(final Race other) {
			if (!isCheck()) {
				throw new UnsupportedOperationException("Conflicting accesses can only be found for data race checks");
			}
			if ((!isWrite() && !other.isWrite()) || mTwinAccesses.contains(other)) {
				// accesses do not conflict because both are reads, or they are twins
				return Optional.of(false);
			}
			if (other.isCheck()) {
				return Optional.of(false);
			}
			if (isUndeterminedRace() || other.isUndeterminedRace()) {
				return Optional.empty();
			}
			return Optional.of(mAccessPath.startsWith(other.mAccessPath) || other.mAccessPath.startsWith(mAccessPath));
		}

		public String getVariable() {
			if (mAccessPath == null) {
				throw new IllegalStateException("heap race has no variable");
			}
			return mAccessPath;
		}

		public boolean isWrite() {
			return mIsWrite;
		}

		public boolean isCheck() {
			return mTwinAccesses != null;
		}

		public boolean isUndeterminedRace() {
			return mAccessPath == null;
		}

		public ILocation getOriginalLocation() {
			return mOriginalLocation;
		}
	}
}
