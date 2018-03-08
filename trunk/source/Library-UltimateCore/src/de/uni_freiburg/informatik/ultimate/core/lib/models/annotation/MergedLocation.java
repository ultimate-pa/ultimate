/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A default implementation of the {@link ILocation} interface. Does not support the deprecated parts of
 * {@link ILocation}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class MergedLocation extends DefaultLocation {

	private static final String MSG_UNKNOWN = "UNKNOWN";
	private static final long serialVersionUID = 1L;
	private final List<ILocation> mOriginLocations;

	/**
	 * Create a {@link MergedLocation} with meaningful values.
	 *
	 * @param fileName
	 * @param startLine
	 * @param endLine
	 * @param startColum
	 * @param endColumn
	 */
	private MergedLocation(final String fileName, final int startLine, final int endLine, final int startColum,
			final int endColumn, final List<ILocation> origins) {
		super(fileName, startLine, endLine, startColum, endColumn);
		mOriginLocations = Objects.requireNonNull(origins);
	}

	@Visualizable
	public List<ILocation> getOriginLocations() {
		return Collections.unmodifiableList(mOriginLocations);
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other instanceof MergedLocation) {
			final MergedLocation otherMergedLoc = (MergedLocation) other;
			final List<ILocation> mergedOrigins = new ArrayList<>();
			mergedOrigins.addAll(getOriginLocations());
			mergedOrigins.addAll(otherMergedLoc.getOriginLocations());
			return mergeNonMergeLocation(this, otherMergedLoc, mergedOrigins);
		}
		if (other instanceof ILocation) {
			return mergeToMergeLocation(this, (ILocation) other);
		}
		return super.merge(other);
	}

	private static ILocation mergeNonMergeLocation(final ILocation loc, final ILocation otherLoc,
			final List<ILocation> origins) {
		final String fileName;
		final int startLine;
		final int endLine;
		final int startColum;
		final int endColumn;
		if (Objects.equals(loc.getFileName(), otherLoc.getFileName())) {
			fileName = loc.getFileName();
			final Pair<Integer, Integer> newLines =
					mergeInterval(loc.getStartLine(), loc.getEndLine(), otherLoc.getStartLine(), otherLoc.getEndLine());
			final Pair<Integer, Integer> newColumns = mergeInterval(loc.getStartColumn(), loc.getEndColumn(),
					otherLoc.getStartColumn(), otherLoc.getEndColumn());
			startLine = newLines.getFirst();
			endLine = newLines.getSecond();
			startColum = newColumns.getFirst();
			endColumn = newColumns.getSecond();
		} else {
			fileName = MSG_UNKNOWN;
			startLine = -1;
			endLine = -1;
			startColum = -1;
			endColumn = -1;
		}
		return new MergedLocation(fileName, startLine, endLine, startColum, endColumn, origins);
	}

	public static Pair<Integer, Integer> mergeInterval(final int aLower, final int aUpper, final int bLower,
			final int bUpper) {
		int newFirst;
		if (aLower < 0 || bLower < 0) {
			newFirst = -1;
		} else if (aLower <= bLower) {
			newFirst = aLower;
		} else {
			newFirst = bLower;
		}

		int newSecond;
		if (aUpper < 0 || bUpper < 0) {
			newSecond = -1;
		} else if (aUpper <= bUpper) {
			newSecond = bUpper;
		} else {
			newSecond = aUpper;
		}
		return new Pair<>(newFirst, newSecond);
	}

	public static ILocation mergeToMergeLocation(final ILocation one, final ILocation other) {
		if (one == null) {
			return other;
		}
		if (other == null) {
			return one;
		}
		if (one instanceof MergedLocation && other instanceof MergedLocation) {
			return (ILocation) one.merge(other);
		}
		final List<ILocation> origins = new ArrayList<>(2);
		origins.add(one);
		origins.add(other);
		return mergeNonMergeLocation(one, other, origins);
	}

	@Override
	public String toString() {
		return "Merged: " + getOriginLocations().stream().map(a -> a.toString()).collect(Collectors.joining(", "));
	}
}
